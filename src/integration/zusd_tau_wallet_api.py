"""Tau-node-backed zUSD wallet transport API.

This module exposes a narrow read/prepare HTTP surface for the zUSD TauToken
transport lane. It talks to a Tau node and returns unsigned stream-9 operation
bundles; transaction signing and submission remain outside the production API.
"""

from __future__ import annotations

import json
import os
import time
from dataclasses import dataclass
from typing import Any, Dict, Mapping, Optional, Tuple, cast
from urllib.parse import urlsplit

from ..core.dex import DexState
from ..core.generic_token_authority import (
    GenericTokenAuthorityState,
    GenericTokenSupplyAction,
    GenericTokenSupplyCommand,
    apply_generic_token_supply_command,
)
from ..core.zusd import E8
from ..state.canonical import canonical_hex_fixed_allow_0x
from .dex_snapshot import state_from_snapshot
from .generic_token_accounting import generic_token_accounting_error
from .generic_token_authority_bridge import generic_token_authority_from_obj
from .raw_signing_boundary import reject_raw_signing_material
from .tau_net_rpc import TauNetRpcError, TauNetTcpClient, TauNetTcpConfig
from .zusd_generic_token_admission_bridge import (
    evaluate_live_generic_token_writer_admission,
    generic_token_admission_reject_code,
)
from .zusd_monetary_bridge import (
    ZUSDMonetaryState,
    zusd_global_ledger_consistency_error,
    zusd_monetary_config_from_policy_binding,
    zusd_monetary_state_from_obj,
)
from .zusd_tau_token import (
    ZUSDTauTokenConfig,
    derive_zusd_tau_asset_id,
    prepare_zusd_tau_token_operation,
    token_sender_nonce_key,
)

MAX_POST_BODY = 65_536
ResponseT = Tuple[int, Dict[str, Any]]
_APP_STATE_SCHEMA_V2 = "zenodex/tau_app_state/v2"
_APP_STATE_VERSION_V2 = 2


@dataclass(frozen=True, slots=True)
class _CommittedTokenState:
    dex_state: DexState
    monetary_state: ZUSDMonetaryState
    generic_authority: GenericTokenAuthorityState


def _env_str(name: str, default: str) -> str:
    raw = os.environ.get(name)
    if raw is None:
        return default
    value = raw.strip()
    return value if value else default


def _env_bool(name: str, default: bool = False) -> bool:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return bool(default)
    return raw.strip().lower() in {"1", "true", "yes", "on"}


def _env_float(name: str, default: float, *, lo: float, hi: float) -> float:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return float(default)
    try:
        value = float(raw.strip())
    except Exception:
        return float(default)
    if value < lo:
        return float(lo)
    if value > hi:
        return float(hi)
    return float(value)


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        value = int(raw.strip())
    except Exception:
        return int(default)
    if value < lo:
        return int(lo)
    if value > hi:
        return int(hi)
    return int(value)


def _tau_client() -> TauNetTcpClient:
    return TauNetTcpClient(
        TauNetTcpConfig(
            host=_env_str("ZUSD_TAU_WALLET_TAU_HOST", "127.0.0.1"),
            port=_env_int("ZUSD_TAU_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
            timeout_s=_env_float("ZUSD_TAU_WALLET_TAU_TIMEOUT_S", 3.0, lo=0.1, hi=60.0),
        )
    )


def _tau_chain_id() -> str:
    return _env_str("ZUSD_TAU_WALLET_CHAIN_ID", _env_str("TAU_DEX_CHAIN_ID", "tau-local"))


def _canonical_zusd_asset_id(*, chain_id: str) -> str:
    configured = _env_str("TAU_DEX_ZUSD_ASSET_ID", "")
    if configured:
        return canonical_hex_fixed_allow_0x(
            configured,
            nbytes=32,
            name="TAU_DEX_ZUSD_ASSET_ID",
        )
    return derive_zusd_tau_asset_id(chain_id=chain_id)


def _tau_verify_config() -> ZUSDTauTokenConfig:
    tau_bin = _env_str("ZUSD_TAU_WALLET_TAU_BIN", "")
    return ZUSDTauTokenConfig(
        enabled=_env_bool("ZUSD_TAU_WALLET_TAU_VERIFY", False),
        timeout_s=_env_float("ZUSD_TAU_WALLET_TAU_VERIFY_TIMEOUT_S", 2.0, lo=0.1, hi=120.0),
        tau_bin=(tau_bin or None),
        allow_path_lookup=_env_bool("ZUSD_TAU_WALLET_TAU_ALLOW_PATH_LOOKUP", False),
    )


def _default_deadline() -> int:
    delta = _env_int("ZUSD_TAU_WALLET_DEFAULT_DEADLINE_S", 3600, lo=1, hi=86_400)
    return int(time.time()) + int(delta)


def _canonical_pubkey(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _pubkey_for_rpc(value: str) -> str:
    s = value.strip().lower()
    return s[2:] if s.startswith("0x") else s


def _parse_json_body(body: Optional[bytes]) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    if body is None or len(body) == 0:
        return None, "empty_body"
    if len(body) > MAX_POST_BODY:
        return None, "body_too_large"
    try:
        obj = json.loads(body)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None, "invalid_json"
    if not isinstance(obj, dict):
        return None, "expected_object"
    return obj, None


def _load_app_state(client: TauNetTcpClient) -> Tuple[Dict[str, Any], Optional[str]]:
    raw = client.getappstate(full=True).strip()
    if not raw:
        raise TauNetRpcError("empty getappstate response")
    obj = json.loads(raw)
    if not isinstance(obj, dict):
        raise TauNetRpcError("invalid getappstate response")
    app_state = obj.get("app_state")
    if app_state is None:
        app_state = {}
    if not isinstance(app_state, dict):
        raise TauNetRpcError("invalid app_state payload")
    app_hash = obj.get("app_hash")
    return app_state, str(app_hash) if isinstance(app_hash, str) and app_hash else None


def _committed_token_state(
    app_state: Mapping[str, Any],
) -> _CommittedTokenState:
    if app_state.get("schema") != _APP_STATE_SCHEMA_V2:
        raise TauNetRpcError("authoritative app state must use schema v2")
    if app_state.get("version") != _APP_STATE_VERSION_V2:
        raise TauNetRpcError("authoritative app state must use version 2")
    dex_obj = app_state.get("dex_state")
    if not isinstance(dex_obj, Mapping):
        raise TauNetRpcError("app_state.dex_state must be an object")
    dex_state = state_from_snapshot(dex_obj)
    raw = app_state.get("zusd_monetary")
    if raw is None:
        raise TauNetRpcError("zUSD monetary policy is absent from authoritative app state")
    if not isinstance(raw, Mapping):
        raise TauNetRpcError("app_state.zusd_monetary must be an object")
    monetary_state = zusd_monetary_state_from_obj(raw)
    generic_authority = generic_token_authority_from_obj(
        app_state.get("generic_token_authority")
    )
    config = zusd_monetary_config_from_policy_binding(
        monetary_state.policy_binding
    )
    zusd_error = zusd_global_ledger_consistency_error(
        config=config,
        state=dex_state,
        monetary_state=monetary_state,
    )
    if zusd_error is not None:
        raise TauNetRpcError(f"global zUSD accounting mismatch: {zusd_error}")
    generic_error = generic_token_accounting_error(
        authority_state=generic_authority,
        dex_state=dex_state,
        monetary_state=monetary_state,
        canonical_zusd_asset=monetary_state.policy_binding.canonical_zusd_asset,
    )
    if generic_error is not None:
        raise TauNetRpcError(
            f"global generic-token accounting mismatch: {generic_error}"
        )
    return _CommittedTokenState(
        dex_state=dex_state,
        monetary_state=monetary_state,
        generic_authority=generic_authority,
    )


def _balances_for_asset(
    committed_state: _CommittedTokenState,
    *,
    asset_id: str,
) -> Dict[str, int]:
    return dict(
        committed_state.dex_state.balances.get_balances_for_asset(asset_id)
    )


def _last_used_token_nonce(
    committed_state: _CommittedTokenState,
    *,
    actor_pubkey: str,
) -> int:
    token_key = token_sender_nonce_key(actor_pubkey)
    return int(committed_state.dex_state.nonces.get_last(token_key))


def _transport_context(
    *,
    client: TauNetTcpClient,
    committed_state: _CommittedTokenState,
    app_hash: Optional[str],
    action: str,
    sender_pubkey: Optional[str],
    recipient_pubkey: Optional[str],
    operator_pubkey: Optional[str],
    asset_id: str,
) -> Dict[str, Any]:
    balances = _balances_for_asset(committed_state, asset_id=asset_id)
    monetary_state = committed_state.monetary_state
    if asset_id == monetary_state.policy_binding.canonical_zusd_asset:
        debt_e8 = int(monetary_state.core.debt_e8)
        if debt_e8 % E8 != 0:
            raise TauNetRpcError("canonical zUSD debt must be whole-token aligned")
        total_supply_before = debt_e8 // E8
    else:
        registered_asset = committed_state.generic_authority.get_asset(asset_id)
        if registered_asset is None:
            raise TauNetRpcError("asset is not registered in committed token authority")
        total_supply_before = registered_asset.total_supply_units

    actor_pubkey: Optional[str]
    if action == "mint":
        actor_pubkey = operator_pubkey
    else:
        actor_pubkey = sender_pubkey
    if actor_pubkey is None:
        raise ValueError("missing actor pubkey")
    last_used_nonce = _last_used_token_nonce(
        committed_state,
        actor_pubkey=actor_pubkey,
    )
    tx_sequence_number = int(client.get_sequence(_pubkey_for_rpc(actor_pubkey)))

    sender_balance_before = int(balances.get((sender_pubkey or "").strip().lower(), 0))
    recipient_balance_before = int(balances.get((recipient_pubkey or "").strip().lower(), 0))

    return {
        "app_hash": app_hash,
        "asset_id": asset_id,
        "actor_pubkey": actor_pubkey,
        "sender_balance_before": sender_balance_before,
        "recipient_balance_before": recipient_balance_before,
        "total_supply_before": total_supply_before,
        "last_used_nonce": last_used_nonce,
        "tx_sequence_number": tx_sequence_number,
    }


def _request_action(body: Mapping[str, Any]) -> str:
    action = body.get("action")
    if type(action) is not str:
        raise ValueError("unsupported_action")
    if action not in {"transfer", "mint", "burn"}:
        raise ValueError("unsupported_action")
    return action


def _assert_exact_request_fields(
    body: Mapping[str, Any],
    *,
    action: str,
    endpoint: str,
) -> None:
    if action == "transfer":
        action_fields = frozenset(("sender_pubkey", "recipient_pubkey"))
    elif action == "mint":
        action_fields = frozenset(("operator_pubkey", "recipient_pubkey"))
    else:
        action_fields = frozenset(("sender_pubkey",))

    common_fields = frozenset(("action", "chain_id", "asset_id"))
    if endpoint == "inspect":
        endpoint_fields: frozenset[str] = frozenset()
    elif endpoint == "prepare":
        endpoint_fields = frozenset(("amount", "deadline"))
    else:
        raise ValueError("unsupported_wallet_endpoint")

    allowed_fields = common_fields | action_fields | endpoint_fields
    if set(body) - allowed_fields:
        raise ValueError("unexpected_request_fields")


def _request_chain_id(
    body: Mapping[str, Any],
    *,
    committed_chain_id: str,
) -> str:
    if "chain_id" not in body:
        return committed_chain_id
    requested_chain_id = body.get("chain_id")
    if type(requested_chain_id) is not str or not requested_chain_id:
        raise ValueError("bad_chain_id")
    if requested_chain_id != committed_chain_id:
        raise ValueError("chain_id does not match committed zUSD policy")
    return committed_chain_id


def _request_asset_id(
    body: Mapping[str, Any],
    *,
    default_asset_id: str,
) -> str:
    if "asset_id" not in body:
        return default_asset_id
    explicit_asset_id = body.get("asset_id")
    if (
        type(explicit_asset_id) is not str
        or not explicit_asset_id
        or explicit_asset_id != explicit_asset_id.strip()
    ):
        raise ValueError("bad_asset_id")
    return canonical_hex_fixed_allow_0x(
        explicit_asset_id,
        nbytes=32,
        name="asset_id",
    )


def _assert_committed_generic_authority_allows(
    committed_state: _CommittedTokenState,
    *,
    action: str,
    asset_id: str,
    amount: int,
    sender_pubkey: str | None,
    recipient_pubkey: str | None,
    operator_pubkey: str | None,
) -> None:
    if asset_id == committed_state.monetary_state.policy_binding.canonical_zusd_asset:
        return
    actor_pubkey = operator_pubkey if action == "mint" else sender_pubkey
    if actor_pubkey is None:
        raise ValueError("missing actor pubkey")
    decision = apply_generic_token_supply_command(
        committed_state.generic_authority,
        GenericTokenSupplyCommand(
            action=GenericTokenSupplyAction(action),
            asset_id=asset_id,
            actor_pubkey=actor_pubkey,
            amount_units=amount,
            recipient_pubkey=recipient_pubkey,
        ),
    )
    if decision.accepted:
        return
    reject_code = (
        "unknown" if decision.reject_code is None else decision.reject_code.value
    )
    raise ValueError(f"generic token authority rejected: {reject_code}")


def _request_int(body: Mapping[str, Any], *, name: str, default: Optional[int] = None) -> int:
    if name not in body:
        if default is None:
            raise ValueError(f"missing_{name}")
        return int(default)
    value = body.get(name)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"bad_{name}")
    return int(value)


def _build_prepare_response(body: Mapping[str, Any]) -> Dict[str, Any]:
    action = _request_action(body)
    _assert_exact_request_fields(
        body,
        action=action,
        endpoint="prepare",
    )
    amount = _request_int(body, name="amount", default=None)
    deadline = _request_int(body, name="deadline", default=_default_deadline())
    sender_pubkey = None
    recipient_pubkey = None
    operator_pubkey = None
    if "sender_pubkey" in body:
        sender_pubkey = _canonical_pubkey(body.get("sender_pubkey"), name="sender_pubkey")
    if "recipient_pubkey" in body:
        recipient_pubkey = _canonical_pubkey(body.get("recipient_pubkey"), name="recipient_pubkey")
    if "operator_pubkey" in body:
        operator_pubkey = _canonical_pubkey(body.get("operator_pubkey"), name="operator_pubkey")

    if action in {"transfer", "burn"} and sender_pubkey is None:
        raise ValueError("missing_sender_pubkey")
    if action in {"transfer", "mint"} and recipient_pubkey is None:
        raise ValueError("missing_recipient_pubkey")
    if action == "mint" and operator_pubkey is None:
        raise ValueError("missing_operator_pubkey")

    client = _tau_client()
    app_state, app_hash = _load_app_state(client)
    committed_state = _committed_token_state(app_state)
    committed_policy = committed_state.monetary_state.policy_binding
    chain_id = _request_chain_id(
        body,
        committed_chain_id=committed_policy.chain_id,
    )
    canonical_zusd_asset = committed_policy.canonical_zusd_asset
    asset_id = _request_asset_id(
        body,
        default_asset_id=canonical_zusd_asset,
    )
    admission = evaluate_live_generic_token_writer_admission(
        chain_id=chain_id,
        canonical_zusd_asset=canonical_zusd_asset,
        action=action,
        asset=asset_id,
        recipient_pubkey=recipient_pubkey,
    )
    reject_code = generic_token_admission_reject_code(admission)
    if reject_code is not None:
        raise ValueError(f"generic zUSD token operation rejected: {reject_code}")
    _assert_committed_generic_authority_allows(
        committed_state,
        action=action,
        asset_id=asset_id,
        amount=amount,
        sender_pubkey=sender_pubkey,
        recipient_pubkey=recipient_pubkey,
        operator_pubkey=operator_pubkey,
    )
    context = _transport_context(
        client=client,
        committed_state=committed_state,
        app_hash=app_hash,
        action=action,
        sender_pubkey=sender_pubkey,
        recipient_pubkey=recipient_pubkey,
        operator_pubkey=operator_pubkey,
        asset_id=asset_id,
    )

    report = prepare_zusd_tau_token_operation(
        action=cast(Any, action),
        amount=amount,
        deadline=deadline,
        last_used_nonce=int(context["last_used_nonce"]),
        total_supply_before=int(context["total_supply_before"]),
        sender_balance_before=int(context["sender_balance_before"]),
        recipient_balance_before=int(context["recipient_balance_before"]),
        sender_pubkey=sender_pubkey,
        recipient_pubkey=recipient_pubkey,
        operator_pubkey=operator_pubkey,
        asset_id=asset_id,
        chain_id=chain_id,
        tau_config=_tau_verify_config(),
    )

    payload = {
        "ok": True,
        "transport": {
            "chain_id": chain_id,
            "app_hash": context["app_hash"],
            "asset_id": asset_id,
            "actor_pubkey": context["actor_pubkey"],
            "sender_balance_before": int(context["sender_balance_before"]),
            "recipient_balance_before": int(context["recipient_balance_before"]),
            "total_supply_before": int(context["total_supply_before"]),
            "last_used_nonce": int(context["last_used_nonce"]),
            "tx_sequence_number": int(context["tx_sequence_number"]),
            "tau_host": _env_str("ZUSD_TAU_WALLET_TAU_HOST", "127.0.0.1"),
            "tau_port": _env_int("ZUSD_TAU_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
        },
        "report": {
            "action": report.action,
            "asset_id": report.asset_id,
            "nonce_key": report.nonce_key,
            "nonce_before": int(report.nonce_before),
            "nonce_after": int(report.nonce_after),
            "operation": dict(report.operation),
            "operations": dict(report.operations),
            "sender_balance_after": int(report.sender_balance_after),
            "recipient_balance_after": int(report.recipient_balance_after),
            "supply_after": int(report.supply_after),
            "tau_receipts": [
                {
                    "spec_id": receipt.spec_id,
                    "gate_output": receipt.gate_output,
                    "steps": [dict(step) for step in receipt.steps],
                    "expected_ok": bool(receipt.expected_ok),
                }
                for receipt in report.tau_receipts
            ],
            "tau_tx_payload": report.tau_tx_payload,
        },
    }
    return payload


def _status_payload() -> Dict[str, Any]:
    configured_chain_id = _tau_chain_id()
    configured_asset_id = _canonical_zusd_asset_id(chain_id=configured_chain_id)
    chain_id = configured_chain_id
    asset_id = configured_asset_id
    status: Dict[str, Any] = {
        "enabled": True,
        "chain_id": chain_id,
        "asset_id": asset_id,
        "tau_host": _env_str("ZUSD_TAU_WALLET_TAU_HOST", "127.0.0.1"),
        "tau_port": _env_int("ZUSD_TAU_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
    }
    try:
        client = _tau_client()
        hello = client.rpc("hello version=1").strip()
        app_state, app_hash = _load_app_state(client)
        committed_state = _committed_token_state(app_state)
        committed_policy = committed_state.monetary_state.policy_binding
        chain_id = committed_policy.chain_id
        asset_id = committed_policy.canonical_zusd_asset
        status.update(
            {
                "configured_chain_id": configured_chain_id,
                "configured_asset_id": configured_asset_id,
                "chain_id": chain_id,
                "asset_id": asset_id,
                "policy_binding_ok": (
                    configured_chain_id == chain_id and configured_asset_id == asset_id
                ),
                "generic_mint_authorities": [
                    {
                        "asset_id": asset.asset_id,
                        "mint_authority_pubkey": asset.mint_authority_pubkey,
                    }
                    for asset in committed_state.generic_authority.assets
                ],
            }
        )
        status["node_reachable"] = True
        status["hello"] = hello
        status["app_hash"] = app_hash
        status["app_bridge_available"] = bool(app_state or app_hash)
        status["holder_count"] = len(
            _balances_for_asset(committed_state, asset_id=asset_id)
        )
    except Exception as exc:
        status["node_reachable"] = False
        status["error"] = f"{type(exc).__name__}: {exc}"
    return status


def handle_zusd_tau_wallet_request(method: str, path: str, body: Optional[bytes]) -> ResponseT:
    parsed_path = urlsplit(path)
    segments = [segment for segment in parsed_path.path.split("/") if segment]
    if (
        len(segments) < 4
        or segments[0] != "api"
        or segments[1] != "zusd"
        or segments[2] != "wallet"
    ):
        return 404, {"ok": False, "error": "not_found"}

    rest = segments[3:]
    try:
        if method == "GET" and rest == ["status"]:
            return 200, {"ok": True, "status": _status_payload()}
        if method != "POST":
            return 405, {"ok": False, "error": "method_not_allowed"}
        parsed, err = _parse_json_body(body)
        if err is not None:
            return 400, {"ok": False, "error": err}
        if parsed is None:
            return 400, {"ok": False, "error": "bad_json"}
        reject_raw_signing_material(parsed)
        if rest == ["inspect"]:
            action = _request_action(parsed)
            _assert_exact_request_fields(
                parsed,
                action=action,
                endpoint="inspect",
            )
            sender_pubkey = (
                _canonical_pubkey(parsed.get("sender_pubkey"), name="sender_pubkey")
                if "sender_pubkey" in parsed
                else None
            )
            recipient_pubkey = (
                _canonical_pubkey(parsed.get("recipient_pubkey"), name="recipient_pubkey")
                if "recipient_pubkey" in parsed
                else None
            )
            operator_pubkey = (
                _canonical_pubkey(parsed.get("operator_pubkey"), name="operator_pubkey")
                if "operator_pubkey" in parsed
                else None
            )
            client = _tau_client()
            app_state, app_hash = _load_app_state(client)
            committed_state = _committed_token_state(app_state)
            committed_policy = committed_state.monetary_state.policy_binding
            chain_id = _request_chain_id(
                parsed,
                committed_chain_id=committed_policy.chain_id,
            )
            asset_id = _request_asset_id(
                parsed,
                default_asset_id=committed_policy.canonical_zusd_asset,
            )
            context = _transport_context(
                client=client,
                committed_state=committed_state,
                app_hash=app_hash,
                action=action,
                sender_pubkey=sender_pubkey,
                recipient_pubkey=recipient_pubkey,
                operator_pubkey=operator_pubkey,
                asset_id=asset_id,
            )
            return 200, {"ok": True, "transport": context, "chain_id": chain_id}
        if rest == ["prepare"]:
            return 200, _build_prepare_response(parsed)
        return 404, {"ok": False, "error": "not_found"}
    except (ValueError, TypeError) as exc:
        return 400, {"ok": False, "error": str(exc)}
    except TauNetRpcError as exc:
        return 502, {"ok": False, "error": "tau_rpc_error", "detail": str(exc)}
    except Exception as exc:
        return 500, {
            "ok": False,
            "error": "internal_error",
            "detail": f"{type(exc).__name__}: {exc}",
        }
