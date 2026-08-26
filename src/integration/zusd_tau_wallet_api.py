"""Tau-node-backed zUSD wallet transport API.

This module exposes a narrow HTTP surface for the zUSD TauToken transport lane.
It is separate from ``zusd_api.py`` because the latter is a local demo state
machine, while this module talks to a Tau testnet node and prepares or submits
stream-9 TauToken operations.
"""

from __future__ import annotations

import json
import os
import re
import time
from dataclasses import dataclass
from typing import Any, Dict, Mapping, Optional, Tuple, cast
from urllib.parse import urlsplit

from ..state.canonical import canonical_hex_fixed_allow_0x
from .tau_net_client import (
    TauNetRpcError,
    TauNetTcpClient,
    TauNetTcpConfig,
    encode_tau_operations_for_wire,
    tau_rpc_response_is_success,
    verify_tau_transaction_payload_signature,
)
from .zusd_tau_token import (
    ZUSDTauTokenConfig,
    derive_zusd_tau_asset_id,
    prepare_zusd_tau_token_operation,
    token_sender_nonce_key,
)

MAX_POST_BODY = 65_536
MAX_TAU_APP_STATE_BYTES = 1_048_576
MAX_TAU_APP_STATE_JSON_DEPTH = 64
ResponseT = Tuple[int, Dict[str, Any]]

_INSPECT_REQUEST_FIELDS = frozenset(
    {
        "action",
        "asset_id",
        "chain_id",
        "operator_pubkey",
        "recipient_pubkey",
        "sender_pubkey",
    }
)
_PREPARE_REQUEST_FIELDS = _INSPECT_REQUEST_FIELDS | {
    "amount",
    "deadline",
    "signed_tau_tx_payload",
    "signer_privkey",
    "tau_tx_payload",
    "tx_fee_limit",
}
_SUBMIT_REQUEST_FIELDS = _PREPARE_REQUEST_FIELDS


class _DuplicateJsonFieldError(ValueError):
    pass


def _reject_duplicate_json_fields(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise _DuplicateJsonFieldError(key)
        result[key] = value
    return result


def _load_json_without_duplicate_fields(raw: bytes | str) -> object:
    return json.loads(raw, object_pairs_hook=_reject_duplicate_json_fields)


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


def _allow_signing() -> bool:
    return _env_bool("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", False)


def _auto_mine() -> bool:
    return _env_bool("ZUSD_TAU_WALLET_AUTO_MINE", False)


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
        obj = _load_json_without_duplicate_fields(body)
    except _DuplicateJsonFieldError:
        return None, "duplicate_json_field"
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None, "invalid_json"
    if not isinstance(obj, dict):
        return None, "expected_object"
    return obj, None


def _require_bounded_json_text(raw: str, *, max_bytes: int, max_depth: int) -> None:
    if len(raw.encode("utf-8")) > max_bytes:
        raise TauNetRpcError("getappstate response too large")
    depth = 0
    in_string = False
    escaped = False
    for char in raw:
        if in_string:
            if escaped:
                escaped = False
                continue
            if char == "\\":
                escaped = True
                continue
            if char == '"':
                in_string = False
            continue
        if char == '"':
            in_string = True
        elif char in "[{":
            depth += 1
            if depth > max_depth:
                raise TauNetRpcError("getappstate JSON nesting too deep")
        elif char in "]}":
            depth -= 1


def _load_app_state(client: TauNetTcpClient) -> Tuple[Dict[str, Any], Optional[str]]:
    raw = client.getappstate(full=True).strip()
    if not raw:
        raise TauNetRpcError("empty getappstate response")
    _require_bounded_json_text(
        raw,
        max_bytes=MAX_TAU_APP_STATE_BYTES,
        max_depth=MAX_TAU_APP_STATE_JSON_DEPTH,
    )
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


def _dex_state_view(app_state: Mapping[str, Any]) -> Mapping[str, Any]:
    dex_state = app_state.get("dex_state")
    if isinstance(dex_state, Mapping):
        return dex_state
    return app_state


def _balances_for_asset(app_state: Mapping[str, Any], *, asset_id: str) -> Dict[str, int]:
    state_view = _dex_state_view(app_state)
    raw = state_view.get("balances") or []
    if not isinstance(raw, list):
        raise TauNetRpcError("app_state.balances must be a list")
    out: Dict[str, int] = {}
    for index, entry in enumerate(raw):
        if not isinstance(entry, Mapping):
            raise TauNetRpcError(f"app_state.balances[{index}] must be an object")
        pubkey = entry.get("pubkey")
        asset = entry.get("asset")
        amount = entry.get("amount")
        if not isinstance(pubkey, str) or not isinstance(asset, str):
            raise TauNetRpcError(f"app_state.balances[{index}] has invalid keys")
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise TauNetRpcError(f"app_state.balances[{index}] amount invalid")
        if asset.strip().lower() != asset_id.strip().lower():
            continue
        out[pubkey.strip().lower()] = int(amount)
    return out


def _last_used_token_nonce(app_state: Mapping[str, Any], *, actor_pubkey: str) -> int:
    state_view = _dex_state_view(app_state)
    raw = state_view.get("nonces") or []
    if not isinstance(raw, list):
        raise TauNetRpcError("app_state.nonces must be a list")
    token_key = token_sender_nonce_key(actor_pubkey)
    last_nonce = 0
    for index, entry in enumerate(raw):
        if not isinstance(entry, Mapping):
            raise TauNetRpcError(f"app_state.nonces[{index}] must be an object")
        pubkey = entry.get("pubkey")
        if not isinstance(pubkey, str):
            raise TauNetRpcError(f"app_state.nonces[{index}].pubkey invalid")
        if pubkey.strip().lower() != token_key.strip().lower():
            continue
        nonce = entry.get("last_nonce", 0)
        if not isinstance(nonce, int) or isinstance(nonce, bool) or nonce < 0:
            raise TauNetRpcError(f"app_state.nonces[{index}].last_nonce invalid")
        last_nonce = int(nonce)
    return last_nonce


def _transport_context(
    *,
    client: TauNetTcpClient,
    action: str,
    sender_pubkey: Optional[str],
    recipient_pubkey: Optional[str],
    operator_pubkey: Optional[str],
    asset_id: str,
) -> Dict[str, Any]:
    app_state, app_hash = _load_app_state(client)
    balances = _balances_for_asset(app_state, asset_id=asset_id)
    total_supply_before = int(sum(int(v) for v in balances.values()))

    actor_pubkey: Optional[str]
    if action == "mint":
        actor_pubkey = operator_pubkey
    else:
        actor_pubkey = sender_pubkey
    if actor_pubkey is None:
        raise ValueError("missing actor pubkey")
    last_used_nonce = _last_used_token_nonce(app_state, actor_pubkey=actor_pubkey)
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
    action = str(body.get("action", "")).strip().lower()
    if action not in {"transfer", "mint", "burn"}:
        raise ValueError("unsupported_action")
    return action


def _request_int(body: Mapping[str, Any], *, name: str, default: Optional[int] = None) -> int:
    if name not in body:
        if default is None:
            raise ValueError(f"missing_{name}")
        return int(default)
    value = body.get(name)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"bad_{name}")
    return int(value)


def _require_closed_request_fields(
    body: Mapping[str, Any],
    *,
    allowed: frozenset[str],
) -> None:
    if any(type(key) is not str for key in body) or not set(body) <= allowed:
        raise ValueError("request_fields_mismatch")


def _bound_chain_and_asset(body: Mapping[str, Any]) -> tuple[str, str]:
    chain_id = _tau_chain_id()
    if "chain_id" in body:
        requested_chain_id = body.get("chain_id")
        if type(requested_chain_id) is not str or requested_chain_id != chain_id:
            raise ValueError("chain_id mismatch")

    asset_id = derive_zusd_tau_asset_id(chain_id=chain_id)
    if "asset_id" in body:
        explicit_asset_id = body.get("asset_id")
        if type(explicit_asset_id) is not str:
            raise ValueError("asset_id mismatch")
        try:
            requested_asset_id = canonical_hex_fixed_allow_0x(
                explicit_asset_id,
                nbytes=32,
                name="asset_id",
            )
        except (TypeError, ValueError) as exc:
            raise ValueError("asset_id mismatch") from exc
        if requested_asset_id != asset_id:
            raise ValueError("asset_id mismatch")
    return chain_id, asset_id


@dataclass(frozen=True, slots=True)
class _UnverifiedTauTxPayloadV1:
    sender_pubkey: str
    sequence_number: int
    expiration_time: int
    operation_stream_9: str
    fee_limit: str
    signature: str

    def to_wire(self) -> dict[str, Any]:
        return {
            "sender_pubkey": self.sender_pubkey,
            "sequence_number": self.sequence_number,
            "expiration_time": self.expiration_time,
            "operations": {"9": self.operation_stream_9},
            "fee_limit": self.fee_limit,
            "signature": self.signature,
        }


@dataclass(frozen=True, slots=True)
class _VerifiedExternalTauTxPayloadV1:
    payload: _UnverifiedTauTxPayloadV1


def _decode_unverified_tau_tx_payload(
    selected: object,
) -> _UnverifiedTauTxPayloadV1:
    if type(selected) is not dict:
        raise ValueError("bad_signed_tau_tx_payload")
    raw = cast(dict[str, Any], selected)
    expected_fields = {
        "sender_pubkey",
        "sequence_number",
        "expiration_time",
        "operations",
        "fee_limit",
        "signature",
    }
    if set(raw) != expected_fields or any(type(key) is not str for key in raw):
        raise ValueError("signed_tau_tx_payload fields mismatch")
    if type(raw["sender_pubkey"]) is not str or not raw["sender_pubkey"]:
        raise ValueError("signed_tau_tx_payload bad sender_pubkey")
    if type(raw["sequence_number"]) is not int:
        raise ValueError("signed_tau_tx_payload bad sequence_number")
    if type(raw["expiration_time"]) is not int:
        raise ValueError("signed_tau_tx_payload bad expiration_time")
    operations = raw["operations"]
    if type(operations) is not dict:
        raise ValueError("signed_tau_tx_payload operations must be an object")
    if set(operations) != {"9"} or type(operations["9"]) is not str:
        raise ValueError("signed_tau_tx_payload operations mismatch")
    if type(raw["fee_limit"]) is not str:
        raise ValueError("signed_tau_tx_payload bad fee_limit")
    if type(raw["signature"]) is not str or not raw["signature"]:
        raise ValueError("signed_tau_tx_payload missing signature")
    return _UnverifiedTauTxPayloadV1(
        sender_pubkey=raw["sender_pubkey"],
        sequence_number=raw["sequence_number"],
        expiration_time=raw["expiration_time"],
        operation_stream_9=operations["9"],
        fee_limit=raw["fee_limit"],
        signature=raw["signature"],
    )


def _request_signed_tau_tx_payload(
    body: Mapping[str, Any],
) -> _UnverifiedTauTxPayloadV1 | None:
    present = tuple(
        name for name in ("signed_tau_tx_payload", "tau_tx_payload") if name in body
    )
    if not present:
        return None
    if len(present) != 1:
        raise ValueError("ambiguous_signed_tau_tx_payload")
    selected = body.get(present[0])
    if type(selected) is str:
        try:
            selected = _load_json_without_duplicate_fields(selected)
        except _DuplicateJsonFieldError as exc:
            raise ValueError("signed_tau_tx_payload duplicate field") from exc
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            raise ValueError("bad_signed_tau_tx_payload") from exc
    return _decode_unverified_tau_tx_payload(selected)


def _request_tx_fee_limit(body: Mapping[str, Any]) -> int:
    raw = body.get("tx_fee_limit", 0)
    if type(raw) is int:
        value = raw
    elif type(raw) is str and raw.isdigit():
        value = int(raw, 10)
    else:
        raise ValueError("bad_tx_fee_limit")
    if value < 0 or value > 10**30:
        raise ValueError("bad_tx_fee_limit")
    return value


def _validate_external_tau_tx_payload(
    payload: _UnverifiedTauTxPayloadV1,
    *,
    actor_pubkey: str,
    tx_sequence_number: int,
    deadline: int,
    operations: Mapping[str, Any],
    tx_fee_limit: int,
) -> _VerifiedExternalTauTxPayloadV1:
    if re.fullmatch(r"[0-9a-f]{96}", payload.sender_pubkey) is None:
        raise ValueError("signed_tau_tx_payload sender_pubkey not canonical")
    if re.fullmatch(r"[0-9a-f]{192}", payload.signature) is None:
        raise ValueError("signed_tau_tx_payload signature not canonical")
    if payload.sender_pubkey != _pubkey_for_rpc(actor_pubkey):
        raise ValueError("signed_tau_tx_payload sender mismatch")

    if payload.sequence_number != tx_sequence_number:
        raise ValueError("signed_tau_tx_payload sequence mismatch")
    if payload.expiration_time != deadline:
        raise ValueError("signed_tau_tx_payload expiration mismatch")
    if payload.fee_limit != str(tx_fee_limit):
        raise ValueError("signed_tau_tx_payload fee_limit mismatch")

    expected_operations = encode_tau_operations_for_wire(operations)
    if expected_operations != {"9": payload.operation_stream_9}:
        raise ValueError("signed_tau_tx_payload operations mismatch")

    if not verify_tau_transaction_payload_signature(payload.to_wire()):
        raise ValueError("signed_tau_tx_payload signature invalid")
    return _VerifiedExternalTauTxPayloadV1(payload=payload)


def _build_prepare_response(body: Mapping[str, Any], *, for_submit: bool) -> Dict[str, Any]:
    action = _request_action(body)
    amount = _request_int(body, name="amount", default=None)
    deadline = _request_int(body, name="deadline", default=_default_deadline())
    tx_fee_limit = _request_tx_fee_limit(body)
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

    chain_id, asset_id = _bound_chain_and_asset(body)
    client = _tau_client()
    context = _transport_context(
        client=client,
        action=action,
        sender_pubkey=sender_pubkey,
        recipient_pubkey=recipient_pubkey,
        operator_pubkey=operator_pubkey,
        asset_id=asset_id,
    )

    signer_privkey = body.get("signer_privkey")
    external_payload = _request_signed_tau_tx_payload(body)
    if external_payload is not None and not for_submit:
        raise ValueError("signed_tau_tx_payload_submit_only")
    if external_payload is not None and signer_privkey is not None:
        raise ValueError("ambiguous_signing_authority")
    if for_submit and external_payload is None and type(signer_privkey) not in {str, int}:
        raise ValueError("missing_signer_privkey")
    if signer_privkey is not None and type(signer_privkey) not in {str, int}:
        raise ValueError("bad_signer_privkey")
    if signer_privkey is not None and not _allow_signing():
        raise ValueError("local_signing_disabled")

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
        signer_privkey=signer_privkey if signer_privkey is not None else None,
        tx_sequence_number=int(context["tx_sequence_number"]) if signer_privkey is not None else None,
        tx_expiration_time=deadline if signer_privkey is not None else None,
        tx_fee_limit=tx_fee_limit,
    )

    tau_tx_payload = report.tau_tx_payload
    signing_mode = "local_test_signing" if signer_privkey is not None else "prepare_only"
    if external_payload is not None:
        verified_external_payload = _validate_external_tau_tx_payload(
            external_payload,
            actor_pubkey=str(context["actor_pubkey"]),
            tx_sequence_number=int(context["tx_sequence_number"]),
            deadline=deadline,
            operations=report.operations,
            tx_fee_limit=tx_fee_limit,
        )
        tau_tx_payload = verified_external_payload.payload.to_wire()
        signing_mode = "external_signed_payload"

    payload: Dict[str, Any] = {
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
            "tx_fee_limit": str(tx_fee_limit),
            "signing_mode": signing_mode,
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
            "tau_tx_payload": tau_tx_payload,
        },
    }
    if for_submit:
        if tau_tx_payload is None:
            raise ValueError("missing_signed_tau_tx_payload")
        send_resp = client.sendtx(cast(Mapping[str, Any], tau_tx_payload))
        if not tau_rpc_response_is_success(send_resp):
            raise TauNetRpcError("sendtx rejected")
        payload["submission"] = {
            "outcome": "accepted",
            "sendtx_response": "accepted",
        }
        try:
            if _auto_mine():
                client.createblock()
                payload["submission"]["createblock_response"] = "received"
            app_state_after, app_hash_after = _load_app_state(client)
            payload["post_submit"] = {
                "status": "observed",
                "app_hash": app_hash_after,
                "balances": _balances_for_asset(app_state_after, asset_id=asset_id),
            }
        except Exception:
            # An explicit sendtx success is irreversible local knowledge. Post-send
            # observation is best-effort and no ordinary observation failure may
            # rewrite that known outcome into a pre-send-style error response.
            payload["post_submit"] = {
                "status": "observation_failed",
                "error": "post_submit_observation_failed",
            }
    return payload


def _status_payload() -> Dict[str, Any]:
    chain_id = _tau_chain_id()
    asset_id = derive_zusd_tau_asset_id(chain_id=chain_id)
    token_operator_pubkey = os.environ.get("TAU_DEX_TOKEN_OPERATOR_PUBKEY", "").strip() or None
    status: Dict[str, Any] = {
        "enabled": True,
        "chain_id": chain_id,
        "asset_id": asset_id,
        "tau_host": _env_str("ZUSD_TAU_WALLET_TAU_HOST", "127.0.0.1"),
        "tau_port": _env_int("ZUSD_TAU_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
        "allow_local_signing": _allow_signing(),
        "external_signed_payload_supported": True,
        "preferred_signing_mode": "external_signed_payload",
        "auto_mine": _auto_mine(),
        "token_operator_pubkey": token_operator_pubkey,
    }
    try:
        client = _tau_client()
        hello = client.rpc("hello version=1").strip()
        app_state, app_hash = _load_app_state(client)
        status["node_reachable"] = True
        status["hello"] = hello
        status["app_hash"] = app_hash
        status["app_bridge_available"] = bool(app_state or app_hash)
        status["holder_count"] = len(_balances_for_asset(app_state, asset_id=asset_id))
    except Exception:
        status["node_reachable"] = False
        status["error"] = "tau_status_unavailable"
    return status


def handle_zusd_tau_wallet_request(method: str, path: str, body: Optional[bytes]) -> ResponseT:
    parsed_path = urlsplit(path)
    segments = [segment for segment in parsed_path.path.split("/") if segment]
    if len(segments) < 4 or segments[0] != "api" or segments[1] != "zusd" or segments[2] != "wallet":
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
        if rest == ["inspect"]:
            _require_closed_request_fields(parsed, allowed=_INSPECT_REQUEST_FIELDS)
            action = _request_action(parsed)
            sender_pubkey = _canonical_pubkey(parsed.get("sender_pubkey"), name="sender_pubkey") if "sender_pubkey" in parsed else None
            recipient_pubkey = _canonical_pubkey(parsed.get("recipient_pubkey"), name="recipient_pubkey") if "recipient_pubkey" in parsed else None
            operator_pubkey = _canonical_pubkey(parsed.get("operator_pubkey"), name="operator_pubkey") if "operator_pubkey" in parsed else None
            chain_id, asset_id = _bound_chain_and_asset(parsed)
            context = _transport_context(
                client=_tau_client(),
                action=action,
                sender_pubkey=sender_pubkey,
                recipient_pubkey=recipient_pubkey,
                operator_pubkey=operator_pubkey,
                asset_id=asset_id,
            )
            return 200, {"ok": True, "transport": context, "chain_id": chain_id}
        if rest == ["prepare"]:
            _require_closed_request_fields(parsed, allowed=_PREPARE_REQUEST_FIELDS)
            return 200, _build_prepare_response(parsed, for_submit=False)
        if rest == ["submit"]:
            _require_closed_request_fields(parsed, allowed=_SUBMIT_REQUEST_FIELDS)
            return 200, _build_prepare_response(parsed, for_submit=True)
        return 404, {"ok": False, "error": "not_found"}
    except (ValueError, TypeError) as exc:
        return 400, {"ok": False, "error": str(exc)}
    except TauNetRpcError:
        return 502, {"ok": False, "error": "tau_rpc_error"}
    except Exception:
        return 500, {"ok": False, "error": "internal_error"}
