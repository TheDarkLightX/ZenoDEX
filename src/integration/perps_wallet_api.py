"""Tau-node-backed perps wallet API.

This module exposes a mounted live surface for stream-8 clearinghouse perps
operations. It intentionally sits beside ``perps_api.py`` because that module
is a demo/development API and does not verify caller authority.
"""

from __future__ import annotations

import json
import os
import time
from typing import Any, Dict, Mapping, Optional, Tuple, cast
from urllib.parse import urlsplit

from ..core.dex import DexState
from ..core.perps import PerpClearinghouse2pMarketState
from ..state.canonical import canonical_hex_fixed_allow_0x
from .dex_snapshot import state_from_snapshot
from .perp_engine import PerpEngineConfig, apply_perp_ops
from .tau_net_client import (
    TauNetRpcError,
    TauNetTcpClient,
    TauNetTcpConfig,
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
    sign_perp_op_for_engine,
)
from .zusd_tau_token import derive_zusd_tau_asset_id


MAX_POST_BODY = 65_536
ResponseT = Tuple[int, Dict[str, Any]]
_STREAM_KEY = "8"
_ENGINE_STREAM_KEY = "5"
_U32_MAX = 0xFFFFFFFF
_ACTIONS = {
    "init_market_2p",
    "deposit_collateral",
    "withdraw_collateral",
    "set_position_pair",
    "advance_epoch",
    "publish_clearing_price",
    "settle_epoch",
}


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
    return min(max(value, lo), hi)


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        value = int(raw.strip())
    except Exception:
        return int(default)
    return min(max(value, lo), hi)


def _tau_client() -> TauNetTcpClient:
    return TauNetTcpClient(
        TauNetTcpConfig(
            host=_env_str("PERPS_WALLET_TAU_HOST", _env_str("ZUSD_MONETARY_WALLET_TAU_HOST", "127.0.0.1")),
            port=_env_int(
                "PERPS_WALLET_TAU_PORT",
                _env_int("ZUSD_MONETARY_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
                lo=1,
                hi=65535,
            ),
            timeout_s=_env_float(
                "PERPS_WALLET_TAU_TIMEOUT_S",
                _env_float("ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S", 3.0, lo=0.1, hi=60.0),
                lo=0.1,
                hi=60.0,
            ),
        )
    )


def _tau_chain_id() -> str:
    return _env_str("PERPS_WALLET_CHAIN_ID", _env_str("TAU_DEX_CHAIN_ID", "tau-local"))


def _allow_signing() -> bool:
    return _env_bool("PERPS_WALLET_ALLOW_LOCAL_SIGNING", False)


def _auto_mine() -> bool:
    return _env_bool("PERPS_WALLET_AUTO_MINE", False)


def _default_deadline() -> int:
    delta = _env_int("PERPS_WALLET_DEFAULT_DEADLINE_S", 3600, lo=1, hi=86_400)
    return int(time.time()) + int(delta)


def _canonical_pubkey(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _canonical_asset(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)


def _pubkey_for_rpc(value: str) -> str:
    s = value.strip().lower()
    return s[2:] if s.startswith("0x") else s


def _pubkey_from_privkey(privkey: object) -> str:
    if not isinstance(privkey, (str, int)):
        raise ValueError("privkey must be string or int")
    return "0x" + bls_pubkey_hex_from_privkey(cast(Any, privkey))


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


def _dex_state_view(app_state: Mapping[str, Any]) -> Mapping[str, Any]:
    dex_state = app_state.get("dex_state")
    if isinstance(dex_state, Mapping):
        return dex_state
    return app_state


def _state_from_app_state(app_state: Mapping[str, Any]) -> DexState:
    return state_from_snapshot(_dex_state_view(app_state))


def _balance_for_asset(app_state: Mapping[str, Any], *, pubkey: str, asset_id: str) -> int:
    state_view = _dex_state_view(app_state)
    raw = state_view.get("balances") or []
    if not isinstance(raw, list):
        raise TauNetRpcError("app_state balances must be a list")
    target_pubkey = pubkey.strip().lower()
    target_asset = asset_id.strip().lower()
    for index, entry in enumerate(raw):
        if not isinstance(entry, Mapping):
            raise TauNetRpcError(f"app_state.balances[{index}] must be an object")
        entry_pubkey = entry.get("pubkey")
        entry_asset = entry.get("asset")
        amount = entry.get("amount")
        if not isinstance(entry_pubkey, str) or not isinstance(entry_asset, str):
            raise TauNetRpcError(f"app_state.balances[{index}] has invalid keys")
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise TauNetRpcError(f"app_state.balances[{index}] amount invalid")
        if entry_pubkey.strip().lower() == target_pubkey and entry_asset.strip().lower() == target_asset:
            return int(amount)
    return 0


def _last_used_perp_nonce(app_state: Mapping[str, Any], *, signer_pubkey: str) -> int:
    state_view = _dex_state_view(app_state)
    raw = state_view.get("nonces") or []
    if not isinstance(raw, list):
        raise TauNetRpcError("app_state.nonces must be a list")
    key = _canonical_pubkey(signer_pubkey, name="signer_pubkey")
    last_nonce = 0
    for index, entry in enumerate(raw):
        if not isinstance(entry, Mapping):
            raise TauNetRpcError(f"app_state.nonces[{index}] must be an object")
        pubkey = entry.get("pubkey")
        if not isinstance(pubkey, str):
            raise TauNetRpcError(f"app_state.nonces[{index}].pubkey invalid")
        if pubkey.strip().lower() != key:
            continue
        nonce = entry.get("last_nonce", 0)
        if not isinstance(nonce, int) or isinstance(nonce, bool) or nonce < 0:
            raise TauNetRpcError(f"app_state.nonces[{index}].last_nonce invalid")
        last_nonce = int(nonce)
    return last_nonce


def _request_action(body: Mapping[str, Any]) -> str:
    action = str(body.get("action", "")).strip().lower()
    if action not in _ACTIONS:
        raise ValueError("unsupported_action")
    return action


def _request_u32(body: Mapping[str, Any], *, name: str, default: Optional[int] = None) -> int:
    if name not in body:
        if default is None:
            raise ValueError(f"missing_{name}")
        return int(default)
    value = body.get(name)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > _U32_MAX:
        raise ValueError(f"bad_{name}")
    return int(value)


def _request_int(body: Mapping[str, Any], *, name: str, default: Optional[int] = None) -> int:
    if name not in body:
        if default is None:
            raise ValueError(f"missing_{name}")
        return int(default)
    value = body.get(name)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"bad_{name}")
    return int(value)


def _request_positive_int(body: Mapping[str, Any], *, name: str) -> int:
    value = _request_int(body, name=name)
    if value <= 0:
        raise ValueError(f"bad_{name}")
    return int(value)


def _request_mapping(body: Mapping[str, Any], *, name: str) -> Mapping[str, Any] | None:
    if name not in body:
        return None
    raw = body.get(name)
    if isinstance(raw, str):
        try:
            parsed = json.loads(raw)
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            raise ValueError(f"bad_{name}") from exc
        raw = parsed
    if not isinstance(raw, Mapping):
        raise ValueError(f"bad_{name}")
    return raw


def _market_id(body: Mapping[str, Any]) -> str:
    raw = str(body.get("market_id") or body.get("marketId") or "").strip()
    if not raw:
        raise ValueError("missing_market_id")
    if len(raw) > 128 or not raw.startswith("perp:ch2p:"):
        raise ValueError("market_id must start with perp:ch2p:")
    return raw


def _quote_asset(body: Mapping[str, Any], *, chain_id: str) -> str:
    raw = body.get("quote_asset") if "quote_asset" in body else body.get("quoteAsset")
    if isinstance(raw, str) and raw.strip():
        return _canonical_asset(raw, name="quote_asset")
    return derive_zusd_tau_asset_id(chain_id=chain_id)


def _account_pubkey(body: Mapping[str, Any], *, field: str, privkey_field: str) -> str:
    raw = body.get(field)
    if isinstance(raw, str) and raw.strip():
        return _canonical_pubkey(raw, name=field)
    privkey = body.get(privkey_field)
    if privkey is not None:
        return _canonical_pubkey(_pubkey_from_privkey(privkey), name=field)
    raise ValueError(f"missing_{field}")


def _nonce_for_signer(body: Mapping[str, Any], *, app_state: Mapping[str, Any], field: str, signer_pubkey: str) -> int:
    if field in body:
        return _request_u32(body, name=field)
    return _last_used_perp_nonce(app_state, signer_pubkey=signer_pubkey) + 1


def _sign_or_copy(
    body: Mapping[str, Any],
    *,
    op: Mapping[str, Any],
    sig_field: str,
    privkey_field: str,
    chain_id: str,
    signer_pubkey: str,
    nonce: int,
) -> str:
    raw_sig = body.get(sig_field)
    if isinstance(raw_sig, str) and raw_sig.strip():
        return raw_sig.strip()
    privkey = body.get(privkey_field)
    if privkey is None:
        raise ValueError(f"missing_{sig_field}")
    if not _allow_signing():
        raise ValueError("local_signing_disabled")
    return sign_perp_op_for_engine(
        op,
        privkey=cast(Any, privkey),
        chain_id=chain_id,
        signer_pubkey=signer_pubkey,
        nonce=nonce,
    )


def _tx_sender_for_action(body: Mapping[str, Any], *, action: str, account_a_pubkey: str | None, account_pubkey: str | None) -> str:
    raw = body.get("sender_pubkey") if "sender_pubkey" in body else body.get("senderPubkey")
    if isinstance(raw, str) and raw.strip():
        return _canonical_pubkey(raw, name="sender_pubkey")
    if action in {"deposit_collateral", "withdraw_collateral", "publish_clearing_price"} and account_pubkey is not None:
        return account_pubkey
    if account_a_pubkey is not None:
        return account_a_pubkey
    operator_pubkey = body.get("operator_pubkey") if "operator_pubkey" in body else body.get("operatorPubkey")
    if isinstance(operator_pubkey, str) and operator_pubkey.strip():
        return _canonical_pubkey(operator_pubkey, name="operator_pubkey")
    env_operator = os.environ.get("TAU_DEX_OPERATOR_PUBKEY") or os.environ.get("TAU_DEX_PERP_OPERATOR_PUBKEY")
    if isinstance(env_operator, str) and env_operator.strip():
        return _canonical_pubkey(env_operator, name="operator_pubkey")
    raise ValueError("missing_sender_pubkey")


def _build_operation_and_sender(
    body: Mapping[str, Any],
    *,
    action: str,
    app_state: Mapping[str, Any],
    chain_id: str,
    deadline: int,
) -> tuple[dict[str, Any], str, dict[str, int | str]]:
    market_id = _market_id(body)
    meta: dict[str, int | str] = {}

    if action in {"deposit_collateral", "withdraw_collateral"}:
        account_pubkey = _account_pubkey(body, field="account_pubkey", privkey_field="account_privkey")
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=account_pubkey)
        operation = {
            "module": "TauPerp",
            "version": "1.0",
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "amount": _request_positive_int(body, name="amount"),
        }
        return operation, tx_sender, meta

    if action == "advance_epoch":
        operation = {
            "module": "TauPerp",
            "version": "1.0",
            "market_id": market_id,
            "action": action,
            "delta": _request_u32(body, name="delta", default=1),
        }
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=None)
        return operation, tx_sender, meta

    if action == "settle_epoch":
        operation = {
            "module": "TauPerp",
            "version": "1.0",
            "market_id": market_id,
            "action": action,
        }
        bridge = _request_mapping(body, name="oracle_adapter_bridge")
        if bridge is not None:
            operation["oracle_adapter_bridge"] = dict(bridge)
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=None)
        return operation, tx_sender, meta

    if action == "publish_clearing_price":
        oracle_pubkey_raw = body.get("oracle_pubkey") if "oracle_pubkey" in body else body.get("oraclePubkey")
        if isinstance(oracle_pubkey_raw, str) and oracle_pubkey_raw.strip():
            oracle_pubkey = _canonical_pubkey(oracle_pubkey_raw, name="oracle_pubkey")
        elif body.get("oracle_privkey") is not None:
            oracle_pubkey = _canonical_pubkey(_pubkey_from_privkey(body.get("oracle_privkey")), name="oracle_pubkey")
        else:
            env_oracle = os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY")
            if not isinstance(env_oracle, str) or not env_oracle.strip():
                raise ValueError("missing_oracle_pubkey")
            oracle_pubkey = _canonical_pubkey(env_oracle, name="oracle_pubkey")
        oracle_nonce = _nonce_for_signer(body, app_state=app_state, field="oracle_nonce", signer_pubkey=oracle_pubkey)
        operation = {
            "module": "TauPerp",
            "version": "1.0",
            "market_id": market_id,
            "action": action,
            "price_e8": _request_positive_int(body, name="price_e8"),
            "deadline": int(deadline),
            "oracle_nonce": oracle_nonce,
        }
        operation["oracle_sig"] = _sign_or_copy(
            body,
            op=operation,
            sig_field="oracle_sig",
            privkey_field="oracle_privkey",
            chain_id=chain_id,
            signer_pubkey=oracle_pubkey,
            nonce=oracle_nonce,
        )
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=oracle_pubkey)
        meta.update({"oracle_pubkey": oracle_pubkey, "oracle_nonce": oracle_nonce})
        return operation, tx_sender, meta

    account_a_pubkey = _account_pubkey(body, field="account_a_pubkey", privkey_field="account_a_privkey")
    account_b_pubkey = _account_pubkey(body, field="account_b_pubkey", privkey_field="account_b_privkey")
    nonce_a = _nonce_for_signer(body, app_state=app_state, field="nonce_a", signer_pubkey=account_a_pubkey)
    nonce_b = _nonce_for_signer(body, app_state=app_state, field="nonce_b", signer_pubkey=account_b_pubkey)
    tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=account_a_pubkey, account_pubkey=None)
    meta.update(
        {
            "account_a_pubkey": account_a_pubkey,
            "account_b_pubkey": account_b_pubkey,
            "nonce_a": nonce_a,
            "nonce_b": nonce_b,
        }
    )

    if action == "init_market_2p":
        operation = {
            "module": "TauPerp",
            "version": "1.0",
            "market_id": market_id,
            "action": action,
            "quote_asset": _quote_asset(body, chain_id=chain_id),
            "account_a_pubkey": account_a_pubkey,
            "account_b_pubkey": account_b_pubkey,
            "deadline": int(deadline),
            "nonce_a": nonce_a,
            "nonce_b": nonce_b,
        }
    else:
        new_a = _request_int(body, name="new_position_base_a")
        new_b = _request_int(body, name="new_position_base_b", default=-new_a)
        operation = {
            "module": "TauPerp",
            "version": "1.0",
            "market_id": market_id,
            "action": action,
            "account_a_pubkey": account_a_pubkey,
            "account_b_pubkey": account_b_pubkey,
            "new_position_base_a": new_a,
            "new_position_base_b": new_b,
            "deadline": int(deadline),
            "nonce_a": nonce_a,
            "nonce_b": nonce_b,
        }

    operation["sig_a"] = _sign_or_copy(
        body,
        op=operation,
        sig_field="sig_a",
        privkey_field="account_a_privkey",
        chain_id=chain_id,
        signer_pubkey=account_a_pubkey,
        nonce=nonce_a,
    )
    operation["sig_b"] = _sign_or_copy(
        body,
        op=operation,
        sig_field="sig_b",
        privkey_field="account_b_privkey",
        chain_id=chain_id,
        signer_pubkey=account_b_pubkey,
        nonce=nonce_b,
    )
    return operation, tx_sender, meta


def _default_oracle_adapter_bridge_verifier(bridge: Mapping[str, Any]) -> Any:
    from tools.zenodex_oracle_aggregate_adapter import (  # pylint: disable=import-outside-toplevel
        verify_aggregate_adapter_bridge,
    )

    return verify_aggregate_adapter_bridge(bridge)


def _build_perp_config(*, chain_id: str) -> PerpEngineConfig:
    operator_pubkey = os.environ.get("TAU_DEX_OPERATOR_PUBKEY") or os.environ.get("TAU_DEX_PERP_OPERATOR_PUBKEY")
    oracle_pubkey = os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY")
    return PerpEngineConfig(
        operator_pubkey=(operator_pubkey or "").strip() or None,
        chain_id=chain_id,
        oracle_pubkey=(oracle_pubkey or "").strip() or None,
        allow_isolated_markets=_env_bool("TAU_DEX_ALLOW_ISOLATED_PERPS", False),
        oracle_adapter_bridge_verifier=_default_oracle_adapter_bridge_verifier,
        require_oracle_adapter_for_clearinghouse_settle_epoch=_env_bool(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
            False,
        ),
    )


def _preflight(
    *,
    app_state: Mapping[str, Any],
    config: PerpEngineConfig,
    operation: Mapping[str, Any],
    tx_sender_pubkey: str,
    block_timestamp: int,
) -> dict[str, Any]:
    try:
        state = _state_from_app_state(app_state)
        res = apply_perp_ops(
            config=config,
            state=state,
            operations={_ENGINE_STREAM_KEY: [dict(operation)]},
            tx_sender_pubkey=tx_sender_pubkey,
            block_timestamp=int(block_timestamp),
        )
        return {"ok": bool(res.ok), "error": res.error, "effects": list(res.effects or [])}
    except Exception as exc:
        return {"ok": False, "error": str(exc), "effects": []}


def _market_summaries(app_state: Mapping[str, Any]) -> list[dict[str, Any]]:
    state = _state_from_app_state(app_state)
    if state.perps is None:
        return []
    summaries: list[dict[str, Any]] = []
    for market_id, market in sorted(state.perps.markets.items()):
        item: dict[str, Any] = {"market_id": market_id, "kind": getattr(market, "kind", "unknown")}
        if isinstance(market, PerpClearinghouse2pMarketState):
            item.update(
                {
                    "quote_asset": market.quote_asset,
                    "account_a_pubkey": market.account_a_pubkey,
                    "account_b_pubkey": market.account_b_pubkey,
                    "now_epoch": int(market.state.get("now_epoch", 0)),
                    "oracle_last_update_epoch": int(market.state.get("oracle_last_update_epoch", 0)),
                    "clearing_price_epoch": int(market.state.get("clearing_price_epoch", 0)),
                    "clearing_price_e8": int(market.state.get("clearing_price_e8", 0)),
                    "index_price_e8": int(market.state.get("index_price_e8", 0)),
                    "position_base_a": int(market.state.get("position_base_a", 0)),
                    "position_base_b": int(market.state.get("position_base_b", 0)),
                    "collateral_e8_a": int(market.state.get("collateral_e8_a", 0)),
                    "collateral_e8_b": int(market.state.get("collateral_e8_b", 0)),
                }
            )
        summaries.append(item)
    return summaries


def _tx_signer_privkey(body: Mapping[str, Any], *, action: str) -> object:
    privkey = body.get("tx_signer_privkey")
    if privkey is not None:
        return privkey
    if action in {"deposit_collateral", "withdraw_collateral"} and body.get("account_privkey") is not None:
        return body.get("account_privkey")
    if action == "publish_clearing_price" and body.get("oracle_privkey") is not None:
        return body.get("oracle_privkey")
    if action in {"advance_epoch", "settle_epoch"} and body.get("operator_privkey") is not None:
        return body.get("operator_privkey")
    if body.get("account_a_privkey") is not None:
        return body.get("account_a_privkey")
    if body.get("signer_privkey") is not None:
        return body.get("signer_privkey")
    raise ValueError("missing_tx_signer_privkey")


def _build_prepare_response(body: Mapping[str, Any], *, for_submit: bool) -> Dict[str, Any]:
    action = _request_action(body)
    chain_id = str(body.get("chain_id") or _tau_chain_id())
    deadline = _request_u32(body, name="deadline", default=_default_deadline())
    client = _tau_client()
    app_state, app_hash = _load_app_state(client)
    config = _build_perp_config(chain_id=chain_id)
    operation, tx_sender_pubkey, meta = _build_operation_and_sender(
        body,
        action=action,
        app_state=app_state,
        chain_id=chain_id,
        deadline=deadline,
    )
    operations = {_STREAM_KEY: [operation]}
    tx_sequence_number = int(client.get_sequence(_pubkey_for_rpc(tx_sender_pubkey)))
    block_timestamp = int(body.get("block_timestamp") if isinstance(body.get("block_timestamp"), int) else int(time.time()))
    preflight = _preflight(
        app_state=app_state,
        config=config,
        operation=operation,
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=block_timestamp,
    )
    if for_submit and not preflight.get("ok"):
        raise ValueError(f"preflight_failed: {preflight.get('error') or 'unknown'}")
    quote_asset = str(operation.get("quote_asset") or body.get("quote_asset") or body.get("quoteAsset") or "")
    account_pubkey = str(operation.get("account_pubkey") or meta.get("account_a_pubkey") or tx_sender_pubkey)
    quote_balance = _balance_for_asset(app_state, pubkey=account_pubkey, asset_id=quote_asset) if quote_asset else 0

    tau_tx_payload: dict[str, Any] | None = None
    if for_submit:
        if not _allow_signing():
            raise ValueError("local_signing_disabled")
        signer_privkey = _tx_signer_privkey(body, action=action)
        signer_pubkey = _canonical_pubkey(_pubkey_from_privkey(signer_privkey), name="tx_signer_pubkey")
        if signer_pubkey.lower() != tx_sender_pubkey.lower():
            raise ValueError("tx_signer_privkey does not match sender_pubkey")
        tau_tx_payload = build_signed_tau_transaction(
            privkey=cast(Any, signer_privkey),
            sequence_number=tx_sequence_number,
            expiration_time=deadline,
            operations=operations,
            fee_limit=body.get("tx_fee_limit", "0"),
        )

    payload: Dict[str, Any] = {
        "ok": True,
        "transport": {
            "chain_id": chain_id,
            "app_hash": app_hash,
            "stream_key": _STREAM_KEY,
            "engine_stream_key": _ENGINE_STREAM_KEY,
            "tx_sender_pubkey": tx_sender_pubkey,
            "tx_sequence_number": tx_sequence_number,
            "tau_host": _env_str("PERPS_WALLET_TAU_HOST", _env_str("ZUSD_MONETARY_WALLET_TAU_HOST", "127.0.0.1")),
            "tau_port": _env_int(
                "PERPS_WALLET_TAU_PORT",
                _env_int("ZUSD_MONETARY_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
                lo=1,
                hi=65535,
            ),
            "allow_local_signing": _allow_signing(),
            "auto_mine": _auto_mine(),
            "quote_balance": quote_balance,
        },
        "report": {
            "action": action,
            "operation": operation,
            "operations": operations,
            "preflight": preflight,
            "tau_tx_payload": tau_tx_payload,
            "nonce_a": meta.get("nonce_a"),
            "nonce_b": meta.get("nonce_b"),
            "oracle_nonce": meta.get("oracle_nonce"),
        },
    }
    if for_submit:
        send_resp = client.sendtx(cast(Mapping[str, Any], tau_tx_payload))
        payload["submission"] = {"sendtx_response": send_resp}
        if _auto_mine():
            payload["submission"]["createblock_response"] = client.createblock()
        app_state_after, app_hash_after = _load_app_state(client)
        payload["post_submit"] = {"app_hash": app_hash_after, "markets": _market_summaries(app_state_after)}
    return payload


def _status_payload() -> Dict[str, Any]:
    chain_id = _tau_chain_id()
    status: Dict[str, Any] = {
        "enabled": True,
        "chain_id": chain_id,
        "tau_host": _env_str("PERPS_WALLET_TAU_HOST", _env_str("ZUSD_MONETARY_WALLET_TAU_HOST", "127.0.0.1")),
        "tau_port": _env_int(
            "PERPS_WALLET_TAU_PORT",
            _env_int("ZUSD_MONETARY_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
            lo=1,
            hi=65535,
        ),
        "allow_local_signing": _allow_signing(),
        "auto_mine": _auto_mine(),
        "quote_asset_default": derive_zusd_tau_asset_id(chain_id=chain_id),
        "operator_pubkey": os.environ.get("TAU_DEX_OPERATOR_PUBKEY") or os.environ.get("TAU_DEX_PERP_OPERATOR_PUBKEY") or None,
        "oracle_pubkey": os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY") or None,
        "require_oracle_adapter_for_clearinghouse_settle_epoch": _env_bool(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
            False,
        ),
    }
    try:
        client = _tau_client()
        hello = client.rpc("hello version=1").strip()
        app_state, app_hash = _load_app_state(client)
        markets = _market_summaries(app_state)
        status["node_reachable"] = True
        status["hello"] = hello
        status["app_hash"] = app_hash
        status["app_bridge_available"] = bool(app_state or app_hash)
        status["market_count"] = len(markets)
        status["markets"] = markets
    except Exception as exc:
        status["node_reachable"] = False
        status["error"] = f"{type(exc).__name__}: {exc}"
    return status


def handle_perps_wallet_request(method: str, path: str, body: Optional[bytes]) -> ResponseT:
    parsed_path = urlsplit(path)
    segments = [segment for segment in parsed_path.path.split("/") if segment]
    if len(segments) < 4 or segments[0] != "api" or segments[1] != "perps" or segments[2] != "wallet":
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
        if rest == ["prepare"]:
            return 200, _build_prepare_response(parsed, for_submit=False)
        if rest == ["submit"]:
            return 200, _build_prepare_response(parsed, for_submit=True)
        return 404, {"ok": False, "error": "not_found"}
    except (ValueError, TypeError) as exc:
        return 400, {"ok": False, "error": str(exc)}
    except TauNetRpcError as exc:
        return 502, {"ok": False, "error": "tau_rpc_error", "detail": str(exc)}
