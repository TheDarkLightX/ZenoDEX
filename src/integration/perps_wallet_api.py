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
from ..core.perps import PerpClearinghouse2pMarketState, PerpMarketState
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
    "partial_liquidate",
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


def _market_quote_asset(app_state: Mapping[str, Any], *, market_id: str) -> str:
    state = _state_from_app_state(app_state)
    if state.perps is None:
        return ""
    try:
        market = state.perps.get_market(market_id)
    except Exception:
        return ""
    if isinstance(market, PerpClearinghouse2pMarketState):
        return str(market.quote_asset)
    return ""


def _safe_native_balance(client: TauNetTcpClient, pubkey: str) -> int | None:
    try:
        return int(client.get_balance(_pubkey_for_rpc(pubkey)))
    except Exception:
        return None


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


def _request_tx_fee_limit(body: Mapping[str, Any]) -> int:
    raw = body.get("tx_fee_limit", 0)
    if isinstance(raw, bool):
        raise ValueError("bad_tx_fee_limit")
    if isinstance(raw, int):
        value = raw
    elif isinstance(raw, str):
        text = raw.strip()
        if not text:
            return 0
        if not text.isdigit():
            raise ValueError("bad_tx_fee_limit")
        value = int(text, 10)
    else:
        raise ValueError("bad_tx_fee_limit")
    if value < 0 or value > 10**30:
        raise ValueError("bad_tx_fee_limit")
    return int(value)


def _fee_limit_posture(*, tx_fee_limit: int, native_balance: int | None) -> dict[str, Any]:
    ok = None if native_balance is None else bool(int(native_balance) >= int(tx_fee_limit))
    warning = None
    if ok is None and tx_fee_limit > 0:
        warning = "native balance unavailable; Tau fee-limit coverage could not be checked"
    elif ok is False:
        warning = "native balance is below requested Tau fee limit"
    return {
        "tx_fee_limit": str(int(tx_fee_limit)),
        "native_balance": native_balance,
        "native_balance_covers_fee_limit": ok,
        "warning": warning,
    }


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


def _market_id(body: Mapping[str, Any], *, action: str | None = None) -> str:
    raw = str(body.get("market_id") or body.get("marketId") or "").strip()
    if not raw:
        raise ValueError("missing_market_id")
    if len(raw) > 128:
        raise ValueError("bad_market_id")
    if action == "partial_liquidate":
        if not raw.startswith("perp:") or raw.startswith("perp:ch2p:"):
            raise ValueError("isolated market_id must start with perp: and not perp:ch2p:")
        return raw
    if not raw.startswith("perp:ch2p:"):
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
    if action in {"deposit_collateral", "withdraw_collateral", "publish_clearing_price", "partial_liquidate"} and account_pubkey is not None:
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
    market_id = _market_id(body, action=action)
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

    if action == "partial_liquidate":
        account_pubkey = _account_pubkey(body, field="account_pubkey", privkey_field="account_privkey")
        fraction_bps = _request_u32(body, name="fraction_bps")
        if fraction_bps > 10_000:
            raise ValueError("bad_fraction_bps")
        operation = {
            "module": "TauPerp",
            "version": "0.1",
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "fraction_bps": fraction_bps,
        }
        bridge = _request_mapping(body, name="oracle_adapter_bridge")
        if bridge is not None:
            operation["oracle_adapter_bridge"] = dict(bridge)
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=account_pubkey)
        meta.update({"account_pubkey": account_pubkey})
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
        require_oracle_adapter_for_isolated_partial_liquidate=_env_bool(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE",
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
                    "account_a_quote_balance": _balance_for_asset(
                        app_state,
                        pubkey=market.account_a_pubkey,
                        asset_id=market.quote_asset,
                    ),
                    "account_b_quote_balance": _balance_for_asset(
                        app_state,
                        pubkey=market.account_b_pubkey,
                        asset_id=market.quote_asset,
                    ),
                    "now_epoch": int(market.state.get("now_epoch", 0)),
                    "oracle_last_update_epoch": int(market.state.get("oracle_last_update_epoch", 0)),
                    "clearing_price_epoch": int(market.state.get("clearing_price_epoch", 0)),
                    "clearing_price_e8": int(market.state.get("clearing_price_e8", 0)),
                    "index_price_e8": int(market.state.get("index_price_e8", 0)),
                    "position_base_a": int(market.state.get("position_base_a", 0)),
                    "position_base_b": int(market.state.get("position_base_b", 0)),
                    "collateral_e8_a": int(market.state.get("collateral_e8_a", 0)),
                    "collateral_e8_b": int(market.state.get("collateral_e8_b", 0)),
                    "fee_pool_e8": int(market.state.get("fee_pool_e8", 0)),
                    "liquidated_this_step": bool(market.state.get("liquidated_this_step", False)),
                    "net_deposited_e8": int(market.state.get("net_deposited_e8", 0)),
                    "maintenance_margin_bps": int(market.state.get("maintenance_margin_bps", 0)),
                    "liquidation_penalty_bps": int(market.state.get("liquidation_penalty_bps", 0)),
                }
            )
        elif isinstance(market, PerpMarketState):
            accounts = []
            for account_pubkey, account in sorted(market.accounts.items()):
                accounts.append(
                    {
                        "account_pubkey": account_pubkey,
                        "position_base": int(account.position_base),
                        "collateral_quote": int(account.collateral_quote),
                        "liquidated_this_step": bool(account.liquidated_this_step),
                    }
                )
            item.update(
                {
                    "quote_asset": market.quote_asset,
                    "now_epoch": int(market.global_state.get("now_epoch", 0)),
                    "index_price_e8": int(market.global_state.get("index_price_e8", 0)),
                    "fee_pool_quote": int(market.global_state.get("fee_pool_quote", 0)),
                    "insurance_balance": int(market.global_state.get("insurance_balance", 0)),
                    "account_count": len(accounts),
                    "accounts": accounts,
                }
            )
        summaries.append(item)
    return summaries


def _local_perps_oracle_bridge_fixture(
    *,
    app_state: Mapping[str, Any],
    config: PerpEngineConfig,
    market_id: str,
    action: str,
    account_pubkey: str | None = None,
    fraction_bps: int = 0,
) -> dict[str, Any]:
    wallet_action = action
    from tools.zenodex_oracle import ACTION_TYPE, receipt_content_hash  # pylint: disable=import-outside-toplevel
    from tools.zenodex_oracle_adapter import (  # pylint: disable=import-outside-toplevel
        ACTION_SCHEMA,
        PROFILE_SCHEMA,
        profile_content_hash,
    )
    from tools.zenodex_oracle_admitted_median3 import (  # pylint: disable=import-outside-toplevel
        sample_admitted_median3_aggregate,
        verify_admitted_median3_aggregate,
    )
    from tools.zenodex_oracle_aggregate_adapter import (  # pylint: disable=import-outside-toplevel
        AGGREGATE_ADAPTER_SCHEMA,
        aggregate_adapter_content_hash,
        verify_aggregate_adapter_bridge,
    )
    from tools.zenodex_oracle_aggregate_read import (  # pylint: disable=import-outside-toplevel
        AGGREGATE_READ_SCHEMA,
        _bundle_for_aggregate,
        aggregate_read_value_hash,
        bridge_content_hash as aggregate_read_content_hash,
    )
    from .perp_engine import (  # pylint: disable=import-outside-toplevel
        _ORACLE_PERPS_INDEX_QUERY_ID,
        _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
        _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        _perps_clearinghouse_runtime_oracle_action_id,
        _perps_liquidate_account_runtime_oracle_action_id,
    )

    state = _state_from_app_state(app_state)
    if state.perps is None:
        raise ValueError("missing_perps_state")
    market = state.perps.get_market(market_id)
    if wallet_action == "settle_epoch":
        if not isinstance(market, PerpClearinghouse2pMarketState):
            raise ValueError("settle_epoch oracle bridge fixture supports clearinghouse_2p markets only")
        action_kind = "settle_epoch"
        profile_id = _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID
        freshness_window_epochs = 2
        action_id = _perps_clearinghouse_runtime_oracle_action_id(
            config,
            market_id=market_id,
            action_kind=action_kind,
            market_kind="clearinghouse_2p_v1",
            quote_asset=market.quote_asset,
            state=market.state,
            participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
        )
    elif wallet_action == "partial_liquidate":
        if not isinstance(market, PerpMarketState):
            raise ValueError("partial_liquidate oracle bridge fixture supports isolated markets only")
        if account_pubkey is None:
            raise ValueError("missing_account_pubkey")
        action_kind = "liquidate_account"
        profile_id = _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID
        freshness_window_epochs = 1
        action_id = _perps_liquidate_account_runtime_oracle_action_id(
            config,
            market_id=market_id,
            market=market,
            account_pubkey=account_pubkey,
            fraction_bps=fraction_bps,
        )
    else:
        raise ValueError("unsupported_oracle_bridge_action")

    aggregate = sample_admitted_median3_aggregate()
    aggregate_result = verify_admitted_median3_aggregate(aggregate)
    if aggregate_result.status != "accepted":
        raise ValueError("local oracle aggregate fixture rejected")
    if aggregate_result.query_id != _ORACLE_PERPS_INDEX_QUERY_ID:
        raise ValueError("local oracle aggregate fixture query mismatch")

    value_hash = aggregate_read_value_hash(
        aggregate_id=str(aggregate_result.aggregate_id),
        query_id=str(aggregate_result.query_id),
        value_e8=int(aggregate_result.value_e8),
        confidence_e8=int(aggregate_result.confidence_e8),
        deviation_bps=int(aggregate_result.deviation_bps),
        observed_epoch=int(aggregate_result.observed_epoch),
        report_count=int(aggregate_result.report_count),
        admission_count=int(aggregate_result.admission_count),
    )
    bundle = _bundle_for_aggregate(
        aggregate_id=str(aggregate_result.aggregate_id),
        query_id=str(aggregate_result.query_id),
        value_hash=value_hash,
        observed_epoch=int(aggregate_result.observed_epoch),
        freshness_window_epochs=freshness_window_epochs,
    )
    read_receipt_id = str(bundle["terminal"]["read_receipt_id"])
    read_receipt = next(
        receipt
        for receipt in bundle["receipts"]
        if isinstance(receipt, Mapping) and receipt.get("id") == read_receipt_id
    )
    action_epoch = int(aggregate_result.observed_epoch) + 1
    action_receipt: dict[str, Any] = {
        "type": ACTION_TYPE,
        "status": "accepted",
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "action_id": action_id,
        "action_epoch": action_epoch,
        "freshness_window_epochs": freshness_window_epochs,
        "query_id": str(aggregate_result.query_id),
        "value_hash": value_hash,
        "read_receipt_id": read_receipt_id,
        "critical": True,
        "emergency_oracle_bypass": False,
        "depends_on": [read_receipt_id],
    }
    action_receipt["id"] = receipt_content_hash(action_receipt)
    bundle["receipts"] = [dict(read_receipt), action_receipt]
    bundle["terminal"]["consumer_action_receipt_id"] = action_receipt["id"]

    aggregate_read: dict[str, Any] = {
        "schema": AGGREGATE_READ_SCHEMA,
        "freshness_window_epochs": freshness_window_epochs,
        "aggregate": dict(aggregate),
        "receipt_bundle": bundle,
    }
    aggregate_read["bridge_id"] = aggregate_read_content_hash(aggregate_read)

    adapter_action = {
        "schema": ACTION_SCHEMA,
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "action_id": action_id,
        "action_epoch": action_epoch,
        "query_id": str(aggregate_result.query_id),
        "value_hash": value_hash,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": freshness_window_epochs,
        "read_receipt_id": read_receipt_id,
        "consumer_action_receipt_id": action_receipt["id"],
        "critical": True,
    }
    profile = {
        "schema": PROFILE_SCHEMA,
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "query_id": str(aggregate_result.query_id),
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": freshness_window_epochs,
        "critical": True,
    }
    profile["profile_id"] = profile_content_hash(profile)
    if profile["profile_id"] != profile_id:
        raise ValueError("local oracle profile fixture mismatch")

    bridge = {
        "schema": AGGREGATE_ADAPTER_SCHEMA,
        "aggregate_read": aggregate_read,
        "action": adapter_action,
        "profile": profile,
    }
    bridge["bridge_id"] = aggregate_adapter_content_hash(bridge)
    verify_result = verify_aggregate_adapter_bridge(bridge).to_json_obj()
    if verify_result.get("status") != "accepted":
        raise ValueError(f"local oracle bridge fixture rejected: {verify_result.get('errors')}")
    return {
        "schema": "zenodex.perps_wallet.oracle_bridge_fixture.v1",
        "ok": True,
        "fixture_kind": "local_o3_aggregate_adapter",
        "production_authority": False,
        "market_id": market_id,
        "action": wallet_action,
        "target": {
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": profile_id,
            "action_id": action_id,
            "consumer_module": "zenodex.perps",
            "action_kind": action_kind,
            "wallet_action": wallet_action,
        },
        "bridge": bridge,
        "verify_result": verify_result,
    }


def _tx_signer_privkey(body: Mapping[str, Any], *, action: str) -> object:
    privkey = body.get("tx_signer_privkey")
    if privkey is not None:
        return privkey
    if action in {"deposit_collateral", "withdraw_collateral", "partial_liquidate"} and body.get("account_privkey") is not None:
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
    native_balance = _safe_native_balance(client, tx_sender_pubkey)
    tx_fee_limit = _request_tx_fee_limit(body)
    fee_limit_posture = _fee_limit_posture(tx_fee_limit=tx_fee_limit, native_balance=native_balance)
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
    if not quote_asset:
        quote_asset = _market_quote_asset(app_state, market_id=_market_id(body, action=action))
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
            fee_limit=tx_fee_limit,
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
            "native_balance_e8": native_balance,
            "tx_fee_limit": str(tx_fee_limit),
            "fee_limit_native_balance_ok": fee_limit_posture["native_balance_covers_fee_limit"],
            "fee_limit_warning": fee_limit_posture["warning"],
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
            "fee_limit": fee_limit_posture,
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
        "allow_isolated_markets": _env_bool("TAU_DEX_ALLOW_ISOLATED_PERPS", False),
        "require_oracle_adapter_for_isolated_partial_liquidate": _env_bool(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE",
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
        if rest == ["oracle-bridge-template"]:
            action = str(parsed.get("action", "settle_epoch")).strip().lower()
            if action not in {"settle_epoch", "partial_liquidate"}:
                return 400, {"ok": False, "error": "unsupported_oracle_bridge_action"}
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            client = _tau_client()
            app_state, _app_hash = _load_app_state(client)
            config = _build_perp_config(chain_id=chain_id)
            account_pubkey: str | None = None
            fraction_bps = 0
            if action == "partial_liquidate":
                account_pubkey = _account_pubkey(parsed, field="account_pubkey", privkey_field="account_privkey")
                fraction_bps = _request_u32(parsed, name="fraction_bps")
                if fraction_bps > 10_000:
                    raise ValueError("bad_fraction_bps")
            return 200, _local_perps_oracle_bridge_fixture(
                app_state=app_state,
                config=config,
                market_id=_market_id(parsed, action=action),
                action=action,
                account_pubkey=account_pubkey,
                fraction_bps=fraction_bps,
            )
        return 404, {"ok": False, "error": "not_found"}
    except (ValueError, TypeError) as exc:
        return 400, {"ok": False, "error": str(exc)}
    except TauNetRpcError as exc:
        return 502, {"ok": False, "error": "tau_rpc_error", "detail": str(exc)}
