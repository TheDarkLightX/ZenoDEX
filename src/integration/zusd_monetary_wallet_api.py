"""Tau-node-backed zUSD monetary wallet API.

This module exposes a mounted live surface for stream-11 zUSD monetary
operations. It follows the same prepare/submit shape as
``zusd_tau_wallet_api.py`` while targeting collateral, mint, repay, redeem,
stability-pool, liquidation, and SP collateral-claim actions.
"""

from __future__ import annotations

import json
import hashlib
import math
import os
import time
from dataclasses import asdict, replace
from typing import Any, Dict, Mapping, Optional, Tuple, cast
from urllib.parse import urlsplit

from ..core.dex import DexState
from ..core.zusd import E8
from .dex_snapshot import state_from_snapshot
from ..state.balances import BalanceTable, NATIVE_ASSET
from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes, sha256_hex
from .live_proof_wrapper import (
    live_zk_proof_required,
    proof_from_request,
    require_live_proof_wrapper,
    verify_live_proof_wrapper,
)
from .tau_net_client import (
    TauNetRpcError,
    TauNetTcpClient,
    TauNetTcpConfig,
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
    encode_tau_operations_for_wire,
    verify_tau_transaction_payload_signature,
)
from .zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    ZUSDMonetaryState,
    apply_zusd_monetary_ops,
    init_monetary_state,
    stability_pool_pubkey,
    zusd_monetary_sender_nonce_key,
    zusd_monetary_state_from_obj,
    zusd_monetary_state_to_obj,
)
from .zusd_tau_token import derive_zusd_tau_asset_id
from .zeno_oracle_authorization import (
    RuntimeActionFacts,
    check_critical_consumer_authorization,
    semantic_hash,
)


MAX_POST_BODY = 65_536
ResponseT = Tuple[int, Dict[str, Any]]
_STREAM_KEY = "11"
_U32_MAX = 0xFFFFFFFF
_ZUSD_PROOF_PROFILE_ID = "zusd_stream11_live_monetary_v0"
_ZUSD_PROOF_PROFILE_SCHEMA = "zenodex/zusd_monetary_wallet/proof_profile/v1"
_ZUSD_PROOF_INTENT_SCHEMA = "zenodex/zusd_monetary_wallet/proof_intent_receipt/v1"
_ZUSD_PROOF_INTENT_HASH_DOMAIN = "zenodex.zusd_monetary_wallet.proof_intent_receipt/v1"
_ZUSD_ZK_PROOF_ENV_PREFIX = "ZUSD_MONETARY_WALLET"
_ZUSD_ZK_PROOF_REQUIRED_ENV = "ZUSD_MONETARY_WALLET_REQUIRE_ZK_PROOF"
_ORACLE_CONSUMER_PROFILE_SCHEMA = "zenodex.oracle.consumer_profile.v1"
_ORACLE_ZUSD_COLLATERAL_QUERY_ID = (
    "sha256:" + hashlib.sha256(b"zenodex.oracle.query.zusd.collateral_price_e8").hexdigest()
)
_ZUSD_ORACLE_ADAPTER_ACTIONS: Dict[str, str] = {
    "mint_zusd": "mint",
    "liquidate": "liquidate_vault",
}
_ZUSD_ORACLE_AUTH_ACTIONS = {
    "bootstrap_oracle",
    "oracle_report",
    "oracle_commit",
    "mint_zusd",
    "liquidate",
}
_ACTIONS = {
    "advance_epoch",
    "bootstrap_oracle",
    "oracle_report",
    "oracle_commit",
    "deposit_collateral",
    "withdraw_collateral",
    "mint_zusd",
    "repay_zusd",
    "deposit_sp",
    "withdraw_sp",
    "redeem_zusd",
    "liquidate",
    "claim_sp_collateral",
}


def _oracle_consumer_profile_id(*, action_kind: str, max_freshness_window_epochs: int) -> str:
    payload = {
        "schema": _ORACLE_CONSUMER_PROFILE_SCHEMA,
        "consumer_module": "zenodex.zusd",
        "action_kind": action_kind,
        "query_id": _ORACLE_ZUSD_COLLATERAL_QUERY_ID,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": int(max_freshness_window_epochs),
        "critical": True,
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


_ZUSD_ORACLE_CONSUMER_PROFILE_IDS: Dict[str, str] = {
    "mint": _oracle_consumer_profile_id(action_kind="mint", max_freshness_window_epochs=2),
    "liquidate_vault": _oracle_consumer_profile_id(
        action_kind="liquidate_vault",
        max_freshness_window_epochs=1,
    ),
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
    value = raw.strip().lower()
    if value in {"1", "true", "yes", "on"}:
        return True
    if value in {"0", "false", "no", "off"}:
        return False
    raise ValueError(
        f"{name} must be one of 1,true,yes,on,0,false,no,off; got {raw!r}"
    )


def _env_bool_alias(primary: str, fallback: str, default: bool) -> bool:
    if os.environ.get(primary, "").strip():
        return _env_bool(primary, default)
    return _env_bool(fallback, default)


def _env_float(name: str, default: float, *, lo: float, hi: float) -> float:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        value = float(default)
    else:
        try:
            value = float(raw.strip())
        except ValueError as exc:
            raise ValueError(
                f"{name} must be a finite float in [{lo}, {hi}]; got {raw!r}"
            ) from exc
    if not math.isfinite(value) or value < lo or value > hi:
        raise ValueError(f"{name} must be finite and in [{lo}, {hi}]; got {value!r}")
    return float(value)


def _env_float_alias(primary: str, fallback: str, default: float, *, lo: float, hi: float) -> float:
    if os.environ.get(primary, "").strip():
        return _env_float(primary, default, lo=lo, hi=hi)
    return _env_float(fallback, default, lo=lo, hi=hi)


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        value = int(default)
    else:
        try:
            value = int(raw.strip())
        except ValueError as exc:
            raise ValueError(
                f"{name} must be an integer in [{lo}, {hi}]; got {raw!r}"
            ) from exc
    if value < lo or value > hi:
        raise ValueError(f"{name} must be in [{lo}, {hi}]; got {value}")
    return int(value)


def _env_int_alias(primary: str, fallback: str, default: int, *, lo: int, hi: int) -> int:
    if os.environ.get(primary, "").strip():
        return _env_int(primary, default, lo=lo, hi=hi)
    return _env_int(fallback, default, lo=lo, hi=hi)


def _hash_payload(domain: str, payload: Mapping[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(domain) + canonical_json_bytes(dict(payload)))


def _oracle_authorization_required() -> bool:
    return _env_bool_alias(
        "ZUSD_MONETARY_WALLET_ORACLE_AUTHORIZATION_REQUIRED",
        "ZUSD_ORACLE_AUTHORIZATION_REQUIRED",
        False,
    )


def _operation_bound_args(operation: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        str(key): value
        for key, value in operation.items()
        if key not in {"oracle_authorization", "oracle_adapter_bridge"}
    }


def _oracle_action_kind(action: str) -> str:
    return _ZUSD_ORACLE_ADAPTER_ACTIONS.get(action, action)


def _oracle_runtime_value_e8(zusd_state: ZUSDMonetaryState, *, action: str, operation: Mapping[str, Any]) -> int | None:
    core = zusd_state.core
    if action in {"bootstrap_oracle", "oracle_report"}:
        value = operation.get("price_e8")
        if isinstance(value, int) and not isinstance(value, bool) and value > 0:
            return int(value)
        return None
    if action == "oracle_commit":
        return int(core.price_pending_e8) if int(core.price_pending_e8) > 0 else None
    if action == "mint_zusd":
        return int(core.price_e8) if int(core.price_e8) > 0 else None
    if action == "liquidate":
        return int(core.price_pending_e8) if int(core.price_pending_e8) > 0 else None
    return None


def _oracle_pre_state_hash(zusd_state: ZUSDMonetaryState) -> str:
    return semantic_hash(
        "zenodex.zusd_monetary.pre_state.v1",
        {"state": zusd_monetary_state_to_obj(zusd_state)},
    )


def _oracle_action_facts_hash(
    *,
    zusd_state: ZUSDMonetaryState,
    action: str,
    action_kind: str,
    operation: Mapping[str, Any],
    query_id: str,
    runtime_value_e8: int,
) -> str:
    core = zusd_state.core
    return semantic_hash(
        "zenodex.zusd_monetary.critical_action_facts.v1",
        {
            "action": action,
            "action_kind": action_kind,
            "operation": _operation_bound_args(operation),
            "now_epoch": int(core.now_epoch),
            "oracle_last_update_epoch": int(core.oracle_last_update_epoch),
            "price_e8": int(core.price_e8),
            "price_pending_e8": int(core.price_pending_e8),
            "query_id": query_id,
            "runtime_value_e8": int(runtime_value_e8),
            "vault_owner_pubkey": zusd_state.vault_owner_pubkey,
        },
    )


def _oracle_action_id(
    *,
    action_facts_hash: str,
    pre_state_hash: str,
    query_id: str,
    runtime_value_e8: int,
) -> str:
    return semantic_hash(
        "zenodex.zusd_monetary.action_id.v1",
        {
            "action_facts_hash": action_facts_hash,
            "pre_state_hash": pre_state_hash,
            "query_id": query_id,
            "runtime_value_e8": int(runtime_value_e8),
        },
    )


def _max_freshness_window_epochs_for_action(action_kind: str) -> int:
    if action_kind == "liquidate_vault":
        return 1
    return 2


def _oracle_profile_id_for_action(action_kind: str) -> str:
    return _ZUSD_ORACLE_CONSUMER_PROFILE_IDS.get(action_kind, "critical-zusd-v1")


def _zusd_state_for_runtime(app_state: Mapping[str, Any], *, config: ZUSDMonetaryConfig) -> ZUSDMonetaryState:
    return _zusd_state_view(app_state) or init_monetary_state(config)


def _oracle_runtime_facts(
    *,
    zusd_state: ZUSDMonetaryState,
    action: str,
    operation: Mapping[str, Any],
) -> RuntimeActionFacts | None:
    if action not in _ZUSD_ORACLE_AUTH_ACTIONS:
        return None
    runtime_value_e8 = _oracle_runtime_value_e8(zusd_state, action=action, operation=operation)
    if runtime_value_e8 is None:
        return None
    action_kind = _oracle_action_kind(action)
    query_id = _ORACLE_ZUSD_COLLATERAL_QUERY_ID
    pre_state_hash = _oracle_pre_state_hash(zusd_state)
    action_facts_hash = _oracle_action_facts_hash(
        zusd_state=zusd_state,
        action=action,
        action_kind=action_kind,
        operation=operation,
        query_id=query_id,
        runtime_value_e8=runtime_value_e8,
    )
    return RuntimeActionFacts(
        consumer_module="zenodex.zusd",
        action_kind=action_kind,
        action_id=_oracle_action_id(
            action_facts_hash=action_facts_hash,
            pre_state_hash=pre_state_hash,
            query_id=query_id,
            runtime_value_e8=runtime_value_e8,
        ),
        action_facts_hash=action_facts_hash,
        pre_state_hash=pre_state_hash,
        profile_id=_oracle_profile_id_for_action(action_kind),
        query_id=query_id,
        runtime_value_e8=int(runtime_value_e8),
        now_epoch=int(zusd_state.core.now_epoch),
        max_freshness_window_epochs=_max_freshness_window_epochs_for_action(action_kind),
    )


def _oracle_runtime_report(
    *,
    runtime: RuntimeActionFacts | None,
    auth_result: Mapping[str, Any] | None = None,
) -> Dict[str, Any]:
    if runtime is None:
        return {
            "required": False,
            "consumer_module": "zenodex.zusd",
            "query_id": _ORACLE_ZUSD_COLLATERAL_QUERY_ID,
            "runtime_action": None,
            "authorization_check": None,
        }
    return {
        "required": _oracle_authorization_required(),
        "consumer_module": runtime.consumer_module,
        "action_kind": runtime.action_kind,
        "query_id": runtime.query_id,
        "profile_id": runtime.profile_id,
        "runtime_value_e8": int(runtime.runtime_value_e8),
        "now_epoch": int(runtime.now_epoch),
        "action_id": runtime.action_id,
        "action_facts_hash": runtime.action_facts_hash,
        "pre_state_hash": runtime.pre_state_hash,
        "max_freshness_window_epochs": runtime.max_freshness_window_epochs,
        "required_evidence_floor": "O3",
        "runtime_action": asdict(runtime),
        "authorization_check": dict(auth_result) if auth_result is not None else None,
    }


def _check_oracle_authorization(
    *,
    body: Mapping[str, Any],
    runtime: RuntimeActionFacts | None,
    enforce: bool,
) -> tuple[str | None, Dict[str, Any]]:
    if runtime is None:
        return None, _oracle_runtime_report(runtime=None)
    required = _oracle_authorization_required()
    auth_obj = body.get("oracle_authorization")
    if auth_obj is None:
        if required and enforce:
            return "oracle_authorization_required", _oracle_runtime_report(runtime=runtime)
        return None, _oracle_runtime_report(runtime=runtime)
    if not isinstance(auth_obj, Mapping):
        if enforce:
            return "oracle_authorization must be an object", _oracle_runtime_report(runtime=runtime)
        return None, _oracle_runtime_report(runtime=runtime)
    try:
        result = check_critical_consumer_authorization(
            auth_obj,
            consumer_module=runtime.consumer_module,
            action_kind=runtime.action_kind,
            action_id=runtime.action_id,
            action_facts_hash=runtime.action_facts_hash,
            pre_state_hash=runtime.pre_state_hash,
            profile_id=runtime.profile_id,
            query_id=runtime.query_id,
            runtime_value_e8=runtime.runtime_value_e8,
            now_epoch=runtime.now_epoch,
            runtime_notional_value_e8=runtime.runtime_notional_value_e8,
            max_freshness_window_epochs=runtime.max_freshness_window_epochs,
            require_receipt_graph=True,
        )
    except Exception as exc:
        if enforce:
            return f"oracle_authorization_rejected: {type(exc).__name__}: {exc}", _oracle_runtime_report(runtime=runtime)
        return None, _oracle_runtime_report(runtime=runtime)
    if result.get("typed_ok") is True:
        return None, _oracle_runtime_report(runtime=runtime, auth_result=result)
    errors = result.get("typed_errors")
    if isinstance(errors, list) and errors:
        detail = ",".join(str(error) for error in errors)
    else:
        detail = "typed authorization rejected"
    if enforce:
        return f"oracle_authorization_rejected:{detail}", _oracle_runtime_report(runtime=runtime, auth_result=result)
    return None, _oracle_runtime_report(runtime=runtime, auth_result=result)


def _zusd_proof_profile() -> dict[str, Any]:
    return {
        "schema": _ZUSD_PROOF_PROFILE_SCHEMA,
        "profile_id": _ZUSD_PROOF_PROFILE_ID,
        "claim_scope": "deterministic_stream11_live_monetary_receipt",
        "covered": [
            "stream11_operation_hash_binding",
            "pre_app_hash_binding",
            "tau_envelope_signature_binding",
            "monetary_preflight_replay",
            "post_submit_app_hash_binding_when_available",
        ],
        "not_covered": [
            "risc0_zkvm_wrapper",
            "production_finality",
            "hardware_wallet_key_custody",
            "exact_liquity_v2_liquidation_parity",
        ],
        "non_claims": [
            "does_not_claim_zusd_zk_execution",
            "does_not_claim_production_finality",
            "does_not_claim_wallet_key_custody",
            "does_not_claim_exact_liquity_v2_parity",
        ],
        "zk_proof_verified": False,
        "artifact_binding_complete": False,
        "zk_wrapper_required_for_production_claim": True,
        "artifact_binding_required_for_production_claim": True,
        "promotion_ready": False,
    }


def _zusd_proof_intent_receipt(
    *,
    chain_id: str,
    action: str,
    asset_id: str,
    operation: Mapping[str, Any],
    operations: Mapping[str, Any],
    app_hash_before: str | None,
    app_hash_after: str | None,
    preflight: Mapping[str, Any],
    actor_pubkey: str,
    nonce_before: int,
    nonce_after: int,
    tx_sequence_number: int,
    tx_fee_limit: int,
    signing_mode: str,
    tau_tx_payload: Mapping[str, Any] | None,
) -> dict[str, Any]:
    tau_tx_hash = None
    if tau_tx_payload is not None:
        tau_tx_hash = _hash_payload("zenodex.zusd_monetary_wallet.tau_tx_payload/v1", tau_tx_payload)
    body = {
        "schema": _ZUSD_PROOF_INTENT_SCHEMA,
        "profile_id": _ZUSD_PROOF_PROFILE_ID,
        "chain_id": chain_id,
        "stream_key": _STREAM_KEY,
        "action": action,
        "asset_id": asset_id,
        "app_hash_before": app_hash_before,
        "app_hash_after": app_hash_after,
        "operation_hash": _hash_payload("zenodex.zusd_monetary_wallet.operation/v1", operation),
        "operations_hash": _hash_payload("zenodex.zusd_monetary_wallet.operations/v1", operations),
        "preflight_ok": bool(preflight.get("ok")),
        "preflight_error": preflight.get("error"),
        "actor_pubkey": actor_pubkey,
        "nonce_before": int(nonce_before),
        "nonce_after": int(nonce_after),
        "tx_sequence_number": int(tx_sequence_number),
        "tx_fee_limit": str(int(tx_fee_limit)),
        "signing_mode": signing_mode,
        "tau_tx_payload_hash": tau_tx_hash,
        "zk_proof_verified": False,
        "proof_verifier": None,
    }
    return {
        "schema": _ZUSD_PROOF_INTENT_SCHEMA,
        "profile_id": _ZUSD_PROOF_PROFILE_ID,
        "body": body,
        "receipt_hash": _hash_payload(_ZUSD_PROOF_INTENT_HASH_DOMAIN, body),
    }


def _bind_live_zk_wrapper(
    payload: dict[str, Any],
    *,
    body: Mapping[str, Any],
    required: bool,
) -> dict[str, Any]:
    proof_section = payload.get("proof")
    if not isinstance(proof_section, dict):
        return payload
    receipt = proof_section.get("intent_receipt")
    if not isinstance(receipt, Mapping):
        return payload
    zk_wrapper = verify_live_proof_wrapper(
        surface="zusd_stream11",
        env_prefix=_ZUSD_ZK_PROOF_ENV_PREFIX,
        proof_intent_receipt=receipt,
        proof=proof_from_request(body),
        required=required,
    )
    require_live_proof_wrapper(zk_wrapper)
    proof_section["zk_wrapper"] = zk_wrapper
    profile = proof_section.get("profile")
    if isinstance(profile, dict):
        profile["zk_proof_verified"] = bool(zk_wrapper.get("zk_proof_verified"))
        profile["artifact_binding_complete"] = bool(zk_wrapper.get("artifact_binding_complete"))
        profile["promotion_ready"] = bool(zk_wrapper.get("zk_proof_verified")) and bool(
            zk_wrapper.get("artifact_binding_complete")
        )
    return payload


def _tau_client() -> TauNetTcpClient:
    return TauNetTcpClient(
        TauNetTcpConfig(
            host=_env_str("ZUSD_MONETARY_WALLET_TAU_HOST", _env_str("ZUSD_TAU_WALLET_TAU_HOST", "127.0.0.1")),
            port=_env_int_alias(
                "ZUSD_MONETARY_WALLET_TAU_PORT",
                "ZUSD_TAU_WALLET_TAU_PORT",
                65432,
                lo=1,
                hi=65535,
            ),
            timeout_s=_env_float_alias(
                "ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S",
                "ZUSD_TAU_WALLET_TAU_TIMEOUT_S",
                3.0,
                lo=0.1,
                hi=60.0,
            ),
        )
    )


def _tau_chain_id() -> str:
    return _env_str("ZUSD_MONETARY_WALLET_CHAIN_ID", _env_str("TAU_DEX_CHAIN_ID", "tau-local"))


def _allow_signing() -> bool:
    return _env_bool_alias(
        "ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING",
        "ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING",
        False,
    )


def _auto_mine() -> bool:
    return _env_bool_alias(
        "ZUSD_MONETARY_WALLET_AUTO_MINE",
        "ZUSD_TAU_WALLET_AUTO_MINE",
        False,
    )


def _default_deadline() -> int:
    delta = _env_int("ZUSD_MONETARY_WALLET_DEFAULT_DEADLINE_S", 3600, lo=1, hi=86_400)
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


def _zusd_state_view(app_state: Mapping[str, Any]) -> ZUSDMonetaryState | None:
    raw = app_state.get("zusd_monetary")
    if raw is None:
        return None
    if not isinstance(raw, Mapping):
        raise TauNetRpcError("app_state.zusd_monetary must be an object")
    return zusd_monetary_state_from_obj(raw)


def _balances_for_asset(app_state: Mapping[str, Any], *, asset_id: str) -> Dict[str, int]:
    state_view = _dex_state_view(app_state)
    raw = state_view.get("balances") or []
    if not isinstance(raw, list):
        raise TauNetRpcError("app_state balances must be a list")
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


def _last_used_monetary_nonce(app_state: Mapping[str, Any], *, actor_pubkey: str) -> int:
    state_view = _dex_state_view(app_state)
    raw = state_view.get("nonces") or []
    if not isinstance(raw, list):
        raise TauNetRpcError("app_state.nonces must be a list")
    nonce_key = zusd_monetary_sender_nonce_key(actor_pubkey)
    last_nonce = 0
    for index, entry in enumerate(raw):
        if not isinstance(entry, Mapping):
            raise TauNetRpcError(f"app_state.nonces[{index}] must be an object")
        pubkey = entry.get("pubkey")
        if not isinstance(pubkey, str):
            raise TauNetRpcError(f"app_state.nonces[{index}].pubkey invalid")
        if pubkey.strip().lower() != nonce_key.strip().lower():
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


def _request_signed_tau_tx_payload(body: Mapping[str, Any]) -> Mapping[str, Any] | None:
    for name in ("signed_tau_tx_payload", "tau_tx_payload"):
        value = _request_mapping(body, name=name)
        if value is not None:
            return value
    return None


def _validate_external_tau_tx_payload(
    payload: Mapping[str, Any],
    *,
    actor_pubkey: str,
    tx_sequence_number: int,
    deadline: int,
    operations: Mapping[str, Any],
    tx_fee_limit: int,
) -> dict[str, Any]:
    sender_raw = payload.get("sender_pubkey")
    if not isinstance(sender_raw, str) or not sender_raw.strip():
        raise ValueError("signed_tau_tx_payload missing sender_pubkey")
    sender_prefixed = sender_raw if sender_raw.lower().startswith("0x") else "0x" + sender_raw
    sender_pubkey = _canonical_pubkey(sender_prefixed, name="signed_tau_tx_payload.sender_pubkey")
    if sender_pubkey.lower() != actor_pubkey.lower():
        raise ValueError("signed_tau_tx_payload sender mismatch")

    sequence_number = payload.get("sequence_number")
    if not isinstance(sequence_number, int) or isinstance(sequence_number, bool):
        raise ValueError("signed_tau_tx_payload bad sequence_number")
    if int(sequence_number) != int(tx_sequence_number):
        raise ValueError("signed_tau_tx_payload sequence mismatch")

    expiration_time = payload.get("expiration_time")
    if not isinstance(expiration_time, int) or isinstance(expiration_time, bool):
        raise ValueError("signed_tau_tx_payload bad expiration_time")
    if int(expiration_time) != int(deadline):
        raise ValueError("signed_tau_tx_payload expiration mismatch")

    if str(payload.get("fee_limit")) != str(tx_fee_limit):
        raise ValueError("signed_tau_tx_payload fee_limit mismatch")

    raw_operations = payload.get("operations")
    if not isinstance(raw_operations, Mapping):
        raise ValueError("signed_tau_tx_payload operations must be an object")
    if dict(raw_operations) != encode_tau_operations_for_wire(operations):
        raise ValueError("signed_tau_tx_payload operations mismatch")

    signature = payload.get("signature")
    if not isinstance(signature, str) or not signature.strip():
        raise ValueError("signed_tau_tx_payload missing signature")
    if not verify_tau_transaction_payload_signature(payload):
        raise ValueError("signed_tau_tx_payload signature invalid")
    return dict(payload)


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


def _request_amount_e8(body: Mapping[str, Any], *, required: bool) -> int | None:
    if "amount_e8" in body:
        value = body.get("amount_e8")
        if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
            raise ValueError("bad_amount_e8")
        return int(value)
    if "amount" in body:
        value = body.get("amount")
        if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
            raise ValueError("bad_amount")
        return int(value) * E8
    if required:
        raise ValueError("missing_amount")
    return None


def _actor_pubkey_for_action(body: Mapping[str, Any], *, action: str) -> str:
    candidates: list[object] = []
    if "sender_pubkey" in body:
        candidates.append(body.get("sender_pubkey"))
    if action in {"deposit_collateral", "withdraw_collateral", "mint_zusd", "repay_zusd"} and "owner_pubkey" in body:
        candidates.append(body.get("owner_pubkey"))
    if action in {"deposit_sp", "withdraw_sp", "redeem_zusd", "claim_sp_collateral"} and "account_pubkey" in body:
        candidates.append(body.get("account_pubkey"))
    if action in {"advance_epoch", "bootstrap_oracle", "oracle_report", "oracle_commit", "liquidate"} and "actor_pubkey" in body:
        candidates.append(body.get("actor_pubkey"))
    if not candidates:
        raise ValueError("missing_sender_pubkey")
    canonical = [_canonical_pubkey(v, name="sender_pubkey") for v in candidates]
    first = canonical[0]
    if any(v != first for v in canonical):
        raise ValueError("sender_pubkey mismatch")
    return first


def _build_operation(body: Mapping[str, Any], *, action: str, actor_pubkey: str, nonce: int, deadline: int) -> dict[str, Any]:
    op: dict[str, Any] = {
        "module": "ZUSDFinance",
        "version": "0.1",
        "action": action,
        "nonce": int(nonce),
        "deadline": int(deadline),
    }
    if action == "advance_epoch":
        op["delta"] = _request_u32(body, name="delta", default=None)
        return op
    if action in {"bootstrap_oracle", "oracle_report"}:
        price_e8 = body.get("price_e8")
        if not isinstance(price_e8, int) or isinstance(price_e8, bool) or price_e8 <= 0:
            raise ValueError("bad_price_e8")
        op["price_e8"] = int(price_e8)
        return op
    if action == "oracle_commit" or action == "liquidate":
        return op
    if action in {"deposit_collateral", "withdraw_collateral", "mint_zusd", "repay_zusd"}:
        op["owner_pubkey"] = actor_pubkey
        op["amount_e8"] = _request_amount_e8(body, required=True)
        return op
    if action in {"deposit_sp", "withdraw_sp", "redeem_zusd", "claim_sp_collateral"}:
        op["account_pubkey"] = actor_pubkey
        op["amount_e8"] = _request_amount_e8(body, required=True)
        return op
    raise ValueError("unsupported_action")


def _state_from_app_state(app_state: Mapping[str, Any], *, actor_pubkey: str, native_balance: int | None) -> DexState:
    state = state_from_snapshot(_dex_state_view(app_state))
    if native_balance is None:
        return state
    balances = BalanceTable()
    for (pubkey, asset), amount in state.balances.get_all_balances().items():
        balances.set(pubkey, asset, int(amount))
    balances.set(actor_pubkey, NATIVE_ASSET, int(native_balance))
    return replace(state, balances=balances)


def _safe_native_balance(client: TauNetTcpClient, actor_pubkey: str) -> int | None:
    try:
        return int(client.get_balance(_pubkey_for_rpc(actor_pubkey)))
    except Exception:
        return None


def _preflight(
    *,
    app_state: Mapping[str, Any],
    config: ZUSDMonetaryConfig,
    operation: Mapping[str, Any],
    actor_pubkey: str,
    block_timestamp: int,
    native_balance: int | None,
) -> dict[str, Any]:
    try:
        state = _state_from_app_state(app_state, actor_pubkey=actor_pubkey, native_balance=native_balance)
        res = apply_zusd_monetary_ops(
            config=config,
            state=state,
            zusd_state=_zusd_state_view(app_state),
            operations=[dict(operation)],
            tx_sender_pubkey=actor_pubkey,
            block_timestamp=int(block_timestamp),
        )
        return {
            "ok": bool(res.ok),
            "error": res.error,
            "effects": list(res.effects or []),
        }
    except Exception as exc:
        return {"ok": False, "error": str(exc), "effects": []}


def _build_prepare_response(
    body: Mapping[str, Any],
    *,
    for_submit: bool,
    bind_zk: bool = True,
    enforce_oracle_authorization: bool = True,
) -> Dict[str, Any]:
    action = _request_action(body)
    actor_pubkey = _actor_pubkey_for_action(body, action=action)
    deadline = _request_u32(body, name="deadline", default=_default_deadline())
    chain_id = str(body.get("chain_id") or _tau_chain_id())
    explicit_asset_id = body.get("asset_id")
    asset_id = (
        _canonical_asset(explicit_asset_id, name="asset_id")
        if isinstance(explicit_asset_id, str) and explicit_asset_id.strip()
        else derive_zusd_tau_asset_id(chain_id=chain_id)
    )
    config = ZUSDMonetaryConfig(
        chain_id=chain_id,
        oracle_pubkey=os.environ.get("TAU_DEX_ZUSD_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY"),
        asset_id=asset_id,
        liquidation_gas_comp_fixed_collateral_e8=_env_int_alias(
            "TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_FIXED_COLLATERAL_E8",
            "TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_FIXED_COLLATERAL_E8",
            0,
            lo=0,
            hi=10**30,
        ),
        liquidation_gas_comp_bps=_env_int_alias(
            "TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_BPS",
            "TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_BPS",
            0,
            lo=0,
            hi=10_000,
        ),
        require_oracle_authorization=_oracle_authorization_required(),
    )

    client = _tau_client()
    app_state, app_hash = _load_app_state(client)
    balances = _balances_for_asset(app_state, asset_id=asset_id)
    sp_pubkey = stability_pool_pubkey(chain_id=chain_id)
    last_used_nonce = _last_used_monetary_nonce(app_state, actor_pubkey=actor_pubkey)
    nonce = last_used_nonce + 1
    tx_sequence_number = int(client.get_sequence(_pubkey_for_rpc(actor_pubkey)))
    native_balance = _safe_native_balance(client, actor_pubkey)
    tx_fee_limit = _request_tx_fee_limit(body)
    fee_limit_posture = _fee_limit_posture(tx_fee_limit=tx_fee_limit, native_balance=native_balance)
    operation = _build_operation(body, action=action, actor_pubkey=actor_pubkey, nonce=nonce, deadline=deadline)
    operations = {_STREAM_KEY: [operation]}
    zusd_runtime_state = _zusd_state_for_runtime(app_state, config=config)
    oracle_runtime = _oracle_runtime_facts(
        zusd_state=zusd_runtime_state,
        action=action,
        operation=operation,
    )
    oracle_error, oracle_report = _check_oracle_authorization(
        body=body,
        runtime=oracle_runtime,
        enforce=enforce_oracle_authorization,
    )
    if oracle_error is not None:
        raise ValueError(oracle_error)
    auth_obj = body.get("oracle_authorization")
    if oracle_runtime is not None and isinstance(auth_obj, Mapping):
        operation["oracle_authorization"] = dict(auth_obj)
    block_timestamp = int(body.get("block_timestamp") if isinstance(body.get("block_timestamp"), int) else int(time.time()))
    preflight = _preflight(
        app_state=app_state,
        config=config,
        operation=operation,
        actor_pubkey=actor_pubkey,
        block_timestamp=block_timestamp,
        native_balance=native_balance,
    )
    if for_submit and not preflight.get("ok"):
        raise ValueError(f"preflight_failed: {preflight.get('error') or 'unknown'}")

    tau_tx_payload: dict[str, Any] | None = None
    signing_mode = "prepare_only"
    signer_privkey = body.get("signer_privkey")
    external_payload = _request_signed_tau_tx_payload(body) if for_submit else None
    if external_payload is not None:
        tau_tx_payload = _validate_external_tau_tx_payload(
            external_payload,
            actor_pubkey=actor_pubkey,
            tx_sequence_number=tx_sequence_number,
            deadline=deadline,
            operations=operations,
            tx_fee_limit=tx_fee_limit,
        )
        signing_mode = "external_signed_payload"
    elif for_submit or signer_privkey is not None:
        if not isinstance(signer_privkey, (str, int)):
            raise ValueError("missing_signer_privkey")
        if not _allow_signing():
            raise ValueError("local_signing_disabled")
        signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(cast(Any, signer_privkey))
        if signer_pubkey.lower() != actor_pubkey.lower():
            raise ValueError("signer_privkey does not match sender_pubkey")
        tau_tx_payload = build_signed_tau_transaction(
            privkey=cast(Any, signer_privkey),
            sequence_number=tx_sequence_number,
            expiration_time=deadline,
            operations=operations,
            fee_limit=tx_fee_limit,
        )
        signing_mode = "local_test_signing"

    payload: Dict[str, Any] = {
        "ok": True,
        "transport": {
            "chain_id": chain_id,
            "app_hash": app_hash,
            "asset_id": asset_id,
            "actor_pubkey": actor_pubkey,
            "native_balance_e8": native_balance,
            "tx_fee_limit": str(tx_fee_limit),
            "fee_limit_native_balance_ok": fee_limit_posture["native_balance_covers_fee_limit"],
            "fee_limit_warning": fee_limit_posture["warning"],
            "zusd_balance": int(balances.get(actor_pubkey.lower(), 0)),
            "stability_pool_pubkey": sp_pubkey,
            "stability_pool_balance": int(balances.get(sp_pubkey.lower(), 0)),
            "last_used_nonce": last_used_nonce,
            "tx_sequence_number": tx_sequence_number,
            "stream_key": _STREAM_KEY,
            "liquidation_gas_comp_fixed_collateral_e8": config.liquidation_gas_comp_fixed_collateral_e8,
            "liquidation_gas_comp_bps": config.liquidation_gas_comp_bps,
            "allow_local_signing": _allow_signing(),
            "signing_mode": signing_mode,
            "auto_mine": _auto_mine(),
            "tau_host": _env_str("ZUSD_MONETARY_WALLET_TAU_HOST", _env_str("ZUSD_TAU_WALLET_TAU_HOST", "127.0.0.1")),
            "tau_port": _env_int_alias(
                "ZUSD_MONETARY_WALLET_TAU_PORT",
                "ZUSD_TAU_WALLET_TAU_PORT",
                65432,
                lo=1,
                hi=65535,
            ),
        },
        "report": {
            "action": action,
            "asset_id": asset_id,
            "nonce_key": zusd_monetary_sender_nonce_key(actor_pubkey),
            "nonce_before": last_used_nonce,
            "nonce_after": nonce,
            "operation": operation,
            "operations": operations,
            "preflight": preflight,
            "fee_limit": fee_limit_posture,
            "tau_tx_payload": tau_tx_payload,
        },
        "oracle_runtime": oracle_report,
        "proof": {
            "profile": _zusd_proof_profile(),
            "intent_receipt": _zusd_proof_intent_receipt(
                chain_id=chain_id,
                action=action,
                asset_id=asset_id,
                operation=operation,
                operations=operations,
                app_hash_before=app_hash,
                app_hash_after=None,
                preflight=preflight,
                actor_pubkey=actor_pubkey,
                nonce_before=last_used_nonce,
                nonce_after=nonce,
                tx_sequence_number=tx_sequence_number,
                tx_fee_limit=tx_fee_limit,
                signing_mode=signing_mode,
                tau_tx_payload=tau_tx_payload,
            ),
        },
    }
    if bind_zk:
        zk_required = live_zk_proof_required(env_prefix=_ZUSD_ZK_PROOF_ENV_PREFIX)
        payload = _bind_live_zk_wrapper(payload, body=body, required=zk_required)
    if for_submit:
        send_resp = client.sendtx(cast(Mapping[str, Any], tau_tx_payload))
        payload["submission"] = {"sendtx_response": send_resp}
        if _auto_mine():
            payload["submission"]["createblock_response"] = client.createblock()
        app_state_after, app_hash_after = _load_app_state(client)
        payload["post_submit"] = {
            "app_hash": app_hash_after,
            "balances": _balances_for_asset(app_state_after, asset_id=asset_id),
            "zusd_monetary": app_state_after.get("zusd_monetary"),
        }
        payload["proof"]["intent_receipt"] = _zusd_proof_intent_receipt(
            chain_id=chain_id,
            action=action,
            asset_id=asset_id,
            operation=operation,
            operations=operations,
            app_hash_before=app_hash,
            app_hash_after=app_hash_after,
            preflight=preflight,
            actor_pubkey=actor_pubkey,
            nonce_before=last_used_nonce,
            nonce_after=nonce,
            tx_sequence_number=tx_sequence_number,
            tx_fee_limit=tx_fee_limit,
            signing_mode=signing_mode,
            tau_tx_payload=tau_tx_payload,
        )
        if bind_zk:
            payload = _bind_live_zk_wrapper(payload, body=body, required=False)
    return payload


def _status_payload() -> Dict[str, Any]:
    chain_id = _tau_chain_id()
    asset_id = derive_zusd_tau_asset_id(chain_id=chain_id)
    sp_pubkey = stability_pool_pubkey(chain_id=chain_id)
    liquidation_fee_comp_fixed_collateral_e8 = _env_int_alias(
        "TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_FIXED_COLLATERAL_E8",
        "TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_FIXED_COLLATERAL_E8",
        0,
        lo=0,
        hi=10**30,
    )
    liquidation_fee_comp_bps = _env_int_alias(
        "TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_BPS",
        "TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_BPS",
        0,
        lo=0,
        hi=10_000,
    )
    status: Dict[str, Any] = {
        "enabled": True,
        "chain_id": chain_id,
        "asset_id": asset_id,
        "tau_host": _env_str("ZUSD_MONETARY_WALLET_TAU_HOST", _env_str("ZUSD_TAU_WALLET_TAU_HOST", "127.0.0.1")),
        "tau_port": _env_int_alias(
            "ZUSD_MONETARY_WALLET_TAU_PORT",
            "ZUSD_TAU_WALLET_TAU_PORT",
            65432,
            lo=1,
            hi=65535,
        ),
        "allow_local_signing": _allow_signing(),
        "auto_mine": _auto_mine(),
        "stability_pool_pubkey": sp_pubkey,
        "oracle_pubkey": os.environ.get("TAU_DEX_ZUSD_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY") or None,
        "liquidation_fee_comp_fixed_collateral_e8": liquidation_fee_comp_fixed_collateral_e8,
        "liquidation_fee_comp_bps": liquidation_fee_comp_bps,
        "liquidation_gas_comp_fixed_collateral_e8": liquidation_fee_comp_fixed_collateral_e8,
        "liquidation_gas_comp_bps": liquidation_fee_comp_bps,
        "proof_profile": _zusd_proof_profile(),
        "oracle_consumer": {
            "authorization_required": _oracle_authorization_required(),
            "consumer_module": "zenodex.zusd",
            "query_id": _ORACLE_ZUSD_COLLATERAL_QUERY_ID,
            "required_evidence_floor": "O3",
            "critical_actions": sorted(_ZUSD_ORACLE_AUTH_ACTIONS),
            "profile_ids": dict(_ZUSD_ORACLE_CONSUMER_PROFILE_IDS),
        },
    }
    try:
        client = _tau_client()
        hello = client.rpc("hello version=1").strip()
        app_state, app_hash = _load_app_state(client)
        balances = _balances_for_asset(app_state, asset_id=asset_id)
        zusd_state = _zusd_state_view(app_state)
        status["node_reachable"] = True
        status["hello"] = hello
        status["app_hash"] = app_hash
        status["app_bridge_available"] = bool(app_state or app_hash)
        status["holder_count"] = len(balances)
        status["stability_pool_balance"] = int(balances.get(sp_pubkey.lower(), 0))
        status["monetary_state_present"] = zusd_state is not None
        if zusd_state is not None:
            status["core"] = dict(zusd_state.core.__dict__)
            status["vault_owner_pubkey"] = zusd_state.vault_owner_pubkey
            status["sp_deposits_e8"] = dict(zusd_state.sp_deposits_e8 or {})
            status["sp_collateral_claims_e8"] = dict(zusd_state.sp_collateral_claims_e8 or {})
    except Exception as exc:
        status["node_reachable"] = False
        status["error"] = f"{type(exc).__name__}: {exc}"
    return status


def handle_zusd_monetary_wallet_request(method: str, path: str, body: Optional[bytes]) -> ResponseT:
    parsed_path = urlsplit(path)
    segments = [segment for segment in parsed_path.path.split("/") if segment]
    if len(segments) < 4 or segments[0] != "api" or segments[1] != "zusd" or segments[2] != "monetary":
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
        if rest == ["oracle-runtime"]:
            return 200, _build_prepare_response(
                parsed,
                for_submit=False,
                bind_zk=False,
                enforce_oracle_authorization=False,
            )
        if rest == ["submit"]:
            return 200, _build_prepare_response(parsed, for_submit=True)
        return 404, {"ok": False, "error": "not_found"}
    except (ValueError, TypeError) as exc:
        return 400, {"ok": False, "error": str(exc)}
    except TauNetRpcError as exc:
        return 502, {"ok": False, "error": "tau_rpc_error", "detail": str(exc)}
    except Exception as exc:
        return 500, {"ok": False, "error": "internal_error", "detail": f"{type(exc).__name__}: {exc}"}
