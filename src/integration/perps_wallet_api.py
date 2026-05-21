"""Tau-node-backed perps wallet API.

This module exposes a mounted live surface for stream-8 clearinghouse perps
operations. It intentionally sits beside ``perps_api.py`` because that module
is a demo/development API and does not verify caller authority.
"""

from __future__ import annotations

import json
import os
import time
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Tuple, cast
from urllib.parse import urlsplit

from ..core.dex import DexState
from ..core.perps import PerpClearinghouse2pMarketState, PerpMarketState
from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes, sha256_hex
from .dex_snapshot import state_from_snapshot
from .live_proof_wrapper import (
    live_zk_proof_required,
    proof_from_request,
    require_live_proof_wrapper,
    verify_live_proof_wrapper,
)
from .perp_engine import PerpEngineConfig, apply_perp_ops
from .perps_wallet_authority import (
    evaluate_perps_wallet_authority_profile_v1,
    evaluate_perps_wallet_recovery_exercise_v1,
)
from .tau_net_client import (
    TauNetRpcError,
    TauNetTcpClient,
    TauNetTcpConfig,
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
    encode_tau_operations_for_wire,
    sign_perp_op_for_engine,
    verify_tau_transaction_payload_signature,
)
from .zeno_oracle_authority import evaluate_oracle_authority_profile_v1
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
_PERPS_PROOF_PROFILE_ID = "perps_stream8_live_wallet_v0"
_PERPS_PROOF_PROFILE_SCHEMA = "zenodex/perps_wallet/proof_profile/v1"
_PERPS_PROOF_INTENT_SCHEMA = "zenodex/perps_wallet/proof_intent_receipt/v1"
_PERPS_PROOF_INTENT_HASH_DOMAIN = "zenodex.perps_wallet.proof_intent_receipt/v1"
_PERPS_ZK_PROOF_ENV_PREFIX = "PERPS_WALLET"
_PERPS_ZK_PROOF_REQUIRED_ENV = "PERPS_WALLET_REQUIRE_ZK_PROOF"
_ORACLE_AUTHORITY_EXERCISE_SCHEMA = "zenodex/perps_wallet/oracle_authority_exercise/v1"
_ORACLE_AUTHORITY_EXERCISE_HASH_DOMAIN = "zenodex.perps_wallet.oracle_authority_exercise/v1"
_ORACLE_AUTHORITY_ACTIONS = {"settle_epoch", "partial_liquidate"}


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


def _wallet_authority_profile_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    raw = _env_str("PERPS_WALLET_AUTHORITY_PROFILE_JSON", "")
    if raw:
        try:
            obj = json.loads(raw)
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            return None, f"perps wallet authority profile JSON invalid: {exc}"
        if not isinstance(obj, Mapping):
            return None, "perps wallet authority profile JSON must be an object"
        return obj, None

    path_raw = _env_str("PERPS_WALLET_AUTHORITY_PROFILE_FILE", "")
    if path_raw:
        try:
            obj = json.loads(Path(path_raw).read_text(encoding="utf-8"))
        except Exception as exc:
            return None, f"perps wallet authority profile file invalid: {exc}"
        if not isinstance(obj, Mapping):
            return None, "perps wallet authority profile file must contain an object"
        return obj, None

    return None, None


def _wallet_recovery_exercise_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=("PERPS_WALLET_RECOVERY_EXERCISE_JSON",),
        file_names=("PERPS_WALLET_RECOVERY_EXERCISE_FILE",),
        label="perps wallet recovery exercise",
    )


def _json_profile_from_env(
    *,
    json_names: tuple[str, ...],
    file_names: tuple[str, ...],
    label: str,
) -> tuple[Mapping[str, Any] | None, str | None]:
    for name in json_names:
        raw = _env_str(name, "")
        if not raw:
            continue
        try:
            obj = json.loads(raw)
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            return None, f"{label} JSON invalid from {name}: {exc}"
        if not isinstance(obj, Mapping):
            return None, f"{label} JSON from {name} must be an object"
        return obj, None

    for name in file_names:
        path_raw = _env_str(name, "")
        if not path_raw:
            continue
        try:
            obj = json.loads(Path(path_raw).read_text(encoding="utf-8"))
        except Exception as exc:
            return None, f"{label} file invalid from {name}: {exc}"
        if not isinstance(obj, Mapping):
            return None, f"{label} file from {name} must contain an object"
        return obj, None

    return None, None


def _oracle_authority_profile_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=(
            "PERPS_ORACLE_AUTHORITY_PROFILE_JSON",
            "ZENO_ORACLE_AUTHORITY_PROFILE_JSON",
        ),
        file_names=(
            "PERPS_ORACLE_AUTHORITY_PROFILE_FILE",
            "ZENO_ORACLE_AUTHORITY_PROFILE_FILE",
            "ZENO_ORACLE_PRODUCTION_AUTHORITY_PROFILE_FILE",
        ),
        label="oracle production authority profile",
    )


def _bind_oracle_authority_status(
    status: dict[str, Any],
    *,
    profile: Mapping[str, Any] | None,
    profile_error: str | None,
    expected_chain_id: str,
) -> dict[str, Any]:
    if profile_error is not None:
        status["ok"] = False
        status["production_authority"] = False
        status["status"] = "blocked"
        status.setdefault("readiness_gaps", []).append(profile_error)

    if profile is not None and profile.get("chain_id") != expected_chain_id:
        status["ok"] = False
        status["production_authority"] = False
        status["status"] = "blocked"
        status.setdefault("readiness_gaps", []).append("oracle production authority profile chain_id mismatch")
    return status


def _require_production_oracle_authority_for_action(action: str) -> bool:
    if action not in _ORACLE_AUTHORITY_ACTIONS:
        return False
    return _env_bool("PERPS_WALLET_REQUIRE_PRODUCTION_ORACLE_AUTHORITY", False)


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


def _hash_payload(domain: str, payload: Mapping[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(domain) + canonical_json_bytes(dict(payload)))


def _perps_proof_profile() -> dict[str, Any]:
    return {
        "schema": _PERPS_PROOF_PROFILE_SCHEMA,
        "profile_id": _PERPS_PROOF_PROFILE_ID,
        "claim_scope": "deterministic_stream8_live_wallet_receipt",
        "covered": [
            "stream8_operation_hash_binding",
            "pre_app_hash_binding",
            "tau_envelope_signature_binding",
            "engine_preflight_replay",
            "post_submit_app_hash_binding_when_available",
            "public_state_delta_witness_binding",
            "oracle_authority_quorum_binding_when_exercised",
        ],
        "not_covered": [
            "risc0_zkvm_wrapper",
            "production_oracle_truth",
            "production_finality",
            "hardware_wallet_key_custody",
            "stream11_zusd_zk_wrapper",
        ],
        "non_claims": [
            "does_not_claim_perps_zk_execution",
            "does_not_claim_oracle_truth_or_governance",
            "does_not_claim_production_finality",
            "does_not_claim_wallet_key_custody",
        ],
        "zk_proof_verified": False,
        "zk_wrapper_required_for_production_claim": True,
        "promotion_ready": False,
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
        surface="perps_stream8",
        env_prefix=_PERPS_ZK_PROOF_ENV_PREFIX,
        proof_intent_receipt=receipt,
        proof=proof_from_request(body),
        required=required,
    )
    require_live_proof_wrapper(zk_wrapper)
    proof_section["zk_wrapper"] = zk_wrapper
    profile = proof_section.get("profile")
    if isinstance(profile, dict):
        profile["zk_proof_verified"] = bool(zk_wrapper.get("zk_proof_verified"))
        profile["promotion_ready"] = bool(zk_wrapper.get("zk_proof_verified"))
    return payload


def _perps_proof_intent_receipt(
    *,
    chain_id: str,
    action: str,
    operation: Mapping[str, Any],
    operations: Mapping[str, Any],
    app_hash_before: str | None,
    app_hash_after: str | None,
    preflight: Mapping[str, Any],
    tx_sender_pubkey: str,
    tx_sequence_number: int,
    tx_fee_limit: int,
    signing_mode: str,
    tau_tx_payload: Mapping[str, Any] | None,
    state_delta_witness: Mapping[str, Any] | None = None,
    oracle_authority_exercise: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    tau_tx_hash = None
    if tau_tx_payload is not None:
        tau_tx_hash = _hash_payload("zenodex.perps_wallet.tau_tx_payload/v1", tau_tx_payload)
    oracle_authority_exercise_hash = None
    oracle_authority_exercised = False
    if oracle_authority_exercise is not None:
        oracle_authority_exercise_hash = str(oracle_authority_exercise.get("exercise_hash") or "")
        oracle_authority_exercised = bool(oracle_authority_exercise.get("authority_exercised"))
    body: dict[str, Any] = {
        "schema": _PERPS_PROOF_INTENT_SCHEMA,
        "profile_id": _PERPS_PROOF_PROFILE_ID,
        "chain_id": str(chain_id),
        "stream_key": _STREAM_KEY,
        "engine_stream_key": _ENGINE_STREAM_KEY,
        "action": str(action),
        "market_id": operation.get("market_id"),
        "app_hash_before": app_hash_before,
        "app_hash_after": app_hash_after,
        "operation_hash": _hash_payload("zenodex.perps_wallet.operation/v1", operation),
        "operations_hash": _hash_payload("zenodex.perps_wallet.operations/v1", operations),
        "preflight_ok": bool(preflight.get("ok")),
        "preflight_error": preflight.get("error"),
        "tx_sender_pubkey": tx_sender_pubkey,
        "tx_sequence_number": int(tx_sequence_number),
        "tx_fee_limit": str(int(tx_fee_limit)),
        "signing_mode": str(signing_mode),
        "tau_tx_payload_hash": tau_tx_hash,
        "oracle_authority_exercised": oracle_authority_exercised,
        "oracle_authority_exercise_hash": oracle_authority_exercise_hash or None,
        "state_delta_witness_hash": (
            None
            if state_delta_witness is None
            else _hash_payload("zenodex.perps_wallet.state_delta_witness/v1", state_delta_witness)
        ),
        "zk_proof_verified": False,
        "proof_verifier": None,
    }
    return {
        "schema": _PERPS_PROOF_INTENT_SCHEMA,
        "profile_id": _PERPS_PROOF_PROFILE_ID,
        "body": body,
        "oracle_authority_exercise": None if oracle_authority_exercise is None else dict(oracle_authority_exercise),
        "state_delta_witness": None if state_delta_witness is None else dict(state_delta_witness),
        "receipt_hash": _hash_payload(_PERPS_PROOF_INTENT_HASH_DOMAIN, body),
    }


def _oracle_authority_exercise_for_action(
    *,
    action: str,
    chain_id: str,
    operation: Mapping[str, Any],
) -> dict[str, Any] | None:
    if action not in _ORACLE_AUTHORITY_ACTIONS:
        return None

    oracle_authority_profile, oracle_authority_error = _oracle_authority_profile_from_env()
    oracle_authority = _bind_oracle_authority_status(
        evaluate_oracle_authority_profile_v1(oracle_authority_profile),
        profile=oracle_authority_profile,
        profile_error=oracle_authority_error,
        expected_chain_id=chain_id,
    )
    bridge = operation.get("oracle_adapter_bridge")
    bridge_present = isinstance(bridge, Mapping)
    readiness_gaps = list(oracle_authority.get("readiness_gaps") or [])
    if not bridge_present:
        readiness_gaps.append("oracle adapter bridge is missing from operation")

    signature_quorum = oracle_authority.get("signature_quorum")
    if not isinstance(signature_quorum, Mapping):
        signature_quorum = {}
    authority_ready = bool(oracle_authority.get("production_authority"))
    authority_exercised = bool(authority_ready and bridge_present)
    body: dict[str, Any] = {
        "schema": _ORACLE_AUTHORITY_EXERCISE_SCHEMA,
        "action": action,
        "chain_id": chain_id,
        "market_id": operation.get("market_id"),
        "required_for_action": _require_production_oracle_authority_for_action(action),
        "authority_exercised": authority_exercised,
        "production_authority": authority_ready,
        "status": "exercised" if authority_exercised else "blocked",
        "readiness_gaps": readiness_gaps,
        "authority_id": oracle_authority.get("authority_id"),
        "authority_hash": oracle_authority.get("authority_hash"),
        "expected_authority_hash": oracle_authority.get("expected_authority_hash"),
        "signer_registry_hash": oracle_authority.get("signer_registry_hash"),
        "key_manager_hash": oracle_authority.get("key_manager_hash"),
        "active_signer_count": int(oracle_authority.get("active_signer_count") or 0),
        "threshold": int(oracle_authority.get("threshold") or 0),
        "signature_count": int(oracle_authority.get("signature_count") or 0),
        "signature_quorum_report_hash": signature_quorum.get("quorum_report_hash"),
        "signature_quorum_accepted_weight": int(signature_quorum.get("accepted_weight") or 0),
        "signature_quorum_threshold": int(signature_quorum.get("threshold") or 0),
        "oracle_adapter_bridge_present": bridge_present,
        "oracle_adapter_bridge_id": bridge.get("bridge_id") if isinstance(bridge, Mapping) else None,
        "oracle_adapter_bridge_hash": (
            _hash_payload("zenodex.perps_wallet.oracle_adapter_bridge/v1", bridge)
            if isinstance(bridge, Mapping)
            else None
        ),
    }
    return {
        **body,
        "exercise_hash": _hash_payload(_ORACLE_AUTHORITY_EXERCISE_HASH_DOMAIN, body),
    }


def _perps_state_delta_witness(
    *,
    chain_id: str,
    action: str,
    app_hash_before: str | None,
    app_hash_after: str | None,
    app_state_before: Mapping[str, Any],
    app_state_after: Mapping[str, Any],
) -> dict[str, Any]:
    before_markets = _market_summaries(app_state_before)
    after_markets = _market_summaries(app_state_after)
    before_by_id = {str(item.get("market_id")): item for item in before_markets}
    after_by_id = {str(item.get("market_id")): item for item in after_markets}
    changed_markets: list[dict[str, Any]] = []
    numeric_fields = (
        "account_a_quote_balance",
        "account_b_quote_balance",
        "collateral_e8_a",
        "collateral_e8_b",
        "fee_pool_e8",
        "net_deposited_e8",
        "position_base_a",
        "position_base_b",
        "index_price_e8",
        "clearing_price_e8",
        "now_epoch",
        "oracle_last_update_epoch",
        "fee_pool_quote",
        "insurance_balance",
    )
    for market_id in sorted(set(before_by_id) | set(after_by_id)):
        before = before_by_id.get(market_id, {})
        after = after_by_id.get(market_id, {})
        deltas: dict[str, int] = {}
        for field in numeric_fields:
            before_value = before.get(field, 0)
            after_value = after.get(field, 0)
            if isinstance(before_value, int) and isinstance(after_value, int):
                delta = int(after_value) - int(before_value)
                if delta:
                    deltas[field] = delta
        account_deltas: list[dict[str, Any]] = []
        before_accounts_raw = before.get("accounts")
        if isinstance(before_accounts_raw, list):
            before_accounts = {
                str(account.get("account_pubkey")): account
                for account in before_accounts_raw
                if isinstance(account, Mapping)
            }
        else:
            before_accounts = {}
        after_accounts_raw = after.get("accounts")
        if isinstance(after_accounts_raw, list):
            after_accounts = {
                str(account.get("account_pubkey")): account
                for account in after_accounts_raw
                if isinstance(account, Mapping)
            }
        else:
            after_accounts = {}
        for account_pubkey in sorted(set(before_accounts) | set(after_accounts)):
            before_account = before_accounts.get(account_pubkey, {})
            after_account = after_accounts.get(account_pubkey, {})
            account_delta: dict[str, Any] = {"account_pubkey": account_pubkey}
            for field in ("position_base", "collateral_quote"):
                before_value = before_account.get(field, 0)
                after_value = after_account.get(field, 0)
                if isinstance(before_value, int) and isinstance(after_value, int):
                    delta = int(after_value) - int(before_value)
                    if delta:
                        account_delta[f"{field}_delta"] = delta
            liquidation_changed = before_account.get("liquidated_this_step") != after_account.get("liquidated_this_step")
            if len(account_delta) > 1 or liquidation_changed:
                account_delta["liquidated_before"] = bool(before_account.get("liquidated_this_step", False))
                account_delta["liquidated_after"] = bool(after_account.get("liquidated_this_step", False))
                account_deltas.append(account_delta)
        market_liquidation_changed = before.get("liquidated_this_step") != after.get("liquidated_this_step")
        if deltas or account_deltas or not before or not after or market_liquidation_changed:
            changed_markets.append(
                {
                    "market_id": market_id,
                    "kind_before": before.get("kind"),
                    "kind_after": after.get("kind"),
                    "deltas": deltas,
                    "account_deltas": account_deltas,
                    "liquidated_before": bool(before.get("liquidated_this_step", False)),
                    "liquidated_after": bool(after.get("liquidated_this_step", False)),
                }
            )
    return {
        "schema": "zenodex/perps_wallet/state_delta_witness/v1",
        "chain_id": str(chain_id),
        "stream_key": _STREAM_KEY,
        "action": str(action),
        "app_hash_before": app_hash_before,
        "app_hash_after": app_hash_after,
        "market_count_before": len(before_markets),
        "market_count_after": len(after_markets),
        "changed_markets": changed_markets,
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


def _request_signed_tau_tx_payload(body: Mapping[str, Any]) -> Mapping[str, Any] | None:
    for name in ("signed_tau_tx_payload", "tau_tx_payload"):
        value = _request_mapping(body, name=name)
        if value is not None:
            return value
    return None


def _validate_external_tau_tx_payload(
    payload: Mapping[str, Any],
    *,
    tx_sender_pubkey: str,
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
    if sender_pubkey.lower() != tx_sender_pubkey.lower():
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


def _oracle_adapter_bridge_from_body(body: Mapping[str, Any]) -> Mapping[str, Any]:
    bridge = _request_mapping(body, name="oracle_adapter_bridge")
    if bridge is None:
        bridge = _request_mapping(body, name="bridge")
    if bridge is None and str(body.get("schema", "")).strip() == "zenodex.oracle.aggregate_adapter_bridge.v1":
        bridge = body
    if bridge is None:
        raise ValueError("missing_oracle_adapter_bridge")
    return bridge


def _inspect_oracle_adapter_bridge(body: Mapping[str, Any]) -> dict[str, Any]:
    from tools.zenodex_oracle_aggregate_adapter import (  # pylint: disable=import-outside-toplevel
        verify_aggregate_adapter_bridge,
    )

    bridge = _oracle_adapter_bridge_from_body(body)
    verify_result = verify_aggregate_adapter_bridge(bridge).to_json_obj()
    aggregate_read = bridge.get("aggregate_read")
    if not isinstance(aggregate_read, Mapping):
        aggregate_read = {}
    aggregate = aggregate_read.get("aggregate")
    if not isinstance(aggregate, Mapping):
        aggregate = {}
    aggregate_value = aggregate.get("aggregate")
    if not isinstance(aggregate_value, Mapping):
        aggregate_value = {}
    action = bridge.get("action")
    if not isinstance(action, Mapping):
        action = {}
    profile = bridge.get("profile")
    if not isinstance(profile, Mapping):
        profile = {}
    receipt_bundle = aggregate_read.get("receipt_bundle")
    terminal = receipt_bundle.get("terminal") if isinstance(receipt_bundle, Mapping) else {}
    if not isinstance(terminal, Mapping):
        terminal = {}

    summary = {
        "bridge_id": bridge.get("bridge_id"),
        "consumer_module": action.get("consumer_module"),
        "action_kind": action.get("action_kind"),
        "action_id": action.get("action_id"),
        "action_epoch": action.get("action_epoch"),
        "query_id": action.get("query_id") or aggregate.get("query_id"),
        "profile_id": profile.get("profile_id"),
        "required_evidence_floor": action.get("required_evidence_floor") or profile.get("required_evidence_floor"),
        "max_freshness_window_epochs": action.get("max_freshness_window_epochs")
        or profile.get("max_freshness_window_epochs"),
        "read_receipt_id": action.get("read_receipt_id") or terminal.get("read_receipt_id"),
        "consumer_action_receipt_id": action.get("consumer_action_receipt_id")
        or terminal.get("consumer_action_receipt_id"),
        "aggregate_id": aggregate.get("aggregate_id"),
        "value_e8": aggregate_value.get("value_e8"),
        "confidence_e8": aggregate_value.get("confidence_e8"),
        "deviation_bps": aggregate_value.get("deviation_bps"),
        "observed_epoch": aggregate_value.get("observed_epoch"),
        "report_count": aggregate_value.get("report_count"),
        "evidence_class": aggregate.get("evidence_class") or aggregate.get("evidence_floor"),
        "production_authority": False,
    }
    return {
        "schema": "zenodex.perps_wallet.oracle_bridge_inspection.v1",
        "ok": verify_result.get("status") == "accepted",
        "status": verify_result.get("status"),
        "summary": summary,
        "verify_result": verify_result,
        "production_authority": False,
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
    oracle_authority_exercise = _oracle_authority_exercise_for_action(
        action=action,
        chain_id=chain_id,
        operation=operation,
    )
    if (
        oracle_authority_exercise is not None
        and oracle_authority_exercise.get("required_for_action") is True
        and oracle_authority_exercise.get("authority_exercised") is not True
    ):
        gaps = ", ".join(str(gap) for gap in oracle_authority_exercise.get("readiness_gaps", []))
        raise ValueError(f"production_oracle_authority_required: {gaps or 'authority not exercised'}")
    quote_asset = str(operation.get("quote_asset") or body.get("quote_asset") or body.get("quoteAsset") or "")
    if not quote_asset:
        quote_asset = _market_quote_asset(app_state, market_id=_market_id(body, action=action))
    account_pubkey = str(operation.get("account_pubkey") or meta.get("account_a_pubkey") or tx_sender_pubkey)
    quote_balance = _balance_for_asset(app_state, pubkey=account_pubkey, asset_id=quote_asset) if quote_asset else 0

    tau_tx_payload: dict[str, Any] | None = None
    signing_mode = "prepare_only"
    if for_submit:
        external_payload = _request_signed_tau_tx_payload(body)
        if external_payload is not None:
            tau_tx_payload = _validate_external_tau_tx_payload(
                external_payload,
                tx_sender_pubkey=tx_sender_pubkey,
                tx_sequence_number=tx_sequence_number,
                deadline=deadline,
                operations=operations,
                tx_fee_limit=tx_fee_limit,
            )
            signing_mode = "external_signed_payload"
        else:
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
            signing_mode = "local_test_signing"

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
            "signing_mode": signing_mode,
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
        "proof": {
            "profile": _perps_proof_profile(),
            "intent_receipt": _perps_proof_intent_receipt(
                chain_id=chain_id,
                action=action,
                operation=operation,
                operations=operations,
                app_hash_before=app_hash,
                app_hash_after=None,
                preflight=preflight,
                tx_sender_pubkey=tx_sender_pubkey,
                tx_sequence_number=tx_sequence_number,
                tx_fee_limit=tx_fee_limit,
                signing_mode=signing_mode,
                tau_tx_payload=tau_tx_payload,
                oracle_authority_exercise=oracle_authority_exercise,
                state_delta_witness=None,
            ),
            "oracle_authority_exercise": oracle_authority_exercise,
        },
    }
    zk_required = live_zk_proof_required(env_prefix=_PERPS_ZK_PROOF_ENV_PREFIX)
    payload = _bind_live_zk_wrapper(payload, body=body, required=zk_required)
    if for_submit:
        send_resp = client.sendtx(cast(Mapping[str, Any], tau_tx_payload))
        payload["submission"] = {"sendtx_response": send_resp}
        if _auto_mine():
            payload["submission"]["createblock_response"] = client.createblock()
        app_state_after, app_hash_after = _load_app_state(client)
        state_delta_witness = _perps_state_delta_witness(
            chain_id=chain_id,
            action=action,
            app_hash_before=app_hash,
            app_hash_after=app_hash_after,
            app_state_before=app_state,
            app_state_after=app_state_after,
        )
        payload["post_submit"] = {
            "app_hash": app_hash_after,
            "markets": _market_summaries(app_state_after),
            "state_delta_witness": state_delta_witness,
        }
        payload["proof"]["intent_receipt"] = _perps_proof_intent_receipt(
            chain_id=chain_id,
            action=action,
            operation=operation,
            operations=operations,
            app_hash_before=app_hash,
            app_hash_after=app_hash_after,
            preflight=preflight,
            tx_sender_pubkey=tx_sender_pubkey,
            tx_sequence_number=tx_sequence_number,
            tx_fee_limit=tx_fee_limit,
            signing_mode=signing_mode,
            tau_tx_payload=tau_tx_payload,
            oracle_authority_exercise=oracle_authority_exercise,
            state_delta_witness=state_delta_witness,
        )
        payload["proof"]["oracle_authority_exercise"] = oracle_authority_exercise
        payload = _bind_live_zk_wrapper(payload, body=body, required=False)
    return payload


def _status_payload() -> Dict[str, Any]:
    chain_id = _tau_chain_id()
    wallet_authority_profile, wallet_authority_error = _wallet_authority_profile_from_env()
    wallet_authority = evaluate_perps_wallet_authority_profile_v1(
        wallet_authority_profile,
        expected_chain_id=chain_id,
    )
    if wallet_authority_error is not None:
        wallet_authority["ok"] = False
        wallet_authority["production_wallet_authority"] = False
        wallet_authority["status"] = "blocked"
        wallet_authority.setdefault("readiness_gaps", []).append(wallet_authority_error)
    recovery_exercise, recovery_exercise_error = _wallet_recovery_exercise_from_env()
    if recovery_exercise is not None:
        wallet_authority["recovery_exercise"] = evaluate_perps_wallet_recovery_exercise_v1(
            wallet_authority_profile,
            recovery_exercise,
            expected_chain_id=chain_id,
        )
    elif recovery_exercise_error is not None:
        wallet_authority["recovery_exercise"] = {
            "schema": "zenodex/perps-wallet-recovery-exercise-status/v1",
            "ok": False,
            "recovery_exercise_ready": False,
            "status": "blocked",
            "errors": [recovery_exercise_error],
            "wallet_authority_hash": None if wallet_authority_profile is None else wallet_authority_profile.get("wallet_authority_hash"),
            "exercise_hash": None,
            "evaluation": None,
            "evaluation_hash": None,
        }
    oracle_authority_profile, oracle_authority_error = _oracle_authority_profile_from_env()
    oracle_authority = _bind_oracle_authority_status(
        evaluate_oracle_authority_profile_v1(oracle_authority_profile),
        profile=oracle_authority_profile,
        profile_error=oracle_authority_error,
        expected_chain_id=chain_id,
    )
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
        "proof_profile": _perps_proof_profile(),
        "wallet_authority": wallet_authority,
        "production_wallet_authority": wallet_authority["production_wallet_authority"],
        "oracle_authority": oracle_authority,
        "production_oracle_authority": oracle_authority["production_authority"],
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
        if rest == ["oracle-bridge", "inspect"]:
            return 200, _inspect_oracle_adapter_bridge(parsed)
        if rest == ["recovery", "evaluate"]:
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            profile, profile_error = _wallet_authority_profile_from_env()
            recovery = evaluate_perps_wallet_recovery_exercise_v1(
                profile,
                parsed,
                expected_chain_id=chain_id,
            )
            if profile_error is not None:
                recovery["ok"] = False
                recovery["recovery_exercise_ready"] = False
                recovery["status"] = "blocked"
                recovery.setdefault("errors", []).append(profile_error)
            return 200, {"ok": recovery.get("recovery_exercise_ready") is True, "recovery_exercise": recovery}
        return 404, {"ok": False, "error": "not_found"}
    except (ValueError, TypeError) as exc:
        return 400, {"ok": False, "error": str(exc)}
    except TauNetRpcError as exc:
        return 502, {"ok": False, "error": "tau_rpc_error", "detail": str(exc)}
