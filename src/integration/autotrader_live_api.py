"""Mounted AutoTrader live-preparation API.

This API exposes the existing receipt-backed AutoTrader live-preparation path to
the ZenoDEX UI. It prepares signed intent operations and admission receipts; it
does not make unattended strategy execution a production claim.
"""

from __future__ import annotations

import json
import os
import threading
import time
from collections.abc import Callable
from typing import Any, Dict, Mapping, Optional, Tuple
from urllib.parse import urlsplit

from ..agents.policy_compiler import compile_policy_candidate
from ..core.liquidity import create_pool
from ..core.quote_receipts import make_route_quote_receipt
from ..core.routing import best_route_exact_in_2hop
from ..state.canonical import canonical_hex_fixed_allow_0x
from ..state.intents import Intent, require_exact_intent
from ..state.pools import PoolState, PoolStatus
from .autotrader_controller import AutoTraderControllerState
from .autotrader_execution_journal import (
    ExecutionJournalStateV2,
    execution_journal_ids,
    mark_execution_sent,
    reserve_execution_id,
)
from .autotrader_live import AutoTraderLiveReport, prepare_autotrader_live_quote_receipt
from .autotrader_risk_disclosure import build_autotrader_risk_disclosure
from .autotrader_supervisor_profile import evaluate_autotrader_supervisor_profile_v1
from .dex_snapshot import state_from_snapshot
from .tau_net_client import (
    TauNetRpcError,
    TauNetTcpClient,
    TauNetTcpConfig,
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
    encode_tau_operations_for_wire,
    tau_rpc_invalid_sequence_numbers,
    tau_rpc_response_is_success,
    verify_tau_transaction_payload_signature,
)
from .zeno_ledger_v0 import hash_v0

MAX_POST_BODY = 96_000
ResponseT = Tuple[int, Dict[str, Any]]
_RISK_ACK_ERROR = "autotrader_live_requires_risk_acknowledgement"
_AUTOTRADER_LIVE_NOT_CLAIMED = [
    "unattended_production_strategy_execution",
    "production_wallet_key_management",
    "production_chain_submission",
    "automated_pending_submission_reconciliation",
]
_AUTOTRADER_SUPERVISOR_PREFLIGHT_SCHEMA = "zenodex/autotrader-supervisor-preflight/v1"
_SUPERVISOR_RUN_COUNTERS: dict[str, int] = {}
_SUPERVISOR_EXECUTION_LOCK = threading.Lock()
_PREPARE_BUDGET_LOCK = threading.Lock()
_PREPARE_IN_FLIGHT = 0
_EXECUTION_PENDING = ExecutionJournalStateV2.PENDING.value
_EXECUTION_SENT = ExecutionJournalStateV2.SENT.value


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
    except ValueError:
        return float(default)
    return min(max(value, lo), hi)


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        value = int(raw.strip())
    except ValueError:
        return int(default)
    return min(max(value, lo), hi)


def _prepare_concurrency_limit() -> int:
    return _env_int("AUTOTRADER_LIVE_PREPARE_MAX_CONCURRENT", 2, lo=1, hi=32)


def _try_enter_prepare_budget() -> tuple[bool, int, int]:
    global _PREPARE_IN_FLIGHT
    limit = _prepare_concurrency_limit()
    with _PREPARE_BUDGET_LOCK:
        if _PREPARE_IN_FLIGHT >= limit:
            return False, _PREPARE_IN_FLIGHT, limit
        _PREPARE_IN_FLIGHT += 1
        return True, _PREPARE_IN_FLIGHT, limit


def _leave_prepare_budget() -> None:
    global _PREPARE_IN_FLIGHT
    with _PREPARE_BUDGET_LOCK:
        _PREPARE_IN_FLIGHT = max(0, _PREPARE_IN_FLIGHT - 1)


def _prepare_budget_status() -> dict[str, int]:
    with _PREPARE_BUDGET_LOCK:
        in_flight = int(_PREPARE_IN_FLIGHT)
    return {
        "max_concurrent": _prepare_concurrency_limit(),
        "in_flight": in_flight,
        "available": max(0, _prepare_concurrency_limit() - in_flight),
    }


def _execution_journal_path() -> str:
    return _env_str("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", "")


def _execution_journal_ids() -> set[str]:
    return execution_journal_ids(_execution_journal_path())


def _execution_already_consumed(execution_keys: set[str], execution_id: str) -> bool:
    if execution_id in execution_keys:
        return True
    return execution_id in _execution_journal_ids()


def _tau_submission_root(*, chain_id: str, tau_tx_payload: Mapping[str, Any]) -> str:
    return hash_v0(
        "autotrader_live_tau_submission_v1",
        {
            "chain_id": chain_id,
            "tau_tx_payload": dict(tau_tx_payload),
        },
    )


def _reserve_execution_id(
    execution_keys: set[str],
    execution_id: str,
    *,
    surface: str,
    submission_root: str,
) -> None:
    reserve_execution_id(
        path=_execution_journal_path(),
        execution_keys=execution_keys,
        execution_id=execution_id,
        surface=surface,
        submission_root=submission_root,
    )


def _mark_execution_sent(execution_id: str, *, surface: str, submission_root: str) -> None:
    mark_execution_sent(
        path=_execution_journal_path(),
        execution_id=execution_id,
        surface=surface,
        submission_root=submission_root,
    )


def _execution_transport_failure(
    *,
    execution_id: str,
    submission_root: str | None,
    sent: bool,
    mode: str | None = None,
) -> dict[str, Any]:
    execution = {
        "execution_id": execution_id,
        "state": _EXECUTION_SENT if sent else _EXECUTION_PENDING,
        "submission_root": submission_root,
        "reconciliation_required": True,
    }
    if mode is not None:
        execution["mode"] = mode
    return {
        "ok": False,
        "error": (
            "tau_submission_observation_failed"
            if sent
            else "tau_submission_outcome_unknown"
        ),
        "execution": execution,
    }


def _allow_signing() -> bool:
    return _env_bool("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", False)


def _allow_testnet_submission() -> bool:
    return _env_bool("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", False)


def _allow_execute_once() -> bool:
    return _env_bool("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", False)


def _allow_supervisor() -> bool:
    return _env_bool("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", False)


def _auto_mine() -> bool:
    return _env_bool("AUTOTRADER_LIVE_AUTO_MINE", False)


def _tau_client() -> TauNetTcpClient:
    return TauNetTcpClient(
        TauNetTcpConfig(
            host=_env_str("AUTOTRADER_LIVE_TAU_HOST", "127.0.0.1"),
            port=_env_int("AUTOTRADER_LIVE_TAU_PORT", 65432, lo=1, hi=65535),
            timeout_s=_env_float("AUTOTRADER_LIVE_TAU_TIMEOUT_S", 3.0, lo=0.1, hi=60.0),
        )
    )


def _default_tx_expiration_time() -> int:
    delta = _env_int("AUTOTRADER_LIVE_DEFAULT_DEADLINE_S", 3600, lo=1, hi=86_400)
    return int(time.time()) + int(delta)


def _pubkey_for_rpc(value: str) -> str:
    s = value.strip().lower()
    return s[2:] if s.startswith("0x") else s


def _require_root_hash(value: object, *, name: str) -> str:
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _parse_json_body(body: Optional[bytes]) -> tuple[Optional[dict[str, Any]], Optional[str]]:
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


def _int_field(data: Mapping[str, Any], key: str, default: int) -> int:
    raw = data.get(key, default)
    if isinstance(raw, bool):
        raise ValueError(f"{key} must be an int")
    if isinstance(raw, int):
        value = int(raw)
        if value < 0:
            raise ValueError(f"{key} must be non-negative")
        return value
    if isinstance(raw, str):
        text = raw.strip()
        if not text:
            raise ValueError(f"{key} must be int-like")
        try:
            value = int(text, 16) if text.lower().startswith("0x") else int(text)
        except ValueError as exc:
            raise ValueError(f"{key} must be int-like") from exc
        if value < 0:
            raise ValueError(f"{key} must be non-negative")
        return value
    raise ValueError(f"{key} must be int-like")


def _require_report_int(value: object, *, name: str) -> int:
    # Supervisor bounded-surface limits are admission controls copied into a
    # receipt hash; booleans must not inherit Python's int semantics here.
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    return int(value)


def _upstream_safe_dex_operations(operations: Mapping[str, Any]) -> dict[str, Any]:
    """Map internal DEX stream keys to Tau testnet app-bridge stream keys."""
    out: dict[str, Any] = {}
    for key, value in operations.items():
        key_s = str(key)
        if key_s == "2":
            out["5"] = value
        elif key_s == "3":
            out["6"] = value
        elif key_s == "4":
            out["7"] = value
        else:
            out[key_s] = value
    return out


def _upstream_safe_dex_stream_map(operations: Mapping[str, Any]) -> dict[str, str]:
    mapping: dict[str, str] = {}
    if "2" in operations:
        mapping["2"] = "5"
    if "3" in operations:
        mapping["3"] = "6"
    if "4" in operations:
        mapping["4"] = "7"
    return mapping


def _build_upstream_safe_tau_payload(
    *,
    tau_tx_payload: Mapping[str, Any],
    report_operations: Mapping[str, Any],
    signer_privkey: int,
) -> dict[str, Any]:
    return build_signed_tau_transaction(
        privkey=signer_privkey,
        sequence_number=_int_field(tau_tx_payload, "sequence_number", 0),
        expiration_time=_int_field(tau_tx_payload, "expiration_time", 0),
        operations=_upstream_safe_dex_operations(report_operations),
        fee_limit=str(tau_tx_payload.get("fee_limit", "0")),
    )


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


def _request_prepared_report(body: Mapping[str, Any]) -> Mapping[str, Any] | None:
    for name in ("prepared_report", "report", "autotrader_live_report"):
        value = _request_mapping(body, name=name)
        if value is not None:
            return value
    return None


def _request_execution_id(body: Mapping[str, Any]) -> str:
    raw = body.get("execution_id", body.get("execution_key"))
    if not isinstance(raw, str) or not raw.strip():
        raise ValueError("execution_id must be a non-empty string")
    value = raw.strip()
    if len(value) > 128:
        raise ValueError("execution_id too long")
    if any(ch.isspace() for ch in value):
        raise ValueError("execution_id must not contain whitespace")
    return value


def _risk_acknowledged(body: Mapping[str, Any]) -> bool:
    return bool(
        body.get("acknowledge_experimental_live_risk")
        or body.get("risk_acknowledged")
        or body.get("acknowledge_live_risk")
    )


def _operation_count(operations: object) -> int:
    if not isinstance(operations, Mapping):
        return 0
    count = 0
    for value in operations.values():
        if isinstance(value, list):
            count += len(value)
        elif isinstance(value, str):
            text = value.strip()
            if not text:
                continue
            try:
                parsed = json.loads(text)
            except (json.JSONDecodeError, UnicodeDecodeError):
                count += 1
                continue
            if isinstance(parsed, list):
                count += len(parsed)
            elif parsed is not None:
                count += 1
        elif value is not None:
            count += 1
    return count


def _validate_external_tau_tx_payload(
    payload: Mapping[str, Any],
    *,
    tx_sender_pubkey: str,
    tx_sequence_number: int,
    expiration_time: int,
    operations: Mapping[str, Any],
    tx_fee_limit: object,
) -> dict[str, Any]:
    sender_raw = payload.get("sender_pubkey")
    if not isinstance(sender_raw, str) or not sender_raw.strip():
        raise ValueError("signed_tau_tx_payload missing sender_pubkey")
    if _pubkey_for_rpc(sender_raw) != _pubkey_for_rpc(tx_sender_pubkey):
        raise ValueError("signed_tau_tx_payload sender mismatch")

    sequence_number = payload.get("sequence_number")
    if not isinstance(sequence_number, int) or isinstance(sequence_number, bool):
        raise ValueError("signed_tau_tx_payload bad sequence_number")
    if int(sequence_number) != int(tx_sequence_number):
        raise ValueError("signed_tau_tx_payload sequence mismatch")

    payload_expiration = payload.get("expiration_time")
    if not isinstance(payload_expiration, int) or isinstance(payload_expiration, bool):
        raise ValueError("signed_tau_tx_payload bad expiration_time")
    if int(payload_expiration) != int(expiration_time):
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


def _body_with_external_tau_fields(body: Mapping[str, Any]) -> dict[str, Any]:
    out = dict(body)
    external_payload = _request_signed_tau_tx_payload(body)
    if external_payload is None:
        return out
    if out.get("tx_sequence_number") is None and isinstance(external_payload.get("sequence_number"), int):
        out["tx_sequence_number"] = int(external_payload["sequence_number"])
    if out.get("tx_expiration_time") is None and isinstance(external_payload.get("expiration_time"), int):
        out["tx_expiration_time"] = int(external_payload["expiration_time"])
    if out.get("tx_fee_limit") is None and external_payload.get("fee_limit") is not None:
        out["tx_fee_limit"] = str(external_payload.get("fee_limit"))
    return out


def _pool_from_obj(data: Mapping[str, Any]) -> PoolState:
    status_raw = str(data.get("status", PoolStatus.ACTIVE.value)).strip().upper()
    return PoolState(
        pool_id=str(data["pool_id"]),
        asset0=str(data["asset0"]),
        asset1=str(data["asset1"]),
        reserve0=_int_field(data, "reserve0", 0),
        reserve1=_int_field(data, "reserve1", 0),
        fee_bps=_int_field(data, "fee_bps", 0),
        lp_supply=max(1, _int_field(data, "lp_supply", 1)),
        status=PoolStatus(status_raw),
        created_at=_int_field(data, "created_at", 0),
        curve_tag=str(data.get("curve_tag", "CPMM")),
        curve_params=str(data.get("curve_params", "")),
    )


def _pools_from_obj(obj: object) -> dict[str, PoolState]:
    if isinstance(obj, Mapping) and "pools" in obj:
        obj = obj["pools"]
    pools: dict[str, PoolState] = {}
    if isinstance(obj, Mapping):
        for key, value in obj.items():
            if not isinstance(value, Mapping):
                raise ValueError("pool map values must be objects")
            pool = _pool_from_obj(value)
            pools[str(key)] = pool
        return pools
    if isinstance(obj, list):
        for value in obj:
            if not isinstance(value, Mapping):
                raise ValueError("pool list entries must be objects")
            pool = _pool_from_obj(value)
            pools[pool.pool_id] = pool
        return pools
    raise ValueError("pools must be a map or list")


def _live_app_state_view() -> Any | None:
    try:
        raw = _tau_client().getappstate(full=True).strip()
        obj = json.loads(raw)
        if not isinstance(obj, Mapping):
            return None
        app_state = obj.get("app_state")
        if not isinstance(app_state, Mapping):
            return None
        dex_state = app_state.get("dex_state") if isinstance(app_state.get("dex_state"), Mapping) else app_state
        return state_from_snapshot(dex_state)
    except (AttributeError, TauNetRpcError, json.JSONDecodeError, KeyError, TypeError, ValueError):
        return None


def _default_fixture_from_live_app_state(*, signer_privkey: int, chain_id: str) -> dict[str, Any] | None:
    state = _live_app_state_view()
    if state is None:
        return None
    pools = {pool_id: pool for pool_id, pool in state.pools.items() if pool.status == PoolStatus.ACTIVE}
    if not pools:
        return None
    owner = "0x" + bls_pubkey_hex_from_privkey(signer_privkey)
    pool = next(iter(pools.values()))
    amount_in = max(1, min(100, int(pool.reserve0) // 100 if int(pool.reserve0) > 0 else 1))
    quote = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in=pool.asset0,
        asset_out=pool.asset1,
        amount_in=amount_in,
    )
    if quote is None:
        return None
    policy = {
        "strategy_id": "dca.live.ui",
        "owner_pubkey": owner,
        "policy_backend": "local",
        "template": "dca",
        "asset_universe": [pool.asset0, pool.asset1],
        "allowed_actions": ["PLACE_SWAP_EXACT_IN"],
        "notional_caps": {
            "per_order_max": amount_in,
            "per_window_max": amount_in * 5,
            "lifetime_max": amount_in * 10,
        },
        "risk_limits": {
            "max_slippage_bps": 50,
            "max_oracle_staleness_epochs": 3,
        },
        "strategy_window": {
            "valid_from_epoch": 1,
            "valid_until_epoch": 100,
            "min_order_spacing_epochs": 4,
        },
        "controls": {
            "kill_switch_enabled": True,
            "max_live_orders": 3,
        },
        "template_params": {
            "fixed_order_size": amount_in,
            "cadence_epochs": 4,
            "asset_in": pool.asset0,
            "asset_out": pool.asset1,
        },
    }
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)
    return {
        "policy": policy,
        "pools_by_id": pools,
        "receipt": receipt,
        "current_epoch": 5,
        "intent_deadline": _default_tx_expiration_time(),
        "last_used_nonce": state.nonces.get_last(owner),
        "chain_id": chain_id,
    }


def _default_fixture(*, signer_privkey: int, chain_id: str) -> dict[str, Any]:
    live_fixture = _default_fixture_from_live_app_state(signer_privkey=signer_privkey, chain_id=chain_id)
    if live_fixture is not None:
        return live_fixture

    owner = "0x" + bls_pubkey_hex_from_privkey(signer_privkey)
    policy = {
        "strategy_id": "dca.live.ui",
        "owner_pubkey": owner,
        "policy_backend": "local",
        "template": "dca",
        "asset_universe": ["A", "B"],
        "allowed_actions": ["PLACE_SWAP_EXACT_IN"],
        "notional_caps": {
            "per_order_max": 100,
            "per_window_max": 500,
            "lifetime_max": 1_000,
        },
        "risk_limits": {
            "max_slippage_bps": 50,
            "max_oracle_staleness_epochs": 3,
        },
        "strategy_window": {
            "valid_from_epoch": 1,
            "valid_until_epoch": 100,
            "min_order_spacing_epochs": 4,
        },
        "controls": {
            "kill_switch_enabled": True,
            "max_live_orders": 3,
        },
        "template_params": {
            "fixed_order_size": 100,
            "cadence_epochs": 4,
            "asset_in": "A",
            "asset_out": "B",
        },
    }
    _pool_id, pool, _lp_minted = create_pool(
        asset0="A",
        asset1="B",
        amount0=1_000,
        amount1=2_000,
        fee_bps=10,
        creator_pubkey=owner,
        created_at=0,
    )
    pools = {pool.pool_id: pool}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    if quote is None:
        raise ValueError("fixture quote unavailable")
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)
    return {
        "policy": policy,
        "pools_by_id": pools,
        "receipt": receipt,
        "current_epoch": 5,
        "intent_deadline": _default_tx_expiration_time(),
        "last_used_nonce": 0,
        "chain_id": chain_id,
    }


def _intent_to_obj(intent: Intent) -> dict[str, Any]:
    intent = require_exact_intent(intent)
    return {
        "module": str(intent.module),
        "version": str(intent.version),
        "kind": str(intent.kind.value),
        "intent_id": str(intent.intent_id),
        "sender_pubkey": str(intent.sender_pubkey),
        "deadline": int(intent.deadline),
        "salt": intent.salt,
        "fields": intent.to_wire_fields(),
    }


def _report_to_obj(report: AutoTraderLiveReport, *, risk_acknowledged: bool) -> dict[str, Any]:
    return {
        "schema": "zenodex/autotrader-live-api-report/v1",
        "mode": "live_prepare",
        "risk_disclosure": build_autotrader_risk_disclosure(
            mode="live_prepare",
            requires_explicit_acknowledgement=True,
            user_acknowledged=bool(risk_acknowledged),
        ),
        "signing": {
            "chain_id": report.chain_id,
            "signer_pubkey": report.signer_pubkey,
            "last_used_nonce_before": int(report.last_used_nonce_before),
            "last_used_nonce_after": int(report.last_used_nonce_after),
        },
        "decision": {
            "tag": report.decision.tag.value,
            "reason": report.decision.reason,
            "explain": list(report.decision.explain),
            "guard_state": {
                "signal_provenance_ok": bool(report.decision.guard_state.signal_provenance_ok),
                "route_economic_sanity_ok": bool(report.decision.guard_state.route_economic_sanity_ok),
                "execution_ok": bool(report.decision.guard_state.execution_ok),
                "oracle_freshness_ok": bool(report.decision.guard_state.oracle_freshness_ok),
                "budget_ok": bool(report.decision.guard_state.budget_ok),
            },
            "intents": [_intent_to_obj(intent) for intent in report.decision.intents],
        },
        "local_guard_evaluation": (
            None if report.local_guard_evaluation is None else report.local_guard_evaluation.to_dict()
        ),
        "live_admission": {
            "ok": None if report.live_admission_ok is None else bool(report.live_admission_ok),
            "error": report.live_admission_error,
        },
        "system_compose": {
            "ok": None if report.system_compose_ok is None else bool(report.system_compose_ok),
            "error": report.system_compose_error,
        },
        "candidate_set_contract": {
            "ok": None if report.candidate_set_ok is None else bool(report.candidate_set_ok),
            "error": report.candidate_set_error,
        },
        "decision_contract": {
            "ok": None if report.decision_ok is None else bool(report.decision_ok),
            "error": report.decision_error,
        },
        "submit_bundle": {
            "ok": None if report.submit_bundle_ok is None else bool(report.submit_bundle_ok),
            "error": report.submit_bundle_error,
        },
        "emit_finalize": {
            "ok": None if report.emit_finalize_ok is None else bool(report.emit_finalize_ok),
            "error": report.emit_finalize_error,
        },
        "user_rule_summary": report.user_rule_summary,
        "actionability_summary": report.actionability_summary,
        "operations": dict(report.operations),
        "tau_tx_payload": report.tau_tx_payload,
        "stage_certificate": None if report.stage_certificate is None else report.stage_certificate.to_dict(),
        "stage_certificate_error": report.stage_certificate_error,
        "live_release_certificate": (
            None if report.live_release_certificate is None else report.live_release_certificate.to_dict()
        ),
        "live_release_certificate_error": report.live_release_certificate_error,
    }


def _load_json_profile_from_env(
    *,
    json_var: str,
    file_var: str,
    label: str,
) -> tuple[Mapping[str, Any] | None, str | None]:
    raw_json = os.environ.get(json_var)
    if raw_json is not None and raw_json.strip():
        try:
            parsed = json.loads(raw_json)
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            return None, f"{label} JSON invalid: {exc}"
        if not isinstance(parsed, Mapping):
            return None, f"{label} JSON must decode to an object"
        return parsed, None
    raw_file = os.environ.get(file_var)
    if raw_file is None or not raw_file.strip():
        return None, None
    try:
        with open(raw_file.strip(), "r", encoding="utf-8") as fh:
            parsed = json.load(fh)
    except OSError as exc:
        return None, f"{label} file unreadable: {exc}"
    except json.JSONDecodeError as exc:
        return None, f"{label} file JSON invalid: {exc}"
    if not isinstance(parsed, Mapping):
        return None, f"{label} file must decode to an object"
    return parsed, None


def _supervisor_profile_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _load_json_profile_from_env(
        json_var="AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON",
        file_var="AUTOTRADER_LIVE_SUPERVISOR_PROFILE_FILE",
        label="autotrader supervisor profile",
    )


def _supervisor_process_key(
    *,
    supervisor_status: Mapping[str, Any],
    chain_id: str,
) -> str:
    supervisor_id = str(supervisor_status.get("supervisor_id") or "").strip()
    return f"{chain_id}:{supervisor_id}" if supervisor_id else chain_id


def _supervisor_runtime_state(
    *,
    supervisor_status: Mapping[str, Any],
    chain_id: str,
    supervisor_runs: Mapping[str, int] | None,
) -> dict[str, Any]:
    run_scope_id = _supervisor_process_key(supervisor_status=supervisor_status, chain_id=chain_id)
    max_runs_per_process = int(supervisor_status.get("max_runs_per_process") or 0)
    consumed_runs_in_process = int((supervisor_runs or {}).get(run_scope_id, 0))
    remaining_runs_in_process = max(0, max_runs_per_process - consumed_runs_in_process)
    return {
        "run_scope_id": run_scope_id,
        "max_runs_per_process": max_runs_per_process,
        "consumed_runs_in_process": consumed_runs_in_process,
        "remaining_runs_in_process": remaining_runs_in_process,
        "run_budget_available": remaining_runs_in_process > 0,
    }


def _supervisor_status_payload(
    *,
    chain_id: str | None = None,
    supervisor_runs: Mapping[str, int] | None = None,
) -> dict[str, Any]:
    profile, profile_error = _supervisor_profile_from_env()
    status = evaluate_autotrader_supervisor_profile_v1(profile, expected_chain_id=chain_id)
    if chain_id is not None:
        status["runtime"] = _supervisor_runtime_state(
            supervisor_status=status,
            chain_id=chain_id,
            supervisor_runs=supervisor_runs,
        )
    if profile_error:
        status["ok"] = False
        status["supervisor_ready"] = False
        status["status"] = "blocked"
        status.setdefault("readiness_gaps", []).append(profile_error)
    return status


def _build_supervisor_preflight(
    *,
    supervisor_status: Mapping[str, Any],
    execution_id: str,
    report: Mapping[str, Any],
    consumed_runs_in_process: int,
) -> dict[str, Any]:
    stage_certificate = report.get("stage_certificate")
    live_release_certificate = report.get("live_release_certificate")
    operations = report.get("operations")
    max_runs_per_process = int(supervisor_status.get("max_runs_per_process") or 0)
    remaining_runs_in_process = max(0, max_runs_per_process - int(consumed_runs_in_process))
    intent_surface = _supervisor_report_intent_surface(report)
    bounded_surface = _supervisor_report_bounded_surface(report)
    body = {
        "schema": _AUTOTRADER_SUPERVISOR_PREFLIGHT_SCHEMA,
        "supervisor_hash": supervisor_status.get("supervisor_hash"),
        "supervisor_id": supervisor_status.get("supervisor_id"),
        "chain_id": report.get("signing", {}).get("chain_id") if isinstance(report.get("signing"), Mapping) else None,
        "execution_id": execution_id,
        "required_signing_mode": "external_signed_payload",
        "external_signed_payload_required": True,
        "decision_tag": report.get("decision", {}).get("tag") if isinstance(report.get("decision"), Mapping) else None,
        "operation_count": _operation_count(operations),
        "max_actions_per_tick": int(supervisor_status.get("max_actions_per_tick") or 0),
        "max_runs_per_process": max_runs_per_process,
        "consumed_runs_in_process": int(consumed_runs_in_process),
        "remaining_runs_in_process": remaining_runs_in_process,
        "template": intent_surface.get("template"),
        "allowed_actions": list(intent_surface.get("allowed_actions") or []),
        "window_valid_from_epoch": bounded_surface.get("window_valid_from_epoch"),
        "window_valid_until_epoch": bounded_surface.get("window_valid_until_epoch"),
        "min_order_spacing_epochs": bounded_surface.get("min_order_spacing_epochs"),
        "per_order_max": bounded_surface.get("per_order_max"),
        "per_window_max": bounded_surface.get("per_window_max"),
        "lifetime_max": bounded_surface.get("lifetime_max"),
        "kill_switch_enabled": bounded_surface.get("kill_switch_enabled"),
        "bounded_surface_hash": bounded_surface.get("bounded_surface_hash"),
        "stage_hash": stage_certificate.get("stage_hash") if isinstance(stage_certificate, Mapping) else None,
        "release_hash": live_release_certificate.get("release_hash") if isinstance(live_release_certificate, Mapping) else None,
        "release_ok": (
            live_release_certificate.get("release_ok")
            if isinstance(live_release_certificate, Mapping)
            else None
        ),
        "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
    }
    return {**body, "preflight_hash": hash_v0("autotrader_supervisor_preflight_v1", body)}


def _supervisor_report_intent_surface(report: Mapping[str, Any]) -> dict[str, Any]:
    user_rule_summary = report.get("user_rule_summary")
    if not isinstance(user_rule_summary, Mapping):
        raise ValueError("supervisor_user_rule_summary_missing")
    intent = user_rule_summary.get("intent")
    if not isinstance(intent, Mapping):
        raise ValueError("supervisor_user_rule_intent_missing")
    template = intent.get("template")
    if not isinstance(template, str) or not template.strip():
        raise ValueError("supervisor_template_missing")
    raw_actions = intent.get("allowed_actions")
    if not isinstance(raw_actions, list) or not raw_actions:
        raise ValueError("supervisor_allowed_actions_missing")
    allowed_actions: list[str] = []
    for item in raw_actions:
        if not isinstance(item, str) or not item.strip():
            raise ValueError("supervisor_allowed_actions_missing")
        allowed_actions.append(item.strip().upper().replace("-", "_").replace(" ", "_"))
    return {
        "template": template.strip(),
        "allowed_actions": allowed_actions,
    }


def _supervisor_report_bounded_surface(report: Mapping[str, Any]) -> dict[str, Any]:
    user_rule_summary = report.get("user_rule_summary")
    if not isinstance(user_rule_summary, Mapping):
        raise ValueError("supervisor_user_rule_summary_missing")
    window = user_rule_summary.get("window")
    if not isinstance(window, Mapping):
        raise ValueError("supervisor_user_rule_window_missing")
    sizing = user_rule_summary.get("sizing")
    if not isinstance(sizing, Mapping):
        raise ValueError("supervisor_user_rule_sizing_missing")
    budget = user_rule_summary.get("budget")
    if not isinstance(budget, Mapping):
        raise ValueError("supervisor_user_rule_budget_missing")
    controls = user_rule_summary.get("controls")
    if not isinstance(controls, Mapping):
        raise ValueError("supervisor_user_rule_controls_missing")

    try:
        valid_from_epoch = _require_report_int(
            window.get("valid_from_epoch"),
            name="user_rule_summary.window.valid_from_epoch",
        )
        valid_until_epoch = _require_report_int(
            window.get("valid_until_epoch"),
            name="user_rule_summary.window.valid_until_epoch",
        )
        min_order_spacing_epochs = _require_report_int(
            window.get("min_order_spacing_epochs", 0),
            name="user_rule_summary.window.min_order_spacing_epochs",
        )
        per_order_max = _require_report_int(
            sizing.get("per_order_max"),
            name="user_rule_summary.sizing.per_order_max",
        )
        per_window_max = _require_report_int(
            budget.get("per_window_max"),
            name="user_rule_summary.budget.per_window_max",
        )
        lifetime_max = _require_report_int(
            budget.get("lifetime_max"),
            name="user_rule_summary.budget.lifetime_max",
        )
    except (TypeError, ValueError):
        raise ValueError("supervisor_user_rule_budget_invalid") from None
    if not isinstance(controls.get("kill_switch_enabled"), bool):
        raise ValueError("supervisor_user_rule_controls_invalid")
    kill_switch_enabled = bool(controls.get("kill_switch_enabled"))
    if valid_from_epoch > valid_until_epoch:
        raise ValueError("supervisor_user_rule_window_invalid")
    if min_order_spacing_epochs < 0:
        raise ValueError("supervisor_user_rule_window_invalid")
    if per_order_max <= 0 or per_window_max <= 0 or lifetime_max <= 0:
        raise ValueError("supervisor_user_rule_budget_invalid")
    if per_order_max > lifetime_max:
        raise ValueError("supervisor_user_rule_budget_invalid")

    body = {
        "window_valid_from_epoch": valid_from_epoch,
        "window_valid_until_epoch": valid_until_epoch,
        "min_order_spacing_epochs": min_order_spacing_epochs,
        "per_order_max": per_order_max,
        "per_window_max": per_window_max,
        "lifetime_max": lifetime_max,
        "kill_switch_enabled": kill_switch_enabled,
    }
    return {
        **body,
        "bounded_surface_hash": hash_v0("autotrader_supervisor_bounded_surface_v1", body),
    }


def _check_supervisor_allowed_surface(
    *,
    supervisor_status: Mapping[str, Any],
    report: Mapping[str, Any],
) -> str | None:
    intent_surface = _supervisor_report_intent_surface(report)
    template = str(intent_surface["template"])
    allowed_templates = {
        str(item).strip().lower().replace("-", "_").replace(" ", "_")
        for item in supervisor_status.get("allowed_templates", [])
        if str(item).strip()
    }
    normalized_template = template.lower().replace("-", "_").replace(" ", "_")
    if allowed_templates and normalized_template not in allowed_templates:
        return f"supervisor_template_not_allowed:{template}"
    profile_allowed_actions = {
        str(item).strip().lower().replace("-", "_").replace(" ", "_")
        for item in supervisor_status.get("allowed_actions", [])
        if str(item).strip()
    }
    for action in intent_surface["allowed_actions"]:
        normalized_action = action.lower().replace("-", "_").replace(" ", "_")
        if profile_allowed_actions and normalized_action not in profile_allowed_actions:
            return f"supervisor_action_not_allowed:{action}"
    return None


def _check_supervisor_prepared_report_binding(
    *,
    supervisor_status: Mapping[str, Any],
    report: Mapping[str, Any],
) -> str | None:
    if report.get("schema") != "zenodex/autotrader-live-api-report/v1":
        return "supervisor_prepared_report_schema_mismatch"
    if report.get("mode") != "live_prepare":
        return "supervisor_prepared_report_mode_mismatch"
    signing = report.get("signing")
    if not isinstance(signing, Mapping):
        return "supervisor_prepared_report_signing_missing"
    report_chain_id = signing.get("chain_id")
    if report_chain_id != supervisor_status.get("chain_id"):
        return "supervisor_prepared_report_chain_id_mismatch"
    signer_pubkey = signing.get("signer_pubkey")
    if not isinstance(signer_pubkey, str) or not signer_pubkey.strip():
        return "supervisor_prepared_report_signer_missing"
    return None


def _build_prepare_response(body: Mapping[str, Any]) -> dict[str, Any]:
    acquired, in_flight, limit = _try_enter_prepare_budget()
    if not acquired:
        return {
            "ok": False,
            "error": "autotrader_prepare_busy",
            "http_status": 429,
            "prepare_budget": {
                "max_concurrent": limit,
                "in_flight": in_flight,
                "available": 0,
            },
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    try:
        return _build_prepare_response_inner(body)
    finally:
        _leave_prepare_budget()


def _build_prepare_response_inner(body: Mapping[str, Any]) -> dict[str, Any]:
    risk_ack = _risk_acknowledged(body)
    if not risk_ack:
        return {
            "ok": False,
            "error": _RISK_ACK_ERROR,
            "risk_disclosure": build_autotrader_risk_disclosure(
                mode="live_prepare",
                requires_explicit_acknowledgement=True,
                user_acknowledged=False,
            ),
        }
    if not _allow_signing():
        return {
            "ok": False,
            "error": "local_signing_disabled",
            "risk_disclosure": build_autotrader_risk_disclosure(
                mode="live_prepare",
                requires_explicit_acknowledgement=True,
                user_acknowledged=True,
            ),
        }

    if body.get("signer_privkey") is None:
        return {"ok": False, "error": "missing_signer_privkey"}
    signer_privkey = _int_field(body, "signer_privkey", 0)
    chain_id = str(body.get("chain_id") or _env_str("AUTOTRADER_LIVE_CHAIN_ID", "tau-local"))
    fixture = _default_fixture(signer_privkey=signer_privkey, chain_id=chain_id)
    policy_obj = body.get("policy") or body.get("strategy") or fixture["policy"]
    if not isinstance(policy_obj, Mapping):
        raise ValueError("policy must be an object")
    strategy = compile_policy_candidate(dict(policy_obj)).strategy

    pools_obj = body.get("pools") or body.get("pools_by_id")
    pools_by_id = fixture["pools_by_id"] if pools_obj is None else _pools_from_obj(pools_obj)
    receipt = body.get("receipt") or fixture["receipt"]
    if not isinstance(receipt, Mapping):
        raise ValueError("receipt must be an object")
    default_intent_deadline = int(fixture["intent_deadline"])
    if body.get("intent_deadline") is None and body.get("tx_expiration_time") is not None:
        default_intent_deadline = _int_field(body, "tx_expiration_time", default_intent_deadline)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools_by_id,
        current_epoch=_int_field(body, "current_epoch", int(fixture["current_epoch"])),
        intent_deadline=_int_field(body, "intent_deadline", default_intent_deadline),
        signer_privkey=signer_privkey,
        last_used_nonce=_int_field(body, "last_used_nonce", int(fixture["last_used_nonce"])),
        chain_id=chain_id,
        krr_backend=str(body.get("krr_backend") or "off"),
        tx_sequence_number=(
            None if body.get("tx_sequence_number") is None else _int_field(body, "tx_sequence_number", 0)
        ),
        tx_expiration_time=(
            None if body.get("tx_expiration_time") is None else _int_field(body, "tx_expiration_time", 0)
        ),
        tx_fee_limit=body.get("tx_fee_limit", "0"),
    )

    report_obj = _report_to_obj(report, risk_acknowledged=risk_ack)
    decision_obj = report_obj.get("decision")
    decision: Mapping[str, Any] = decision_obj if isinstance(decision_obj, Mapping) else {}
    live_admission_obj = report_obj.get("live_admission")
    live_admission: Mapping[str, Any] = (
        live_admission_obj if isinstance(live_admission_obj, Mapping) else {}
    )
    decision_tag = decision.get("tag")
    prepared_ok = decision_tag == "submit" and live_admission.get("ok") is not False
    return {
        "ok": prepared_ok,
        "status": "prepared" if prepared_ok else "prepared_rejected",
        "surface": "autotrader_live_prepare",
        "error": None if prepared_ok else str(live_admission.get("error") or f"decision_{decision_tag or 'unknown'}"),
        "report": report_obj,
        "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
    }


def _build_external_prepared_response(body: Mapping[str, Any]) -> dict[str, Any] | None:
    report = _request_prepared_report(body)
    if report is None:
        return None
    if not _risk_acknowledged(body):
        return {
            "ok": False,
            "error": _RISK_ACK_ERROR,
            "risk_disclosure": build_autotrader_risk_disclosure(
                mode="live_prepare",
                requires_explicit_acknowledgement=True,
                user_acknowledged=False,
            ),
        }
    return {
        "ok": True,
        "status": "prepared",
        "surface": "autotrader_live_external_prepared_report",
        "report": dict(report),
        "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
    }


def _tx_send_ok(response: object) -> bool:
    return tau_rpc_response_is_success(response)


def _observe_app_hash(client: TauNetTcpClient) -> str | None:
    try:
        raw = client.getappstate(full=True).strip()
        obj = json.loads(raw)
        if not isinstance(obj, Mapping):
            return None
        app_hash = obj.get("app_hash")
        if isinstance(app_hash, str) and app_hash.strip():
            return app_hash.strip()
        app_state = obj.get("app_state")
        if isinstance(app_state, Mapping):
            return hash_v0("tau_app_state_observation_v1", dict(app_state))
    except (AttributeError, TauNetRpcError, json.JSONDecodeError, TypeError, ValueError):
        return None
    return None


def _app_hash_wait_timeout_s() -> float:
    return _env_float("AUTOTRADER_LIVE_APP_HASH_WAIT_S", 2.0, lo=0.0, hi=30.0)


def _wait_for_app_hash_change(
    client: TauNetTcpClient,
    app_hash_before: str | None,
    *,
    submission: dict[str, Any],
) -> bool:
    timeout_s = _app_hash_wait_timeout_s()
    deadline = time.monotonic() + timeout_s
    observed_app_hash: str | None = None
    while True:
        observed_app_hash = _observe_app_hash(client)
        if observed_app_hash is not None:
            submission["observed_app_hash_after_wait"] = observed_app_hash
            if app_hash_before is not None and observed_app_hash != app_hash_before:
                return True
        if time.monotonic() >= deadline:
            return False
        time.sleep(0.25)


def _mine_or_observe_sequence_advance(
    *,
    client: TauNetTcpClient,
    signer_pubkey: str,
    initial_sequence: int,
    initial_app_hash: str | None,
    submission: dict[str, Any],
) -> bool:
    createblock_response = client.createblock()
    submission["createblock_response"] = createblock_response
    if _tx_send_ok(createblock_response):
        return True
    observed_app_hash = _observe_app_hash(client)
    if observed_app_hash is not None:
        submission["observed_app_hash_after_createblock"] = observed_app_hash
        if initial_app_hash is not None and observed_app_hash != initial_app_hash:
            return True
    if initial_app_hash is not None and _wait_for_app_hash_change(
        client,
        initial_app_hash,
        submission=submission,
    ):
        return True
    try:
        observed_sequence = int(client.get_sequence(_pubkey_for_rpc(signer_pubkey)))
        submission["observed_sequence_after_createblock"] = observed_sequence
        if observed_sequence > int(initial_sequence):
            submission["sequence_advanced_without_app_delta"] = True
    except (AttributeError, OSError, TauNetRpcError, TypeError, ValueError) as exc:
        submission["sequence_observation_error"] = f"{type(exc).__name__}: {exc}"
    return False


def _build_external_prepared_submit_response(
    body: Mapping[str, Any],
    *,
    prepared: Mapping[str, Any],
    before_send: Callable[[Mapping[str, Any]], None] | None = None,
    after_send_accepted: Callable[[], None] | None = None,
) -> dict[str, Any]:
    if not _allow_testnet_submission():
        return {
            "ok": False,
            "error": "testnet_submission_disabled",
            "risk_disclosure": build_autotrader_risk_disclosure(
                mode="live_submit",
                requires_explicit_acknowledgement=True,
                user_acknowledged=_risk_acknowledged(body),
            ),
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    external_payload = _request_signed_tau_tx_payload(body)
    if external_payload is None:
        return {"ok": False, "error": "external_signed_tau_tx_payload_required"}
    report = prepared.get("report")
    if not isinstance(report, Mapping):
        return {"ok": False, "error": "prepared_report_missing"}
    if report.get("schema") != "zenodex/autotrader-live-api-report/v1":
        return {"ok": False, "error": "prepared_report_schema_mismatch"}
    if report.get("mode") != "live_prepare":
        return {"ok": False, "error": "prepared_report_mode_mismatch"}
    signing = report.get("signing")
    if not isinstance(signing, Mapping):
        return {"ok": False, "error": "prepared_report_signing_missing"}
    expected_chain_id = str(body.get("chain_id") or _env_str("AUTOTRADER_LIVE_CHAIN_ID", "tau-local"))
    if signing.get("chain_id") != expected_chain_id:
        return {"ok": False, "error": "prepared_report_chain_id_mismatch"}
    signer_pubkey = signing.get("signer_pubkey")
    if not isinstance(signer_pubkey, str) or not signer_pubkey.strip():
        return {"ok": False, "error": "prepared_report_signer_missing"}
    operations = report.get("operations")
    if not isinstance(operations, Mapping):
        return {"ok": False, "error": "prepared_report_operations_missing"}
    sender_pubkey = external_payload.get("sender_pubkey")
    if not isinstance(sender_pubkey, str) or not sender_pubkey.strip():
        return {"ok": False, "error": "signed_tau_tx_payload missing sender_pubkey"}
    expiration_time = external_payload.get("expiration_time")
    if not isinstance(expiration_time, int) or isinstance(expiration_time, bool):
        return {"ok": False, "error": "signed_tau_tx_payload bad expiration_time"}

    client = _tau_client()
    current_sequence = int(client.get_sequence(_pubkey_for_rpc(signer_pubkey)))
    try:
        tau_tx_payload = _validate_external_tau_tx_payload(
            external_payload,
            tx_sender_pubkey=signer_pubkey,
            tx_sequence_number=current_sequence,
            expiration_time=int(expiration_time),
            operations=operations,
            tx_fee_limit=external_payload.get("fee_limit"),
        )
    except ValueError as exc:
        return {"ok": False, "error": str(exc)}

    prepared_report = {
        **dict(report),
        "tau_tx_payload": tau_tx_payload,
        "tau_tx_signing_mode": "external_signed_payload",
    }
    prepared_payload = {**dict(prepared), "report": prepared_report}
    initial_app_hash = _observe_app_hash(client)
    if before_send is not None:
        before_send(tau_tx_payload)
    send_response = client.sendtx(tau_tx_payload)
    submission: dict[str, Any] = {"sendtx_response": send_response, "signing_mode": "external_signed_payload"}
    if not _tx_send_ok(send_response):
        return {
            **prepared_payload,
            "ok": False,
            "status": "submit_rejected",
            "surface": "autotrader_live_local_testnet_submit",
            "error": "sendtx_failed",
            "submission": submission,
        }
    if after_send_accepted is not None:
        after_send_accepted()
    if _auto_mine():
        if not _mine_or_observe_sequence_advance(
            client=client,
            signer_pubkey=signer_pubkey,
            initial_sequence=current_sequence,
            initial_app_hash=initial_app_hash,
            submission=submission,
        ):
            return {
                **prepared_payload,
                "ok": False,
                "status": "submit_rejected",
                "surface": "autotrader_live_local_testnet_submit",
                "error": "createblock_failed",
                "submission": submission,
            }
    return {
        **prepared_payload,
        "ok": True,
        "status": "submitted",
        "surface": "autotrader_live_local_testnet_submit",
        "submission": submission,
        "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
    }


def _build_submit_response(
    body: Mapping[str, Any],
    *,
    before_send: Callable[[Mapping[str, Any]], None] | None = None,
    after_send_accepted: Callable[[], None] | None = None,
) -> dict[str, Any]:
    if not _allow_testnet_submission():
        return {
            "ok": False,
            "error": "testnet_submission_disabled",
            "risk_disclosure": build_autotrader_risk_disclosure(
                mode="live_submit",
                requires_explicit_acknowledgement=True,
                user_acknowledged=bool(
                    body.get("acknowledge_experimental_live_risk")
                    or body.get("risk_acknowledged")
                    or body.get("acknowledge_live_risk")
                ),
            ),
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }

    external_prepared = _build_external_prepared_response(body)
    if external_prepared is not None:
        return {
            "ok": False,
            "error": "external_prepared_report_untrusted",
            "status": "submit_rejected",
            "surface": "autotrader_live_local_testnet_submit",
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }

    submit_body: dict[str, Any] = _body_with_external_tau_fields(body)
    external_payload = _request_signed_tau_tx_payload(body)
    if submit_body.get("signer_privkey") is None:
        return {"ok": False, "error": "missing_signer_privkey"}
    signer_privkey = _int_field(submit_body, "signer_privkey", 0)
    signer_pubkey_raw = bls_pubkey_hex_from_privkey(signer_privkey)
    client = _tau_client()
    current_sequence = int(client.get_sequence(signer_pubkey_raw))
    if submit_body.get("tx_sequence_number") is None:
        submit_body["tx_sequence_number"] = current_sequence
    elif _int_field(submit_body, "tx_sequence_number", 0) != current_sequence:
        error = (
            "signed_tau_tx_payload sequence mismatch"
            if external_payload is not None
            else "tx_sequence_number sequence mismatch"
        )
        return {
            "ok": False,
            "error": error,
            "risk_disclosure": build_autotrader_risk_disclosure(
                mode="live_submit",
                requires_explicit_acknowledgement=True,
                user_acknowledged=bool(
                    body.get("acknowledge_experimental_live_risk")
                    or body.get("risk_acknowledged")
                    or body.get("acknowledge_live_risk")
                ),
            ),
        }
    if submit_body.get("tx_expiration_time") is None:
        submit_body["tx_expiration_time"] = _default_tx_expiration_time()

    prepared = _build_prepare_response(submit_body)
    if prepared.get("ok") is not True:
        return prepared
    report = prepared.get("report")
    if not isinstance(report, Mapping):
        return {"ok": False, "error": "prepared_report_missing"}
    tau_tx_payload = report.get("tau_tx_payload")
    if not isinstance(tau_tx_payload, Mapping):
        return {"ok": False, "error": "tau_tx_payload_missing"}
    report_operations = report.get("operations")
    if not isinstance(report_operations, Mapping):
        return {"ok": False, "error": "prepared_report_operations_missing"}
    wire_tau_tx_payload = dict(tau_tx_payload)
    signing_mode = "local_test_signing"
    if external_payload is not None:
        signing = report.get("signing")
        if not isinstance(signing, Mapping):
            return {"ok": False, "error": "prepared_signing_missing"}
        tau_tx_payload = _validate_external_tau_tx_payload(
            external_payload,
            tx_sender_pubkey=str(signing.get("signer_pubkey") or ""),
            tx_sequence_number=int(submit_body["tx_sequence_number"]),
            expiration_time=int(submit_body["tx_expiration_time"]),
            operations=report["operations"] if isinstance(report.get("operations"), Mapping) else {},
            tx_fee_limit=tau_tx_payload.get("fee_limit"),
        )
        report = {**dict(report), "tau_tx_payload": tau_tx_payload, "tau_tx_signing_mode": "external_signed_payload"}
        prepared = {**prepared, "report": report}
        signing_mode = "external_signed_payload"
        wire_tau_tx_payload = dict(tau_tx_payload)
    else:
        wire_tau_tx_payload = _build_upstream_safe_tau_payload(
            tau_tx_payload=tau_tx_payload,
            report_operations=report_operations,
            signer_privkey=signer_privkey,
        )

    initial_app_hash = _observe_app_hash(client)
    if before_send is not None:
        before_send(wire_tau_tx_payload)
    send_response = client.sendtx(wire_tau_tx_payload)
    submission: dict[str, Any] = {
        "sendtx_response": send_response,
        "signing_mode": signing_mode,
        "wire_stream_map": _upstream_safe_dex_stream_map(report_operations) if external_payload is None else {},
        "wire_tau_tx_payload": wire_tau_tx_payload,
    }
    if not _tx_send_ok(send_response):
        invalid_sequence = tau_rpc_invalid_sequence_numbers(send_response)
        if (
            before_send is None
            and
            external_payload is None
            and invalid_sequence is not None
            and int(invalid_sequence[1]) == int(current_sequence)
            and int(invalid_sequence[0]) > int(current_sequence)
        ):
            current_sequence = int(invalid_sequence[0])
            submit_body["tx_sequence_number"] = current_sequence
            submission["retry_sequence_error"] = {
                "expected": int(invalid_sequence[0]),
                "got": int(invalid_sequence[1]),
            }
            submission["initial_wire_tau_tx_payload"] = wire_tau_tx_payload
            prepared = _build_prepare_response(submit_body)
            if prepared.get("ok") is True and isinstance(prepared.get("report"), Mapping):
                report = prepared["report"]
                tau_tx_payload = report.get("tau_tx_payload")
                report_operations = report.get("operations")
                if isinstance(tau_tx_payload, Mapping) and isinstance(report_operations, Mapping):
                    wire_tau_tx_payload = _build_upstream_safe_tau_payload(
                        tau_tx_payload=tau_tx_payload,
                        report_operations=report_operations,
                        signer_privkey=signer_privkey,
                    )
                    submission["wire_tau_tx_payload"] = wire_tau_tx_payload
                    submission["wire_stream_map"] = _upstream_safe_dex_stream_map(report_operations)
                    initial_app_hash = _observe_app_hash(client)
                    retry_send_response = client.sendtx(wire_tau_tx_payload)
                    submission["retry_sendtx_response"] = retry_send_response
                    send_response = retry_send_response
        if not _tx_send_ok(send_response):
            return {
                **prepared,
                "ok": False,
                "status": "submit_rejected",
                "surface": "autotrader_live_local_testnet_submit",
                "error": "sendtx_failed",
                "submission": submission,
            }
    if after_send_accepted is not None:
        after_send_accepted()
    if _auto_mine():
        if not _mine_or_observe_sequence_advance(
            client=client,
            signer_pubkey=signer_pubkey_raw,
            initial_sequence=current_sequence,
            initial_app_hash=initial_app_hash,
            submission=submission,
        ):
            return {
                **prepared,
                "ok": False,
                "status": "submit_rejected",
                "surface": "autotrader_live_local_testnet_submit",
                "error": "createblock_failed",
                "submission": submission,
            }

    return {
        **prepared,
        "status": "submitted",
        "surface": "autotrader_live_local_testnet_submit",
        "submission": submission,
        "not_claimed": [
            *_AUTOTRADER_LIVE_NOT_CLAIMED,
        ],
    }


def _build_supervisor_preflight_response(
    body: Mapping[str, Any],
    *,
    supervisor_runs: Mapping[str, int] | None,
) -> dict[str, Any]:
    if not _allow_supervisor():
        return {
            "ok": False,
            "error": "supervisor_disabled",
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    chain_id = str(body.get("chain_id") or _env_str("AUTOTRADER_LIVE_CHAIN_ID", "tau-local"))
    supervisor = _supervisor_status_payload(chain_id=chain_id, supervisor_runs=supervisor_runs)
    if supervisor.get("supervisor_ready") is not True:
        return {
            "ok": False,
            "error": "supervisor_profile_not_ready",
            "supervisor": supervisor,
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    runtime_obj = supervisor.get("runtime")
    runtime: Mapping[str, Any] = runtime_obj if isinstance(runtime_obj, Mapping) else {}
    consumed_runs_in_process = int(runtime.get("consumed_runs_in_process") or 0)
    max_runs_per_process = int(supervisor.get("max_runs_per_process") or 0)
    if max_runs_per_process > 0 and consumed_runs_in_process >= max_runs_per_process:
        return {
            "ok": False,
            "error": f"supervisor_max_runs_per_process_exceeded:{consumed_runs_in_process}>={max_runs_per_process}",
            "supervisor": supervisor,
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    execution_id = _request_execution_id(body)
    external_prepared = _build_external_prepared_response(body)
    if external_prepared is not None:
        if supervisor.get("require_local_preparation") is True:
            return {
                "ok": False,
                "error": "supervisor_external_prepared_report_untrusted",
                "supervisor": supervisor,
                "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
            }
        if (
            supervisor.get("stage_certificate_required") is True
            or supervisor.get("release_certificate_required") is True
        ):
            return {
                "ok": False,
                "error": "supervisor_external_prepared_report_certificates_untrusted",
                "supervisor": supervisor,
                "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
            }
        prepared = external_prepared
    else:
        prepared = _build_prepare_response(_body_with_external_tau_fields(body))
    if prepared.get("ok") is not True:
        return prepared
    report = prepared.get("report")
    if not isinstance(report, Mapping):
        return {"ok": False, "error": "prepared_report_missing"}
    binding_error = _check_supervisor_prepared_report_binding(
        supervisor_status=supervisor,
        report=report,
    )
    if binding_error is not None:
        return {
            "ok": False,
            "error": binding_error,
            "supervisor": supervisor,
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    try:
        surface_error = _check_supervisor_allowed_surface(
            supervisor_status=supervisor,
            report=report,
        )
    except ValueError as exc:
        return {
            "ok": False,
            "error": str(exc),
            "supervisor": supervisor,
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    if surface_error is not None:
        return {
            "ok": False,
            "error": surface_error,
            "supervisor": supervisor,
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    try:
        _supervisor_report_bounded_surface(report)
    except ValueError as exc:
        return {
            "ok": False,
            "error": str(exc),
            "supervisor": supervisor,
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    operations = report.get("operations")
    operation_count = _operation_count(operations)
    max_actions_per_tick = int(supervisor.get("max_actions_per_tick") or 0)
    if operation_count > max_actions_per_tick:
        return {
            "ok": False,
            "error": f"supervisor_max_actions_per_tick_exceeded:{operation_count}>{max_actions_per_tick}",
            "supervisor": supervisor,
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    if supervisor.get("stage_certificate_required") is True:
        stage_certificate = report.get("stage_certificate")
        if not isinstance(stage_certificate, Mapping):
            return {
                "ok": False,
                "error": "supervisor_stage_certificate_missing",
                "supervisor": supervisor,
                "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
            }
        stage_hash = stage_certificate.get("stage_hash")
        if not isinstance(stage_hash, str) or not stage_hash.strip():
            return {
                "ok": False,
                "error": "supervisor_stage_certificate_hash_missing",
                "supervisor": supervisor,
                "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
            }
        try:
            _require_root_hash(stage_hash, name="stage_hash")
        except (TypeError, ValueError):
            return {
                "ok": False,
                "error": "supervisor_stage_certificate_hash_invalid",
                "supervisor": supervisor,
                "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
            }
    if supervisor.get("release_certificate_required") is True and not isinstance(
        report.get("live_release_certificate"),
        Mapping,
    ):
        return {
            "ok": False,
            "error": "supervisor_release_certificate_missing",
            "supervisor": supervisor,
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    if supervisor.get("release_certificate_required") is True:
        live_release_certificate = report.get("live_release_certificate")
        if isinstance(live_release_certificate, Mapping):
            release_hash = live_release_certificate.get("release_hash")
            if not isinstance(release_hash, str) or not release_hash.strip():
                return {
                    "ok": False,
                    "error": "supervisor_release_certificate_hash_missing",
                    "supervisor": supervisor,
                    "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
                }
            try:
                _require_root_hash(release_hash, name="release_hash")
            except (TypeError, ValueError):
                return {
                    "ok": False,
                    "error": "supervisor_release_certificate_hash_invalid",
                    "supervisor": supervisor,
                    "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
                }
            if live_release_certificate.get("release_ok") is not True:
                return {
                    "ok": False,
                    "error": "supervisor_release_certificate_not_ok",
                    "supervisor": supervisor,
                    "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
                }
    preflight = _build_supervisor_preflight(
        supervisor_status=supervisor,
        execution_id=execution_id,
        report=report,
        consumed_runs_in_process=consumed_runs_in_process,
    )
    return {
        **prepared,
        "status": "supervisor_preflight_ready",
        "surface": "autotrader_live_supervisor_preflight",
        "supervisor": supervisor,
        "preflight": preflight,
        "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
    }


def _build_supervisor_execute_response(
    body: Mapping[str, Any],
    *,
    execution_keys: set[str] | None,
    supervisor_runs: dict[str, int] | None,
) -> dict[str, Any]:
    if execution_keys is None:
        return {"ok": False, "error": "execution_key_table_unavailable"}
    if _request_signed_tau_tx_payload(body) is None:
        return {
            "ok": False,
            "error": "external_signed_tau_tx_payload_required",
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    if supervisor_runs is None:
        supervisor_runs = _SUPERVISOR_RUN_COUNTERS
    preflight_payload = _build_supervisor_preflight_response(body, supervisor_runs=supervisor_runs)
    if preflight_payload.get("ok") is not True:
        return preflight_payload
    execution_id = _request_execution_id(body)
    supervisor_obj = preflight_payload.get("supervisor")
    supervisor: Mapping[str, Any] = supervisor_obj if isinstance(supervisor_obj, Mapping) else {}
    chain_id = str(body.get("chain_id") or _env_str("AUTOTRADER_LIVE_CHAIN_ID", "tau-local"))
    run_scope_id = _supervisor_process_key(supervisor_status=supervisor, chain_id=chain_id)
    max_runs_per_process = int(supervisor.get("max_runs_per_process") or 0)
    with _SUPERVISOR_EXECUTION_LOCK:
        if _execution_already_consumed(execution_keys, execution_id):
            return {
                "ok": False,
                "error": "execution_replay",
                "execution": {
                    "execution_id": execution_id,
                    "replay_guard": "already_consumed",
                    "mode": "supervised_manual_tick",
                },
                "supervisor": preflight_payload.get("supervisor"),
                "preflight": preflight_payload.get("preflight"),
            }
        consumed_before = int(supervisor_runs.get(run_scope_id, 0))
        if max_runs_per_process > 0 and consumed_before >= max_runs_per_process:
            return {
                "ok": False,
                "error": f"supervisor_max_runs_per_process_exceeded:{consumed_before}>={max_runs_per_process}",
                "supervisor": preflight_payload.get("supervisor"),
                "preflight": preflight_payload.get("preflight"),
            }
        execution_surface = "autotrader_live_supervisor_execute"
        reserved = False
        sent = False
        submission_root: str | None = None

        def reserve_before_send(tau_tx_payload: Mapping[str, Any]) -> None:
            nonlocal reserved, submission_root
            submission_root = _tau_submission_root(
                chain_id=chain_id,
                tau_tx_payload=tau_tx_payload,
            )
            _reserve_execution_id(
                execution_keys,
                execution_id,
                surface=execution_surface,
                submission_root=submission_root,
            )
            reserved = True

        def mark_sent_after_acceptance() -> None:
            nonlocal sent
            if submission_root is None:
                raise ValueError("execution_journal_submission_root_unavailable")
            _mark_execution_sent(
                execution_id,
                surface=execution_surface,
                submission_root=submission_root,
            )
            sent = True

        try:
            if _request_prepared_report(body) is not None:
                submitted = _build_external_prepared_submit_response(
                    body,
                    prepared=preflight_payload,
                    before_send=reserve_before_send,
                    after_send_accepted=mark_sent_after_acceptance,
                )
            else:
                submitted = _build_submit_response(
                    body,
                    before_send=reserve_before_send,
                    after_send_accepted=mark_sent_after_acceptance,
                )
        except TauNetRpcError:
            if not reserved:
                return {"ok": False, "error": "tau_rpc_unavailable_before_submission"}
            return _execution_transport_failure(
                execution_id=execution_id,
                submission_root=submission_root,
                sent=sent,
                mode="supervised_manual_tick",
            )
        except (TypeError, ValueError) as exc:
            if not reserved:
                raise
            return {
                "ok": False,
                "error": str(exc),
                "execution": {
                    "execution_id": execution_id,
                    "state": _EXECUTION_SENT if sent else _EXECUTION_PENDING,
                    "submission_root": submission_root,
                    "reconciliation_required": True,
                    "mode": "supervised_manual_tick",
                },
            }
        if submitted.get("ok") is not True:
            if reserved:
                return {
                    **submitted,
                    "execution": {
                        "execution_id": execution_id,
                        "state": _EXECUTION_SENT if sent else _EXECUTION_PENDING,
                        "submission_root": submission_root,
                        "reconciliation_required": True,
                        "mode": "supervised_manual_tick",
                    },
                }
            return submitted
        consumed_runs_in_process = consumed_before + 1
        supervisor_runs[run_scope_id] = consumed_runs_in_process
    remaining_runs_in_process = max(0, max_runs_per_process - consumed_runs_in_process)
    return {
        **submitted,
        "status": "supervisor_executed",
        "surface": "autotrader_live_supervisor_execute",
        "supervisor": preflight_payload.get("supervisor"),
        "preflight": preflight_payload.get("preflight"),
        "execution": {
            "execution_id": execution_id,
            "replay_guard": "consumed",
            "submission_root": submission_root,
            "mode": "supervised_manual_tick",
            "run_scope_id": run_scope_id,
            "consumed_runs_in_process": consumed_runs_in_process,
            "remaining_runs_in_process": remaining_runs_in_process,
        },
        "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
    }


def _build_execute_once_response(
    body: Mapping[str, Any],
    *,
    execution_keys: set[str] | None,
) -> dict[str, Any]:
    if not _allow_execute_once():
        return {
            "ok": False,
            "error": "execute_once_disabled",
            "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
        }
    if execution_keys is None:
        return {"ok": False, "error": "execution_key_table_unavailable"}

    execution_id = _request_execution_id(body)
    with _SUPERVISOR_EXECUTION_LOCK:
        if _execution_already_consumed(execution_keys, execution_id):
            return {
                "ok": False,
                "error": "execution_replay",
                "execution": {
                    "execution_id": execution_id,
                    "replay_guard": "already_consumed",
                },
            }

        execution_surface = "autotrader_live_execute_once"
        reserved = False
        sent = False
        submission_root: str | None = None
        chain_id = str(body.get("chain_id") or _env_str("AUTOTRADER_LIVE_CHAIN_ID", "tau-local"))

        def reserve_before_send(tau_tx_payload: Mapping[str, Any]) -> None:
            nonlocal reserved, submission_root
            submission_root = _tau_submission_root(
                chain_id=chain_id,
                tau_tx_payload=tau_tx_payload,
            )
            _reserve_execution_id(
                execution_keys,
                execution_id,
                surface=execution_surface,
                submission_root=submission_root,
            )
            reserved = True

        def mark_sent_after_acceptance() -> None:
            nonlocal sent
            if submission_root is None:
                raise ValueError("execution_journal_submission_root_unavailable")
            _mark_execution_sent(
                execution_id,
                surface=execution_surface,
                submission_root=submission_root,
            )
            sent = True

        try:
            submitted = _build_submit_response(
                body,
                before_send=reserve_before_send,
                after_send_accepted=mark_sent_after_acceptance,
            )
        except TauNetRpcError:
            if not reserved:
                return {"ok": False, "error": "tau_rpc_unavailable_before_submission"}
            return _execution_transport_failure(
                execution_id=execution_id,
                submission_root=submission_root,
                sent=sent,
            )
        except (TypeError, ValueError) as exc:
            if not reserved:
                raise
            return {
                "ok": False,
                "error": str(exc),
                "execution": {
                    "execution_id": execution_id,
                    "state": _EXECUTION_SENT if sent else _EXECUTION_PENDING,
                    "submission_root": submission_root,
                    "reconciliation_required": True,
                },
            }
        if submitted.get("ok") is not True:
            if reserved:
                return {
                    **submitted,
                    "execution": {
                        "execution_id": execution_id,
                        "state": _EXECUTION_SENT if sent else _EXECUTION_PENDING,
                        "submission_root": submission_root,
                        "reconciliation_required": True,
                    },
                }
            return submitted

    return {
        **submitted,
        "status": "executed_once",
        "surface": "autotrader_live_local_testnet_execute_once",
        "execution": {
            "execution_id": execution_id,
            "replay_guard": "consumed",
            "submission_root": submission_root,
        },
        "not_claimed": [
            *_AUTOTRADER_LIVE_NOT_CLAIMED,
        ],
    }


def _status_payload() -> dict[str, Any]:
    chain_id = _env_str("AUTOTRADER_LIVE_CHAIN_ID", "tau-local")
    return {
        "enabled": True,
        "surface": "autotrader_live_prepare",
        "mode": "receipt_backed_prepare",
        "chain_id": chain_id,
        "allow_local_signing": _allow_signing(),
        "testnet_submission_enabled": _allow_testnet_submission(),
        "execute_once_enabled": _allow_execute_once(),
        "supervisor_enabled": _allow_supervisor(),
        "auto_mine": _auto_mine(),
        "prepare_budget": _prepare_budget_status(),
        "tau_host": _env_str("AUTOTRADER_LIVE_TAU_HOST", "127.0.0.1"),
        "tau_port": _env_int("AUTOTRADER_LIVE_TAU_PORT", 65432, lo=1, hi=65535),
        "supervisor": _supervisor_status_payload(
            chain_id=chain_id,
            supervisor_runs=_SUPERVISOR_RUN_COUNTERS,
        ),
        "endpoints": [
            "GET /api/strategy/autotrader/status",
            "POST /api/strategy/autotrader/prepare",
            "POST /api/strategy/autotrader/submit",
            "POST /api/strategy/autotrader/execute-once",
            "POST /api/strategy/autotrader/supervisor/preflight",
            "POST /api/strategy/autotrader/supervisor/execute",
        ],
        "risk_disclosure": build_autotrader_risk_disclosure(
            mode="live_prepare",
            requires_explicit_acknowledgement=True,
            user_acknowledged=False,
        ),
        "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
    }


def _payload_http_status(payload: Mapping[str, Any]) -> int:
    if payload.get("ok") is True:
        return 200
    raw = payload.get("http_status")
    if isinstance(raw, int) and not isinstance(raw, bool) and 400 <= raw <= 499:
        return int(raw)
    return 400


def handle_autotrader_live_request(
    method: str,
    path: str,
    body: Optional[bytes],
    *,
    execution_keys: set[str] | None = None,
    supervisor_runs: dict[str, int] | None = None,
) -> ResponseT:
    parsed_path = urlsplit(path)
    segments = [segment for segment in parsed_path.path.split("/") if segment]
    if len(segments) < 4 or segments[0] != "api" or segments[1] != "strategy" or segments[2] != "autotrader":
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
            payload = _build_prepare_response(parsed)
            return _payload_http_status(payload), payload
        if rest == ["submit"]:
            payload = _build_submit_response(parsed)
            return _payload_http_status(payload), payload
        if rest == ["execute-once"]:
            payload = _build_execute_once_response(parsed, execution_keys=execution_keys)
            return _payload_http_status(payload), payload
        if rest == ["supervisor", "preflight"]:
            payload = _build_supervisor_preflight_response(
                parsed,
                supervisor_runs=_SUPERVISOR_RUN_COUNTERS if supervisor_runs is None else supervisor_runs,
            )
            return _payload_http_status(payload), payload
        if rest == ["supervisor", "execute"]:
            payload = _build_supervisor_execute_response(
                parsed,
                execution_keys=execution_keys,
                supervisor_runs=_SUPERVISOR_RUN_COUNTERS if supervisor_runs is None else supervisor_runs,
            )
            return _payload_http_status(payload), payload
        return 404, {"ok": False, "error": "not_found"}
    except (ValueError, TypeError) as exc:
        return 400, {"ok": False, "error": str(exc)}
