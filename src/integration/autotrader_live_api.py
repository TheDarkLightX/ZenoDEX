"""Mounted AutoTrader live-preparation API.

This API exposes the existing receipt-backed AutoTrader live-preparation path to
the ZenoDEX UI. It prepares signed intent operations and admission receipts; it
does not make unattended strategy execution a production claim.
"""

from __future__ import annotations

import json
import math
import os
import time
from typing import Any, Dict, Mapping, Optional, Tuple
from urllib.parse import urlsplit

from ..agents.policy_compiler import compile_policy_candidate
from ..core.liquidity import create_pool
from ..core.quote_receipts import make_route_quote_receipt
from ..core.routing import best_route_exact_in_2hop
from ..state.immutable_collections import deep_thaw_json
from ..state.pools import PoolState, PoolStatus
from .autotrader_controller import AutoTraderControllerState
from .autotrader_live import AutoTraderLiveReport, prepare_autotrader_live_quote_receipt
from .autotrader_risk_disclosure import build_autotrader_risk_disclosure
from .autotrader_supervisor_profile import evaluate_autotrader_supervisor_profile_v1
from .tau_net_client import (
    TauNetTcpClient,
    TauNetTcpConfig,
    bls_pubkey_hex_from_privkey,
    encode_tau_operations_for_wire,
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
]
_AUTOTRADER_SUPERVISOR_PREFLIGHT_SCHEMA = "zenodex/autotrader-supervisor-preflight/v1"
_SUPERVISOR_RUN_COUNTERS: dict[str, int] = {}


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
    if isinstance(raw, (int, str)):
        value = int(raw)
        if value < 0:
            raise ValueError(f"{key} must be non-negative")
        return value
    raise ValueError(f"{key} must be int-like")


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


def _default_fixture(*, signer_privkey: int, chain_id: str) -> dict[str, Any]:
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
            "min_order_spacing_epochs": 0,
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
        "intent_deadline": 999_999_999,
        "last_used_nonce": 0,
        "chain_id": chain_id,
    }


def _intent_to_obj(intent: Any) -> dict[str, Any]:
    return {
        "module": str(intent.module),
        "version": str(intent.version),
        "kind": str(intent.kind.value),
        "intent_id": str(intent.intent_id),
        "sender_pubkey": str(intent.sender_pubkey),
        "deadline": int(intent.deadline),
        "salt": intent.salt,
        "fields": deep_thaw_json(intent.fields or {}),
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


def _build_prepare_response(body: Mapping[str, Any]) -> dict[str, Any]:
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

    signer_privkey = _int_field(body, "signer_privkey", 7)
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

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools_by_id,
        current_epoch=_int_field(body, "current_epoch", int(fixture["current_epoch"])),
        intent_deadline=_int_field(body, "intent_deadline", int(fixture["intent_deadline"])),
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

    return {
        "ok": True,
        "status": "prepared",
        "surface": "autotrader_live_prepare",
        "report": _report_to_obj(report, risk_acknowledged=risk_ack),
        "not_claimed": list(_AUTOTRADER_LIVE_NOT_CLAIMED),
    }


def _tx_send_ok(response: object) -> bool:
    text = str(response)
    return bool(text.strip()) and "ERROR" not in text.upper()


def _build_submit_response(body: Mapping[str, Any]) -> dict[str, Any]:
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

    submit_body: dict[str, Any] = dict(body)
    external_payload = _request_signed_tau_tx_payload(body)
    if external_payload is not None:
        if submit_body.get("tx_sequence_number") is None and isinstance(external_payload.get("sequence_number"), int):
            submit_body["tx_sequence_number"] = int(external_payload["sequence_number"])
        if submit_body.get("tx_expiration_time") is None and isinstance(external_payload.get("expiration_time"), int):
            submit_body["tx_expiration_time"] = int(external_payload["expiration_time"])
        if submit_body.get("tx_fee_limit") is None and external_payload.get("fee_limit") is not None:
            submit_body["tx_fee_limit"] = str(external_payload.get("fee_limit"))
    signer_privkey = _int_field(submit_body, "signer_privkey", 7)
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

    send_response = client.sendtx(tau_tx_payload)
    submission: dict[str, Any] = {"sendtx_response": send_response, "signing_mode": signing_mode}
    if not _tx_send_ok(send_response):
        return {
            **prepared,
            "ok": False,
            "status": "submit_rejected",
            "surface": "autotrader_live_local_testnet_submit",
            "error": "sendtx_failed",
            "submission": submission,
        }
    if _auto_mine():
        createblock_response = client.createblock()
        submission["createblock_response"] = createblock_response
        if not _tx_send_ok(createblock_response):
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
    runtime = supervisor.get("runtime") if isinstance(supervisor.get("runtime"), Mapping) else {}
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
    prepared = _build_prepare_response(body)
    if prepared.get("ok") is not True:
        return prepared
    report = prepared.get("report")
    if not isinstance(report, Mapping):
        return {"ok": False, "error": "prepared_report_missing"}
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
    if supervisor.get("stage_certificate_required") is True and not isinstance(report.get("stage_certificate"), Mapping):
        return {
            "ok": False,
            "error": "supervisor_stage_certificate_missing",
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
    if execution_id in execution_keys:
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
    submitted = _build_submit_response(body)
    if submitted.get("ok") is not True:
        return submitted
    execution_keys.add(execution_id)
    supervisor = preflight_payload.get("supervisor") if isinstance(preflight_payload.get("supervisor"), Mapping) else {}
    chain_id = str(body.get("chain_id") or _env_str("AUTOTRADER_LIVE_CHAIN_ID", "tau-local"))
    run_scope_id = _supervisor_process_key(supervisor_status=supervisor, chain_id=chain_id)
    consumed_runs_in_process = int(supervisor_runs.get(run_scope_id, 0)) + 1
    supervisor_runs[run_scope_id] = consumed_runs_in_process
    max_runs_per_process = int(supervisor.get("max_runs_per_process") or 0)
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
    if execution_id in execution_keys:
        return {
            "ok": False,
            "error": "execution_replay",
            "execution": {
                "execution_id": execution_id,
                "replay_guard": "already_consumed",
            },
        }

    submitted = _build_submit_response(body)
    if submitted.get("ok") is not True:
        return submitted

    execution_keys.add(execution_id)
    return {
        **submitted,
        "status": "executed_once",
        "surface": "autotrader_live_local_testnet_execute_once",
        "execution": {
            "execution_id": execution_id,
            "replay_guard": "consumed",
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
            status = 200 if payload.get("ok") is True else 400
            return status, payload
        if rest == ["submit"]:
            payload = _build_submit_response(parsed)
            status = 200 if payload.get("ok") is True else 400
            return status, payload
        if rest == ["execute-once"]:
            payload = _build_execute_once_response(parsed, execution_keys=execution_keys)
            status = 200 if payload.get("ok") is True else 400
            return status, payload
        if rest == ["supervisor", "preflight"]:
            payload = _build_supervisor_preflight_response(
                parsed,
                supervisor_runs=_SUPERVISOR_RUN_COUNTERS if supervisor_runs is None else supervisor_runs,
            )
            status = 200 if payload.get("ok") is True else 400
            return status, payload
        if rest == ["supervisor", "execute"]:
            payload = _build_supervisor_execute_response(
                parsed,
                execution_keys=execution_keys,
                supervisor_runs=_SUPERVISOR_RUN_COUNTERS if supervisor_runs is None else supervisor_runs,
            )
            status = 200 if payload.get("ok") is True else 400
            return status, payload
        return 404, {"ok": False, "error": "not_found"}
    except (ValueError, TypeError) as exc:
        return 400, {"ok": False, "error": str(exc)}
