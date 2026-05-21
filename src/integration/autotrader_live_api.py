"""Mounted AutoTrader live-preparation API.

This API exposes the existing receipt-backed AutoTrader live-preparation path to
the ZenoDEX UI. It prepares signed intent operations and admission receipts; it
does not make unattended strategy execution a production claim.
"""

from __future__ import annotations

import json
import os
from typing import Any, Dict, Mapping, Optional, Tuple
from urllib.parse import urlsplit

from ..agents.policy_compiler import compile_policy_candidate
from ..core.quote_receipts import make_route_quote_receipt
from ..core.routing import best_route_exact_in_2hop
from ..state.pools import PoolState, PoolStatus
from .autotrader_controller import AutoTraderControllerState
from .autotrader_live import AutoTraderLiveReport, prepare_autotrader_live_quote_receipt
from .autotrader_risk_disclosure import build_autotrader_risk_disclosure
from .tau_net_client import bls_pubkey_hex_from_privkey


MAX_POST_BODY = 96_000
ResponseT = Tuple[int, Dict[str, Any]]
_RISK_ACK_ERROR = "autotrader_live_requires_risk_acknowledgement"


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


def _allow_signing() -> bool:
    return _env_bool("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", False)


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
    pool = PoolState(
        pool_id="p_ab",
        asset0="A",
        asset1="B",
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=10,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    pools = {"p_ab": pool}
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
        "fields": dict(intent.fields or {}),
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


def _build_prepare_response(body: Mapping[str, Any]) -> dict[str, Any]:
    risk_ack = bool(
        body.get("acknowledge_experimental_live_risk")
        or body.get("risk_acknowledged")
        or body.get("acknowledge_live_risk")
    )
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
        "not_claimed": [
            "unattended_production_strategy_execution",
            "production_wallet_key_management",
            "production_chain_submission",
        ],
    }


def _status_payload() -> dict[str, Any]:
    return {
        "enabled": True,
        "surface": "autotrader_live_prepare",
        "mode": "receipt_backed_prepare",
        "chain_id": _env_str("AUTOTRADER_LIVE_CHAIN_ID", "tau-local"),
        "allow_local_signing": _allow_signing(),
        "endpoints": [
            "GET /api/strategy/autotrader/status",
            "POST /api/strategy/autotrader/prepare",
        ],
        "risk_disclosure": build_autotrader_risk_disclosure(
            mode="live_prepare",
            requires_explicit_acknowledgement=True,
            user_acknowledged=False,
        ),
        "not_claimed": [
            "unattended_production_strategy_execution",
            "production_wallet_key_management",
            "production_chain_submission",
        ],
    }


def handle_autotrader_live_request(method: str, path: str, body: Optional[bytes]) -> ResponseT:
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
        return 404, {"ok": False, "error": "not_found"}
    except (ValueError, TypeError) as exc:
        return 400, {"ok": False, "error": str(exc)}
