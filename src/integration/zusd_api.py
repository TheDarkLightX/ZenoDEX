"""REST API handlers for zUSD endpoints (DEMO / DEVELOPMENT ONLY).

Pure stdlib module -- no third-party dependencies.
Imported lazily by ``api_server.py`` when a ``/api/zusd/`` path is hit.

This module intentionally keeps mutable demo state in-memory and is not the
production transaction path.
"""

from __future__ import annotations

import hashlib
import json
import os
import threading
import time
from typing import Any, Dict, List, Mapping, Optional, Tuple, cast

from ..core.zusd import (
    ZUSDCommand,
    ZUSDCommandTag,
    ZUSDMultiCommand,
    ZUSDMultiState,
    ZUSDState,
    init_multi_state,
    init_state,
)
from .zusd_tau_gate import ZUSDTauGateConfig, step_multi_with_tau, step_with_tau
from ..state.canonical import canonical_json_bytes
from .zeno_oracle_authorization import check_critical_consumer_authorization, semantic_hash

MAX_POST_BODY: int = 65_536

_lock = threading.Lock()
_demo_single: ZUSDState = init_state()
_demo_multi: ZUSDMultiState = init_multi_state()
_history: List[Dict[str, Any]] = []
_MAX_HISTORY: int = 200

ResponseT = Tuple[int, Dict[str, Any]]
PostStateResultT = Tuple[ZUSDState, ZUSDMultiState, List[Dict[str, Any]], ResponseT]
_VALID_ZUSD_TAGS: frozenset[str] = frozenset(
    {
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
    }
)
_ZUSD_ORACLE_ADAPTER_ACTIONS: Dict[str, str] = {
    "mint_zusd": "mint",
    "liquidate": "liquidate_vault",
}
_ORACLE_CONSUMER_PROFILE_SCHEMA = "zenodex.oracle.consumer_profile.v1"
_ORACLE_ZUSD_COLLATERAL_QUERY_ID = (
    "sha256:" + hashlib.sha256(b"zenodex.oracle.query.zusd.collateral_price_e8").hexdigest()
)


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


def _bool_env(name: str, *, default: bool) -> bool:
    raw = os.environ.get(name)
    if raw is None:
        return bool(default)
    v = raw.strip().lower()
    if v in {"1", "true", "yes", "on"}:
        return True
    if v in {"0", "false", "no", "off"}:
        return False
    return bool(default)


def _strict_bool_env(name: str, *, default: bool) -> bool:
    raw = os.environ.get(name)
    if raw is None:
        return bool(default)
    v = raw.strip().lower()
    if v in {"1", "true", "yes", "on"}:
        return True
    if v in {"0", "false", "no", "off"}:
        return False
    raise ValueError(f"{name} must be one of: 1, true, yes, on, 0, false, no, off")


def _float_env(name: str, default: float, *, lo: float, hi: float) -> float:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return float(default)
    try:
        v = float(raw.strip())
    except Exception:
        return float(default)
    if v < lo:
        return float(lo)
    if v > hi:
        return float(hi)
    return float(v)


def _int_env(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        v = int(raw.strip())
    except Exception:
        return int(default)
    if v < lo:
        return int(lo)
    if v > hi:
        return int(hi)
    return int(v)


def _tau_gate_config_from_env() -> ZUSDTauGateConfig:
    return ZUSDTauGateConfig(
        enabled=_bool_env("ZUSD_TAU_GATE_ENABLED", default=True),
        timeout_s=_float_env("ZUSD_TAU_GATE_TIMEOUT_S", 5.0, lo=0.1, hi=120.0),
        tau_bin=(os.environ.get("ZUSD_TAU_BIN", "").strip() or None),
        allow_path_lookup=_bool_env("ZUSD_TAU_ALLOW_PATH_LOOKUP", default=False),
    )


def _planned_single_oracle_sync_target(*, state: ZUSDState, tag: str, args: Mapping[str, Any]) -> Optional[Tuple[int, int]]:
    """Return (price_e8, epoch) for commands that would set active oracle price."""
    if tag == "bootstrap_oracle":
        raw = args.get("price_e8")
        if isinstance(raw, int) and not isinstance(raw, bool) and raw > 0:
            return int(raw), int(state.now_epoch)
        return None
    if tag == "oracle_commit":
        if state.price_pending_e8 > 0:
            return int(state.price_pending_e8), int(state.now_epoch)
        return None
    return None


def _planned_multi_oracle_sync_target(*, state: ZUSDMultiState, tag: str, args: Mapping[str, Any]) -> Optional[Tuple[int, int]]:
    """Return (price_e8, epoch) for multi-vault commands that set active oracle price."""
    if tag == "bootstrap_oracle":
        raw = args.get("price_e8")
        if isinstance(raw, int) and not isinstance(raw, bool) and raw > 0:
            return int(raw), int(state.now_epoch)
        return None
    if tag == "oracle_commit":
        if state.price_pending_e8 > 0:
            return int(state.price_pending_e8), int(state.now_epoch)
        return None
    return None


def _check_perp_oracle_sync(*, price_e8: int, epoch: int) -> Optional[str]:
    """Optional cross-module zUSD/perp oracle synchronization gate."""
    if not _bool_env("ZUSD_PERP_ORACLE_SYNC_ENABLED", default=False):
        return None
    market_id = (os.environ.get("ZUSD_PERP_ORACLE_SYNC_MARKET_ID", "TAU-USD") or "").strip()
    if not market_id:
        return "oracle_sync_config_error: missing ZUSD_PERP_ORACLE_SYNC_MARKET_ID"

    max_div_bps = _int_env(
        "ZUSD_PERP_ORACLE_SYNC_MAX_DIVERGENCE_BPS",
        500,
        lo=0,
        hi=10_000,
    )
    max_epoch_lag = _int_env(
        "ZUSD_PERP_ORACLE_SYNC_MAX_EPOCH_LAG",
        10,
        lo=0,
        hi=1_000_000,
    )

    try:
        from .perps_api import get_oracle_sync_snapshot
    except Exception as exc:
        return f"oracle_sync_unavailable:{type(exc).__name__}"

    snap = get_oracle_sync_snapshot(market_id)
    if snap is None:
        return f"oracle_sync_unavailable: market={market_id}"

    perp_price_e8 = int(snap.get("price_e8", 0))
    perp_epoch = int(snap.get("oracle_last_update_epoch", 0))
    if perp_price_e8 <= 0:
        return f"oracle_sync_unavailable: non-positive perp price for market={market_id}"

    divergence_bps = (abs(int(price_e8) - perp_price_e8) * 10_000) // perp_price_e8
    if divergence_bps > max_div_bps:
        return (
            f"oracle_sync_divergence: market={market_id} "
            f"divergence_bps={divergence_bps} cap_bps={max_div_bps}"
        )

    epoch_lag = abs(int(epoch) - perp_epoch)
    if epoch_lag > max_epoch_lag:
        return (
            f"oracle_sync_epoch_lag: market={market_id} "
            f"epoch_lag={epoch_lag} cap={max_epoch_lag}"
        )

    return None


def _single_state_payload(state: ZUSDState) -> Dict[str, Any]:
    return dict(state.__dict__)


def _multi_state_payload(state: ZUSDMultiState) -> Dict[str, Any]:
    out = dict(state.__dict__)
    out["vault_a"] = dict(state.vault_a.__dict__)
    out["vault_b"] = dict(state.vault_b.__dict__)
    return out


def _history_with_entry(
    history: List[Dict[str, Any]],
    *,
    mode: str,
    tag: str,
    args: Mapping[str, Any],
    ok: bool,
    error: Optional[str],
) -> List[Dict[str, Any]]:
    entry: Dict[str, Any] = {
        "ts": time.time(),
        "mode": mode,
        "tag": str(tag),
        "args": dict(args),
        "ok": bool(ok),
        "error": str(error) if error else None,
    }
    new_history = [*history, entry]
    if len(new_history) > _MAX_HISTORY:
        new_history = new_history[len(new_history) - _MAX_HISTORY :]
    return new_history


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


def _cmd_from_body(body: Dict[str, Any]) -> Tuple[Optional[str], Optional[Dict[str, Any]], Optional[str]]:
    tag = body.get("tag")
    args = body.get("args", {})
    if not isinstance(tag, str) or not tag:
        return None, None, "missing_tag"
    if tag not in _VALID_ZUSD_TAGS:
        return None, None, "unknown_tag"
    if not isinstance(args, dict):
        return None, None, "invalid_args"
    return tag, args, None


def _adapter_result_get(result: Any, key: str) -> Any:
    if isinstance(result, Mapping):
        return result.get(key)
    return getattr(result, key, None)


def _adapter_error_summary(result: Any) -> str:
    errors = _adapter_result_get(result, "errors")
    if isinstance(errors, list):
        parts = [str(x) for x in errors[:3]]
        if parts:
            return "; ".join(parts)
    if isinstance(errors, tuple):
        parts = [str(x) for x in errors[:3]]
        if parts:
            return "; ".join(parts)
    return "bridge verifier rejected"


def _zusd_runtime_oracle_action_id(
    *,
    mode: str,
    state: ZUSDState | ZUSDMultiState,
    tag: str,
    args: Mapping[str, Any],
) -> str:
    action_kind = _ZUSD_ORACLE_ADAPTER_ACTIONS[tag]
    payload = {
        "schema": "zenodex.oracle.zusd_runtime_action_id.v1",
        "consumer_module": "zenodex.zusd",
        "action_kind": action_kind,
        "mode": mode,
        "tag": tag,
        "args": dict(args),
        "now_epoch": int(state.now_epoch),
        "price_e8": int(state.price_e8),
        "price_pending_e8": int(state.price_pending_e8),
        "oracle_last_update_epoch": int(state.oracle_last_update_epoch),
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _zusd_runtime_oracle_pre_state_hash(*, mode: str, state: ZUSDState | ZUSDMultiState) -> str:
    state_payload = _single_state_payload(state) if isinstance(state, ZUSDState) else _multi_state_payload(state)
    return semantic_hash(
        "zenodex.zusd.pre_state.v1",
        {
            "mode": mode,
            "state": state_payload,
        },
    )


def _zusd_runtime_oracle_action_facts_hash(
    *,
    mode: str,
    state: ZUSDState | ZUSDMultiState,
    tag: str,
    args: Mapping[str, Any],
) -> str:
    action_kind = _ZUSD_ORACLE_ADAPTER_ACTIONS[tag]
    return semantic_hash(
        "zenodex.zusd.action_facts.v1",
        {
            "args": dict(args),
            "consumer_module": "zenodex.zusd",
            "action_kind": action_kind,
            "mode": mode,
            "now_epoch": int(state.now_epoch),
            "query_id": _ORACLE_ZUSD_COLLATERAL_QUERY_ID,
            "runtime_value_e8": int(state.price_e8),
            "tag": tag,
        },
    )


def _check_zusd_oracle_adapter_bridge(
    *,
    body: Mapping[str, Any],
    mode: str,
    state: ZUSDState | ZUSDMultiState,
    tag: str,
    args: Mapping[str, Any],
) -> Optional[str]:
    action_kind = _ZUSD_ORACLE_ADAPTER_ACTIONS.get(tag)
    if action_kind is None:
        return None

    try:
        required = _strict_bool_env("ZUSD_ORACLE_ADAPTER_REQUIRED", default=False)
    except ValueError as exc:
        return f"oracle_adapter_bridge config error: {exc}"
    if "oracle_adapter_bridge" not in body:
        if required:
            return f"{action_kind} requires oracle_adapter_bridge"
        return None

    bridge = body.get("oracle_adapter_bridge")
    if not isinstance(bridge, Mapping):
        return "oracle_adapter_bridge must be an object"

    try:
        from tools.zenodex_oracle_aggregate_adapter import (  # pylint: disable=import-outside-toplevel
            verify_aggregate_adapter_bridge,
        )
    except Exception as exc:
        return f"oracle_adapter_bridge verifier unavailable: {type(exc).__name__}"

    try:
        result = verify_aggregate_adapter_bridge(bridge)
    except Exception as exc:
        return f"oracle_adapter_bridge verifier error: {type(exc).__name__}"

    if _adapter_result_get(result, "status") != "accepted":
        return f"oracle_adapter_bridge rejected: {_adapter_error_summary(result)}"
    if _adapter_result_get(result, "consumer_module") != "zenodex.zusd":
        return "oracle_adapter_bridge consumer mismatch"
    if _adapter_result_get(result, "action_kind") != action_kind:
        return "oracle_adapter_bridge action mismatch"
    if _adapter_result_get(result, "query_id") != _ORACLE_ZUSD_COLLATERAL_QUERY_ID:
        return "oracle_adapter_bridge query mismatch"
    if _adapter_result_get(result, "profile_id") != _ZUSD_ORACLE_CONSUMER_PROFILE_IDS[action_kind]:
        return "oracle_adapter_bridge profile mismatch"
    expected_action_id = _zusd_runtime_oracle_action_id(mode=mode, state=state, tag=tag, args=args)
    if _adapter_result_get(result, "action_id") != expected_action_id:
        return "oracle_adapter_bridge action_id mismatch"
    return None


def _check_zusd_oracle_authorization(
    *,
    body: Mapping[str, Any],
    mode: str,
    state: ZUSDState | ZUSDMultiState,
    tag: str,
    args: Mapping[str, Any],
) -> Optional[str]:
    action_kind = _ZUSD_ORACLE_ADAPTER_ACTIONS.get(tag)
    if action_kind is None:
        return None

    try:
        required = _strict_bool_env("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", default=False)
    except ValueError as exc:
        return f"oracle_authorization config error: {exc}"

    if "oracle_authorization" not in body:
        if required:
            return f"{action_kind} requires oracle_authorization"
        return None

    authorization = body.get("oracle_authorization")
    if not isinstance(authorization, Mapping):
        return "oracle_authorization must be an object"

    try:
        result = check_critical_consumer_authorization(
            authorization,
            consumer_module="zenodex.zusd",
            action_kind=action_kind,
            action_id=_zusd_runtime_oracle_action_id(mode=mode, state=state, tag=tag, args=args),
            action_facts_hash=_zusd_runtime_oracle_action_facts_hash(mode=mode, state=state, tag=tag, args=args),
            pre_state_hash=_zusd_runtime_oracle_pre_state_hash(mode=mode, state=state),
            profile_id=_ZUSD_ORACLE_CONSUMER_PROFILE_IDS[action_kind],
            query_id=_ORACLE_ZUSD_COLLATERAL_QUERY_ID,
            runtime_value_e8=int(state.price_e8),
            now_epoch=int(state.now_epoch),
        )
    except Exception as exc:
        return f"oracle_authorization verifier error: {type(exc).__name__}"

    if not result.get("typed_ok"):
        errors = result.get("typed_errors")
        if isinstance(errors, list) and errors:
            return "oracle_authorization rejected: " + "; ".join(str(error) for error in errors[:3])
        return "oracle_authorization rejected"
    return None


def _handle_get(single: ZUSDState, multi: ZUSDMultiState, history: List[Dict[str, Any]], rest: List[str]) -> ResponseT:
    if rest == ["state"]:
        return 200, {"ok": True, "mode": "single", "state": _single_state_payload(single)}
    if rest == ["multi", "state"]:
        return 200, {"ok": True, "mode": "multi", "state": _multi_state_payload(multi)}
    if rest == ["history"]:
        return 200, {"ok": True, "history": list(reversed(history[-50:]))}
    return 404, {"ok": False, "error": "not_found"}


def _handle_post(
    single: ZUSDState,
    multi: ZUSDMultiState,
    history: List[Dict[str, Any]],
    rest: List[str],
    body: Optional[bytes],
) -> PostStateResultT:
    known = (["step"], ["multi", "step"], ["reset"])
    if rest not in known:
        return single, multi, history, (404, {"ok": False, "error": "not_found"})

    if rest == ["reset"]:
        next_single = init_state()
        next_multi = init_multi_state()
        return next_single, next_multi, [], (
            200,
            {
                "ok": True,
                "state": _single_state_payload(next_single),
                "multiState": _multi_state_payload(next_multi),
            },
        )

    parsed, err = _parse_json_body(body)
    if err is not None:
        return single, multi, history, (400, {"ok": False, "error": err})
    if parsed is None:
        return single, multi, history, (400, {"ok": False, "error": "bad_json"})

    tag, args, cmd_err = _cmd_from_body(parsed)
    if cmd_err is not None:
        return single, multi, history, (400, {"ok": False, "error": cmd_err})
    if tag is None or args is None:
        return single, multi, history, (400, {"ok": False, "error": "invalid_command"})

    tau_cfg = _tau_gate_config_from_env()

    if rest == ["step"]:
        bridge_err = _check_zusd_oracle_adapter_bridge(
            body=parsed,
            mode="single",
            state=single,
            tag=tag,
            args=args,
        )
        if bridge_err is not None:
            new_history = _history_with_entry(
                history,
                mode="single",
                tag=tag,
                args=args,
                ok=False,
                error=bridge_err,
            )
            return single, multi, new_history, (
                400,
                {
                    "ok": False,
                    "error": "rejected",
                    "detail": bridge_err,
                },
            )

        authorization_err = _check_zusd_oracle_authorization(
            body=parsed,
            mode="single",
            state=single,
            tag=tag,
            args=args,
        )
        if authorization_err is not None:
            new_history = _history_with_entry(
                history,
                mode="single",
                tag=tag,
                args=args,
                ok=False,
                error=authorization_err,
            )
            return single, multi, new_history, (
                400,
                {
                    "ok": False,
                    "error": "rejected",
                    "detail": authorization_err,
                },
            )

        sync_target = _planned_single_oracle_sync_target(state=single, tag=tag, args=args)
        if sync_target is not None:
            sync_err = _check_perp_oracle_sync(price_e8=sync_target[0], epoch=sync_target[1])
            if sync_err is not None:
                new_history = _history_with_entry(
                    history,
                    mode="single",
                    tag=tag,
                    args=args,
                    ok=False,
                    error=sync_err,
                )
                return single, multi, new_history, (
                    400,
                    {
                        "ok": False,
                        "error": "rejected",
                        "detail": sync_err,
                    },
                )

        cmd = ZUSDCommand(tag=cast(ZUSDCommandTag, tag), args=args)
        result = step_with_tau(single, cmd, config=tau_cfg)
        new_history = _history_with_entry(history, mode="single", tag=tag, args=args, ok=result.ok, error=result.error)
        if not result.ok or result.state is None:
            return single, multi, new_history, (
                400,
                {
                    "ok": False,
                    "error": "rejected",
                    "detail": result.error or "step rejected",
                },
            )
        return result.state, multi, new_history, (
            200,
            {
                "ok": True,
                "mode": "single",
                "state": _single_state_payload(result.state),
                "effects": dict(result.effects or {}),
                "tauGate": {
                    "enabled": tau_cfg.enabled,
                    "timeoutS": tau_cfg.timeout_s,
                },
            },
            )

    bridge_err_multi = _check_zusd_oracle_adapter_bridge(
        body=parsed,
        mode="multi",
        state=multi,
        tag=tag,
        args=args,
    )
    if bridge_err_multi is not None:
        new_history = _history_with_entry(
            history,
            mode="multi",
            tag=tag,
            args=args,
            ok=False,
            error=bridge_err_multi,
        )
        return single, multi, new_history, (
            400,
            {
                "ok": False,
                "error": "rejected",
                "detail": bridge_err_multi,
            },
        )

    authorization_err_multi = _check_zusd_oracle_authorization(
        body=parsed,
        mode="multi",
        state=multi,
        tag=tag,
        args=args,
    )
    if authorization_err_multi is not None:
        new_history = _history_with_entry(
            history,
            mode="multi",
            tag=tag,
            args=args,
            ok=False,
            error=authorization_err_multi,
        )
        return single, multi, new_history, (
            400,
            {
                "ok": False,
                "error": "rejected",
                "detail": authorization_err_multi,
            },
        )

    sync_target_multi = _planned_multi_oracle_sync_target(state=multi, tag=tag, args=args)
    if sync_target_multi is not None:
        sync_err = _check_perp_oracle_sync(price_e8=sync_target_multi[0], epoch=sync_target_multi[1])
        if sync_err is not None:
            new_history = _history_with_entry(
                history,
                mode="multi",
                tag=tag,
                args=args,
                ok=False,
                error=sync_err,
            )
            return single, multi, new_history, (
                400,
                {
                    "ok": False,
                    "error": "rejected",
                    "detail": sync_err,
                },
            )

    cmd_multi = ZUSDMultiCommand(tag=cast(ZUSDCommandTag, tag), args=args)
    result_multi = step_multi_with_tau(multi, cmd_multi, config=tau_cfg)
    new_history = _history_with_entry(
        history,
        mode="multi",
        tag=tag,
        args=args,
        ok=result_multi.ok,
        error=result_multi.error,
    )
    if not result_multi.ok or result_multi.state is None:
        return single, multi, new_history, (
            400,
            {
                "ok": False,
                "error": "rejected",
                "detail": result_multi.error or "step rejected",
            },
        )
    return single, result_multi.state, new_history, (
        200,
        {
            "ok": True,
            "mode": "multi",
            "state": _multi_state_payload(result_multi.state),
            "effects": dict(result_multi.effects or {}),
            "tauGate": {
                "enabled": tau_cfg.enabled,
                "timeoutS": tau_cfg.timeout_s,
            },
        },
    )


def handle_zusd_request(method: str, path: str, body: Optional[bytes]) -> ResponseT:
    """Route a zUSD API request. Returns (status_code, response_dict)."""
    segments = [s for s in path.split("/") if s]
    if len(segments) < 3 or segments[0] != "api" or segments[1] != "zusd":
        return 404, {"ok": False, "error": "not_found"}

    rest = segments[2:]

    global _demo_single, _demo_multi, _history
    with _lock:
        try:
            if method == "GET":
                return _handle_get(_demo_single, _demo_multi, _history, rest)
            if method == "POST":
                next_single, next_multi, next_history, resp = _handle_post(
                    _demo_single,
                    _demo_multi,
                    _history,
                    rest,
                    body,
                )
                _demo_single = next_single
                _demo_multi = next_multi
                _history = next_history
                return resp
        except Exception:
            return 500, {"ok": False, "error": "internal_error"}

    return 405, {"ok": False, "error": "method_not_allowed"}


def reset_demo_state() -> None:
    """Reset module-level demo state. For tests only."""
    global _demo_single, _demo_multi, _history
    with _lock:
        _demo_single = init_state()
        _demo_multi = init_multi_state()
        _history.clear()
