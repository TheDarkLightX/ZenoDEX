"""REST API handlers for zUSD endpoints (DEMO / DEVELOPMENT ONLY).

Pure stdlib module -- no third-party dependencies.
Imported lazily by ``api_server.py`` when a ``/api/zusd/`` path is hit.

This module intentionally keeps mutable demo state in-memory and is not the
production transaction path.
"""

from __future__ import annotations

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
    ZUSDVault,
    init_multi_state,
    init_state,
)
from .zusd_oracle_contracts import (
    ZUSDCrossModuleOracleSyncContract,
    ZUSDOraclePendingGateContract,
    build_zusd_cross_module_oracle_sync_contract,
    build_zusd_oracle_pending_gate_contract,
    verify_zusd_cross_module_oracle_sync_contract_payload,
    verify_zusd_oracle_pending_gate_contract_payload,
)
from .zusd_oracle_recovery_lifecycle import (
    build_zusd_oracle_recovery_lifecycle_packet,
    verify_zusd_oracle_recovery_lifecycle_packet_payload,
)
from .zusd_tau_gate import ZUSDTauGateConfig, step_multi_with_tau, step_with_tau

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


def _parse_zusd_state_payload(payload: object) -> ZUSDState | ZUSDMultiState:
    if not isinstance(payload, Mapping):
        raise ValueError("state must be an object")
    if "vault_a" in payload or "vault_b" in payload:
        vault_a_raw = payload.get("vault_a")
        vault_b_raw = payload.get("vault_b")
        if not isinstance(vault_a_raw, Mapping) or not isinstance(vault_b_raw, Mapping):
            raise ValueError("multi-state requires vault_a and vault_b objects")
        vault_a = ZUSDVault(
            collateral_e8=int(vault_a_raw.get("collateral_e8", 0)),
            debt_e8=int(vault_a_raw.get("debt_e8", 0)),
        )
        vault_b = ZUSDVault(
            collateral_e8=int(vault_b_raw.get("collateral_e8", 0)),
            debt_e8=int(vault_b_raw.get("debt_e8", 0)),
        )
        kwargs = dict(payload)
        kwargs["vault_a"] = vault_a
        kwargs["vault_b"] = vault_b
        return ZUSDMultiState(**kwargs)
    return ZUSDState(**dict(payload))


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
    if rest == ["build_oracle_pending_gate_contract"]:
        parsed, err = _parse_json_body(body)
        if err is not None:
            return single, multi, history, (400, {"ok": False, "error": err})
        if parsed is None:
            return single, multi, history, (400, {"ok": False, "error": "bad_json"})
        try:
            state = _parse_zusd_state_payload(parsed.get("state"))
            contract = build_zusd_oracle_pending_gate_contract(
                state,
                risky_requested=bool(parsed.get("risky_requested", False)),
                max_staleness_epochs=int(parsed.get("max_staleness_epochs", 100)),
                tcr_ok=bool(parsed.get("tcr_ok", True)),
            )
            return single, multi, history, (200, {"ok": True, "contract": contract.to_dict()})
        except Exception as exc:
            return single, multi, history, (
                400,
                {"ok": False, "error": "build_oracle_pending_gate_contract_error", "detail": str(exc)},
            )

    if rest == ["verify_oracle_pending_gate_contract"]:
        parsed, err = _parse_json_body(body)
        if err is not None:
            return single, multi, history, (400, {"ok": False, "error": err})
        if parsed is None or not isinstance(parsed.get("contract"), dict):
            return single, multi, history, (400, {"ok": False, "error": "bad_contract"})
        ok, verify_err = verify_zusd_oracle_pending_gate_contract_payload(parsed["contract"])
        return single, multi, history, (200, {"ok": bool(ok), "error": verify_err})

    if rest == ["build_cross_module_oracle_sync_contract"]:
        parsed, err = _parse_json_body(body)
        if err is not None:
            return single, multi, history, (400, {"ok": False, "error": err})
        if parsed is None:
            return single, multi, history, (400, {"ok": False, "error": "bad_json"})
        try:
            contract = build_zusd_cross_module_oracle_sync_contract(
                market_id=str(parsed.get("market_id", "")),
                zusd_price_e8=int(parsed.get("zusd_price_e8", 0)),
                zusd_epoch=int(parsed.get("zusd_epoch", 0)),
                perp_price_e8=int(parsed.get("perp_price_e8", 0)),
                perp_oracle_epoch=int(parsed.get("perp_oracle_epoch", 0)),
                max_divergence_bps=int(parsed.get("max_divergence_bps", 0)),
                max_epoch_lag=int(parsed.get("max_epoch_lag", 0)),
            )
            return single, multi, history, (200, {"ok": True, "contract": contract.to_dict()})
        except Exception as exc:
            return single, multi, history, (
                400,
                {"ok": False, "error": "build_cross_module_oracle_sync_contract_error", "detail": str(exc)},
            )

    if rest == ["verify_cross_module_oracle_sync_contract"]:
        parsed, err = _parse_json_body(body)
        if err is not None:
            return single, multi, history, (400, {"ok": False, "error": err})
        if parsed is None or not isinstance(parsed.get("contract"), dict):
            return single, multi, history, (400, {"ok": False, "error": "bad_contract"})
        ok, verify_err = verify_zusd_cross_module_oracle_sync_contract_payload(parsed["contract"])
        return single, multi, history, (200, {"ok": bool(ok), "error": verify_err})

    if rest == ["build_oracle_recovery_lifecycle_packet"]:
        parsed, err = _parse_json_body(body)
        if err is not None:
            return single, multi, history, (400, {"ok": False, "error": err})
        if parsed is None:
            return single, multi, history, (400, {"ok": False, "error": "bad_json"})
        try:
            previous_pending = ZUSDOraclePendingGateContract.from_dict(parsed.get("previous_pending_gate_contract"))
            current_pending = ZUSDOraclePendingGateContract.from_dict(parsed.get("current_pending_gate_contract"))
            current_sync = ZUSDCrossModuleOracleSyncContract.from_dict(parsed.get("current_sync_contract"))
            packet = build_zusd_oracle_recovery_lifecycle_packet(
                previous_pending_gate_contract=previous_pending,
                current_pending_gate_contract=current_pending,
                current_sync_contract=current_sync,
            )
            return single, multi, history, (200, {"ok": True, "packet": packet.to_dict()})
        except Exception as exc:
            return single, multi, history, (
                400,
                {"ok": False, "error": "build_oracle_recovery_lifecycle_packet_error", "detail": str(exc)},
            )

    if rest == ["verify_oracle_recovery_lifecycle_packet"]:
        parsed, err = _parse_json_body(body)
        if err is not None:
            return single, multi, history, (400, {"ok": False, "error": err})
        if parsed is None or not isinstance(parsed.get("packet"), dict):
            return single, multi, history, (400, {"ok": False, "error": "bad_packet"})
        ok, verify_err = verify_zusd_oracle_recovery_lifecycle_packet_payload(parsed["packet"])
        return single, multi, history, (200, {"ok": bool(ok), "error": verify_err})

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
