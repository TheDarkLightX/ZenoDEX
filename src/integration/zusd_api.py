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
from typing import Any, Dict, List, Mapping, Optional, Tuple

from ..core.zusd import (
    ZUSDCommand,
    ZUSDMultiCommand,
    ZUSDMultiState,
    ZUSDState,
    init_multi_state,
    init_state,
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


def _tau_gate_config_from_env() -> ZUSDTauGateConfig:
    return ZUSDTauGateConfig(
        enabled=_bool_env("ZUSD_TAU_GATE_ENABLED", default=True),
        timeout_s=_float_env("ZUSD_TAU_GATE_TIMEOUT_S", 5.0, lo=0.1, hi=120.0),
        tau_bin=(os.environ.get("ZUSD_TAU_BIN", "").strip() or None),
        allow_path_lookup=_bool_env("ZUSD_TAU_ALLOW_PATH_LOOKUP", default=True),
    )


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
    if not isinstance(args, dict):
        return None, None, "invalid_args"
    return tag, args, None


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
    assert parsed is not None

    tag, args, cmd_err = _cmd_from_body(parsed)
    if cmd_err is not None:
        return single, multi, history, (400, {"ok": False, "error": cmd_err})
    assert tag is not None and args is not None

    tau_cfg = _tau_gate_config_from_env()

    if rest == ["step"]:
        cmd = ZUSDCommand(tag=tag, args=args)
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

    cmd_multi = ZUSDMultiCommand(tag=tag, args=args)
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
