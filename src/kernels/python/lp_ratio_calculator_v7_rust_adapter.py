"""Rust-backed ESSO shell adapter for `lp_ratio_calculator_v7`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/lp_ratio_calculator_v7.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/lp_ratio_calculator_v7.yaml --adapter <this>:make_adapter

The adapter binds the ESSO ratio model to the Rust `lp_math_v7` CLI surface.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from .lp_math_v7_rust_adapter_common import is_rust_ok, run_rust_lp_math


IR_HASH = "sha256:33a238faeee9e52207e1114d98488f98e974881af6a825566fef2e0e59672b0c"


def _step_error(code: str, message: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code=code, message=message)


def _guard_false(action_id: str) -> Any:
    return _step_error("GuardFalse", f"guard false for action '{action_id}'")


@dataclass
class LpRatioCalculatorV7RustAdapter:
    ir: Any
    _state: dict[str, Any] = field(default_factory=dict)
    _pending_effects: dict[str, Any] = field(default_factory=dict)

    def reset(self, *, state: Mapping[str, Any]) -> None:
        self._state = dict(state)
        self._pending_effects = {}

    def get_state(self) -> Mapping[str, Any]:
        return dict(self._state)

    def apply(self, command: Any) -> Any:
        self._pending_effects = {}
        handler = ACTION_HANDLERS.get(str(getattr(command, "tag", "")))
        if handler is None:
            return _step_error("UnknownAction", "no handler for command.tag")

        res = handler(self, command)
        from ESSO.kernel.interpreter import StepOk  # type: ignore

        if isinstance(res, StepOk):
            self._state = dict(res.state)
            for eff_id, value in res.effects.items():
                eff_handler = EFFECT_HANDLERS.get(str(eff_id))
                if eff_handler is not None:
                    eff_handler(self, str(eff_id), value)
        return res

    def drain_effects(self) -> Mapping[str, Any]:
        out = dict(self._pending_effects)
        self._pending_effects = {}
        return out


def _handle_calculate_optimal(adapter: LpRatioCalculatorV7RustAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    action_id = "calculate_optimal"
    state = adapter._state
    args = dict(getattr(command, "args", {}) or {})
    reserve0 = int(state["reserve0"])
    reserve1 = int(state["reserve1"])
    desired0 = int(args["desired0"])
    desired1 = int(args["desired1"])

    if not ((reserve0 == 0 and reserve1 == 0) or (reserve0 > 0 and reserve1 > 0)):
        return _guard_false(action_id)

    payload = run_rust_lp_math("optimal", reserve0, reserve1, desired0, desired1)
    if not is_rust_ok(payload):
        return _guard_false(action_id)
    result = dict(payload["result"])

    amount0_used = int(result["amount0_used"])
    amount1_used = int(result["amount1_used"])
    refund0 = int(result["amount0_refund"])
    refund1 = int(result["amount1_refund"])
    is_initial = bool(reserve0 == 0 and reserve1 == 0)
    effects = {
        "is_initial": is_initial,
        "optimal0": amount0_used,
        "optimal1": amount1_used,
        "refund0": refund0,
        "refund1": refund1,
        "refund0_nonneg": bool(refund0 >= 0),
        "refund1_nonneg": bool(refund1 >= 0),
        "optimal0_le_desired0": bool(amount0_used <= desired0),
        "optimal1_le_desired1": bool(amount1_used <= desired1),
        "sum0_ok": bool(amount0_used + refund0 == desired0),
        "sum1_ok": bool(amount1_used + refund1 == desired1),
    }
    return StepOk(state=dict(state), effects=effects)


def _commit_effect(adapter: LpRatioCalculatorV7RustAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[LpRatioCalculatorV7RustAdapter, Any], Any]] = {
    "calculate_optimal": _handle_calculate_optimal,
}

EFFECT_HANDLERS: dict[str, Callable[[LpRatioCalculatorV7RustAdapter, str, Any], None]] = {
    "is_initial": _commit_effect,
    "optimal0": _commit_effect,
    "optimal1": _commit_effect,
    "refund0": _commit_effect,
    "refund1": _commit_effect,
    "refund0_nonneg": _commit_effect,
    "refund1_nonneg": _commit_effect,
    "optimal0_le_desired0": _commit_effect,
    "optimal1_le_desired1": _commit_effect,
    "sum0_ok": _commit_effect,
    "sum1_ok": _commit_effect,
}


def make_adapter(ir: Any) -> LpRatioCalculatorV7RustAdapter:
    return LpRatioCalculatorV7RustAdapter(ir=ir)
