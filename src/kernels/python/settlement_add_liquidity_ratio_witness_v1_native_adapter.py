"""Native (non-interpreter) shell adapter for `settlement_add_liquidity_ratio_witness_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/settlement_add_liquidity_ratio_witness_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/settlement_add_liquidity_ratio_witness_v1.yaml --adapter <this>:make_adapter

This adapter exists to:
  - pin down ADD_LIQUIDITY ratio selection as a small, replayable primitive
  - check wiring/effects determinism end-to-end vs ESSO interpreter semantics
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bind this adapter to the exact kernel spec version (fail-closed by default).
# Derived from: `python3 -m ESSO validate src/kernels/dex/settlement_add_liquidity_ratio_witness_v1.yaml`.
IR_HASH = "sha256:a683169f39cf57ed0dad10cecd4f7d415e2dbd121e4f3fe32ab5bb8e6a9f6604"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class SettlementAddLiquidityRatioWitnessV1NativeAdapter:
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
            from ESSO.kernel.interpreter import StepError  # type: ignore

            return StepError(code="UnknownAction", message="no handler for command.tag")

        res = handler(self, command)
        from ESSO.kernel.interpreter import StepOk  # type: ignore

        if isinstance(res, StepOk):
            self._state = dict(res.state)
            for eff_id, value in res.effects.items():
                eff_handler = EFFECT_HANDLERS.get(str(eff_id))
                if eff_handler is None:
                    continue
                eff_handler(self, str(eff_id), value)
        return res

    def drain_effects(self) -> Mapping[str, Any]:
        out = dict(self._pending_effects)
        self._pending_effects = {}
        return out


def _handle_bind_add_liquidity_ratio(
    adapter: SettlementAddLiquidityRatioWitnessV1NativeAdapter, command: Any
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    args = dict(getattr(command, "args", {}) or {})

    pool_active = int(s["pool_active"])
    reserve0 = int(s["reserve0"])
    reserve1 = int(s["reserve1"])

    desired0 = int(args["amount0_desired"])
    desired1 = int(args["amount1_desired"])
    used0 = int(args["amount0_used"])
    used1 = int(args["amount1_used"])
    refund0 = int(args["amount0_refund"])
    refund1 = int(args["amount1_refund"])

    action_id = "bind_add_liquidity_ratio"

    if pool_active != 1:
        return _guard_false(action_id)
    if used0 > desired0 or used1 > desired1:
        return _guard_false(action_id)
    if refund0 != desired0 - used0:
        return _guard_false(action_id)
    if refund1 != desired1 - used1:
        return _guard_false(action_id)

    lhs = desired0 * reserve1
    rhs = desired1 * reserve0
    left_branch = lhs <= rhs

    if left_branch:
        if used0 != desired0:
            return _guard_false(action_id)
        if used1 != (desired0 * reserve1) // reserve0:
            return _guard_false(action_id)
    else:
        if used1 != desired1:
            return _guard_false(action_id)
        if used0 != (desired1 * reserve0) // reserve1:
            return _guard_false(action_id)

    effects = {
        "amount0_used": int(used0),
        "amount1_used": int(used1),
        "amount0_refund": int(refund0),
        "amount1_refund": int(refund1),
        "binding_ok": 1,
        "left_branch": bool(left_branch),
    }
    return StepOk(state=dict(s), effects=effects)


def _commit_effect(adapter: SettlementAddLiquidityRatioWitnessV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[SettlementAddLiquidityRatioWitnessV1NativeAdapter, Any], Any]] = {
    "bind_add_liquidity_ratio": _handle_bind_add_liquidity_ratio,
}

EFFECT_HANDLERS: dict[str, Callable[[SettlementAddLiquidityRatioWitnessV1NativeAdapter, str, Any], None]] = {
    "amount0_used": _commit_effect,
    "amount1_used": _commit_effect,
    "amount0_refund": _commit_effect,
    "amount1_refund": _commit_effect,
    "binding_ok": _commit_effect,
    "left_branch": _commit_effect,
}


def make_adapter(ir: Any) -> SettlementAddLiquidityRatioWitnessV1NativeAdapter:
    return SettlementAddLiquidityRatioWitnessV1NativeAdapter(ir=ir)
