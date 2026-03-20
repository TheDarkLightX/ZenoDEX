"""Native (non-interpreter) shell adapter for `settlement_remove_liquidity_apply_witness_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/settlement_remove_liquidity_apply_witness_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/settlement_remove_liquidity_apply_witness_v1.yaml --adapter <this>:make_adapter

This adapter exists to:
  - pin down REMOVE_LIQUIDITY settlement math as a small, replayable primitive
  - check wiring/effects determinism end-to-end vs ESSO interpreter semantics
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bind this adapter to the exact kernel spec version (fail-closed by default).
# Derived from: `python3 -m ESSO validate src/kernels/dex/settlement_remove_liquidity_apply_witness_v1.yaml`.
IR_HASH = "sha256:779d27ade779c391eb365017165d3ece440e24623cb9f8aaa8390442c9c582ee"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class SettlementRemoveLiquidityApplyWitnessV1NativeAdapter:
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


def _handle_remove_liquidity_apply(adapter: SettlementRemoveLiquidityApplyWitnessV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    args = dict(getattr(command, "args", {}) or {})

    pool_active = int(s["pool_active"])
    recipient_asset0 = int(s["recipient_asset0"])
    recipient_asset1 = int(s["recipient_asset1"])
    sender_lp = int(s["sender_lp"])
    reserve0 = int(s["reserve0"])
    reserve1 = int(s["reserve1"])
    lp_supply = int(s["lp_supply"])

    lp_amount = int(args["lp_amount"])
    amount0_min = int(args["amount0_min"])
    amount1_min = int(args["amount1_min"])

    action_id = "remove_liquidity_apply"

    if pool_active != 1:
        return _guard_false(action_id)
    if sender_lp < lp_amount:
        return _guard_false(action_id)
    if lp_amount > lp_supply:
        return _guard_false(action_id)

    amount0_out = (lp_amount * reserve0) // lp_supply
    amount1_out = (lp_amount * reserve1) // lp_supply
    if amount0_out < amount0_min:
        return _guard_false(action_id)
    if amount1_out < amount1_min:
        return _guard_false(action_id)

    post = dict(s)
    post["reserve0_before"] = reserve0
    post["reserve1_before"] = reserve1
    post["lp_supply_before"] = lp_supply
    post["recipient_asset0"] = recipient_asset0 + amount0_out
    post["recipient_asset1"] = recipient_asset1 + amount1_out
    post["sender_lp"] = sender_lp - lp_amount
    post["reserve0"] = reserve0 - amount0_out
    post["reserve1"] = reserve1 - amount1_out
    post["lp_supply"] = lp_supply - lp_amount

    effects = {
        "lp_burned": int(lp_amount),
        "amount0_out": int(amount0_out),
        "amount1_out": int(amount1_out),
        "reserve0_after": int(post["reserve0"]),
        "reserve1_after": int(post["reserve1"]),
        "lp_supply_after": int(post["lp_supply"]),
        "balance_delta_ok": 1,
        "reserve_delta_ok": 1,
        "lp_delta_ok": 1,
    }
    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: SettlementRemoveLiquidityApplyWitnessV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[SettlementRemoveLiquidityApplyWitnessV1NativeAdapter, Any], Any]] = {
    "remove_liquidity_apply": _handle_remove_liquidity_apply,
}

EFFECT_HANDLERS: dict[str, Callable[[SettlementRemoveLiquidityApplyWitnessV1NativeAdapter, str, Any], None]] = {
    "lp_burned": _commit_effect,
    "amount0_out": _commit_effect,
    "amount1_out": _commit_effect,
    "reserve0_after": _commit_effect,
    "reserve1_after": _commit_effect,
    "lp_supply_after": _commit_effect,
    "balance_delta_ok": _commit_effect,
    "reserve_delta_ok": _commit_effect,
    "lp_delta_ok": _commit_effect,
}


def make_adapter(ir: Any) -> SettlementRemoveLiquidityApplyWitnessV1NativeAdapter:
    return SettlementRemoveLiquidityApplyWitnessV1NativeAdapter(ir=ir)
