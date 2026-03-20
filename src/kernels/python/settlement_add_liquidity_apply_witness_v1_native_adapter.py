"""Native (non-interpreter) shell adapter for `settlement_add_liquidity_apply_witness_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/settlement_add_liquidity_apply_witness_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/settlement_add_liquidity_apply_witness_v1.yaml --adapter <this>:make_adapter

This adapter exists to:
  - pin down ADD_LIQUIDITY settlement apply semantics as a small, replayable primitive
  - check wiring/effects determinism end-to-end vs ESSO interpreter semantics
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bind this adapter to the exact kernel spec version (fail-closed by default).
# Derived from: `python3 -m ESSO validate src/kernels/dex/settlement_add_liquidity_apply_witness_v1.yaml`.
IR_HASH = "sha256:e0c9586b99fbdfcf0b11993e7860e1be7fa73ac75c2965f9a8d8d46096b42940"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class SettlementAddLiquidityApplyWitnessV1NativeAdapter:
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


def _handle_add_liquidity_apply(adapter: SettlementAddLiquidityApplyWitnessV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    args = dict(getattr(command, "args", {}) or {})

    pool_active = int(s["pool_active"])
    sender_asset0 = int(s["sender_asset0"])
    sender_asset1 = int(s["sender_asset1"])
    recipient_lp = int(s["recipient_lp"])
    reserve0 = int(s["reserve0"])
    reserve1 = int(s["reserve1"])
    lp_supply = int(s["lp_supply"])

    amount0_used = int(args["amount0_used"])
    amount1_used = int(args["amount1_used"])
    lp_minted = int(args["lp_minted"])

    action_id = "add_liquidity_apply"

    if pool_active != 1:
        return _guard_false(action_id)
    if sender_asset0 < amount0_used or sender_asset1 < amount1_used:
        return _guard_false(action_id)
    if reserve0 + amount0_used > 3000:
        return _guard_false(action_id)
    if reserve1 + amount1_used > 3000:
        return _guard_false(action_id)
    if recipient_lp + lp_minted > 3000:
        return _guard_false(action_id)
    if lp_supply + lp_minted > 4000:
        return _guard_false(action_id)

    lp_from_amount0 = (amount0_used * lp_supply) // reserve0
    lp_from_amount1 = (amount1_used * lp_supply) // reserve1
    if lp_minted > lp_from_amount0 or lp_minted > lp_from_amount1:
        return _guard_false(action_id)
    if lp_minted != lp_from_amount0 and lp_minted != lp_from_amount1:
        return _guard_false(action_id)

    post = dict(s)
    post["reserve0_before"] = reserve0
    post["reserve1_before"] = reserve1
    post["lp_supply_before"] = lp_supply
    post["sender_asset0"] = sender_asset0 - amount0_used
    post["sender_asset1"] = sender_asset1 - amount1_used
    post["recipient_lp"] = recipient_lp + lp_minted
    post["reserve0"] = reserve0 + amount0_used
    post["reserve1"] = reserve1 + amount1_used
    post["lp_supply"] = lp_supply + lp_minted

    effects = {
        "amount0_used": int(amount0_used),
        "amount1_used": int(amount1_used),
        "lp_minted": int(lp_minted),
        "reserve0_after": int(post["reserve0"]),
        "reserve1_after": int(post["reserve1"]),
        "lp_supply_after": int(post["lp_supply"]),
        "lp_math_ok": bool(
            lp_minted <= lp_from_amount0
            and lp_minted <= lp_from_amount1
            and (lp_minted == lp_from_amount0 or lp_minted == lp_from_amount1)
        ),
        "balance_delta_ok": 1,
        "reserve_delta_ok": 1,
        "lp_delta_ok": 1,
    }
    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: SettlementAddLiquidityApplyWitnessV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[SettlementAddLiquidityApplyWitnessV1NativeAdapter, Any], Any]] = {
    "add_liquidity_apply": _handle_add_liquidity_apply,
}

EFFECT_HANDLERS: dict[str, Callable[[SettlementAddLiquidityApplyWitnessV1NativeAdapter, str, Any], None]] = {
    "amount0_used": _commit_effect,
    "amount1_used": _commit_effect,
    "lp_minted": _commit_effect,
    "reserve0_after": _commit_effect,
    "reserve1_after": _commit_effect,
    "lp_supply_after": _commit_effect,
    "lp_math_ok": _commit_effect,
    "balance_delta_ok": _commit_effect,
    "reserve_delta_ok": _commit_effect,
    "lp_delta_ok": _commit_effect,
}


def make_adapter(ir: Any) -> SettlementAddLiquidityApplyWitnessV1NativeAdapter:
    return SettlementAddLiquidityApplyWitnessV1NativeAdapter(ir=ir)
