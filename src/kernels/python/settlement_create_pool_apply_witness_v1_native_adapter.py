"""Native (non-interpreter) shell adapter for `settlement_create_pool_apply_witness_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/settlement_create_pool_apply_witness_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/settlement_create_pool_apply_witness_v1.yaml --adapter <this>:make_adapter

This adapter exists to:
  - pin down CREATE_POOL settlement math as a small, replayable primitive
  - check wiring/effects determinism end-to-end vs ESSO interpreter semantics
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Bind this adapter to the exact kernel spec version (fail-closed by default).
# Derived from: `python3 -m ESSO validate src/kernels/dex/settlement_create_pool_apply_witness_v1.yaml`.
IR_HASH = "sha256:5f3f7b9a42f6bd646305a5020807f0bddefe1049430b6bf9033657e77a2a069e"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class SettlementCreatePoolApplyWitnessV1NativeAdapter:
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


def _handle_create_pool_apply(adapter: SettlementCreatePoolApplyWitnessV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    args = dict(getattr(command, "args", {}) or {})

    pool_initialized = int(s["pool_initialized"])
    creator_asset0 = int(s["creator_asset0"])
    creator_asset1 = int(s["creator_asset1"])
    creator_lp = int(s["creator_lp"])
    lock_lp = int(s["lock_lp"])
    reserve0 = int(s["reserve0"])
    reserve1 = int(s["reserve1"])
    lp_supply = int(s["lp_supply"])

    amount0 = int(args["amount0"])
    amount1 = int(args["amount1"])
    fee_bps = int(args["fee_bps"])
    sqrt_product = int(args["sqrt_product"])

    action_id = "create_pool_apply"

    if pool_initialized != 0:
        return _guard_false(action_id)
    if reserve0 != 0 or reserve1 != 0:
        return _guard_false(action_id)
    if creator_lp != 0 or lock_lp != 0 or lp_supply != 0:
        return _guard_false(action_id)
    if creator_asset0 < amount0 or creator_asset1 < amount1:
        return _guard_false(action_id)
    if fee_bps < 0 or fee_bps > 10_000:
        return _guard_false(action_id)
    if sqrt_product * sqrt_product > amount0 * amount1:
        return _guard_false(action_id)
    if amount0 * amount1 >= (sqrt_product + 1) * (sqrt_product + 1):
        return _guard_false(action_id)
    if sqrt_product <= 1000:
        return _guard_false(action_id)

    lp_minted = sqrt_product - 1000
    post = dict(s)
    post["pool_initialized"] = 1
    post["creator_asset0"] = creator_asset0 - amount0
    post["creator_asset1"] = creator_asset1 - amount1
    post["creator_lp"] = lp_minted
    post["lock_lp"] = 1000
    post["reserve0"] = amount0
    post["reserve1"] = amount1
    post["lp_supply"] = sqrt_product

    effects = {
        "amount0_used": int(amount0),
        "amount1_used": int(amount1),
        "lp_minted": int(lp_minted),
        "reserve0_after": int(amount0),
        "reserve1_after": int(amount1),
        "lp_supply_after": int(sqrt_product),
        "witness_ok": bool(
            sqrt_product * sqrt_product <= amount0 * amount1
            and amount0 * amount1 < (sqrt_product + 1) * (sqrt_product + 1)
        ),
        "balance_delta_ok": 1,
        "reserve_delta_ok": 1,
        "lp_delta_ok": 1,
    }

    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: SettlementCreatePoolApplyWitnessV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[SettlementCreatePoolApplyWitnessV1NativeAdapter, Any], Any]] = {
    "create_pool_apply": _handle_create_pool_apply,
}

EFFECT_HANDLERS: dict[str, Callable[[SettlementCreatePoolApplyWitnessV1NativeAdapter, str, Any], None]] = {
    "amount0_used": _commit_effect,
    "amount1_used": _commit_effect,
    "lp_minted": _commit_effect,
    "reserve0_after": _commit_effect,
    "reserve1_after": _commit_effect,
    "lp_supply_after": _commit_effect,
    "witness_ok": _commit_effect,
    "balance_delta_ok": _commit_effect,
    "reserve_delta_ok": _commit_effect,
    "lp_delta_ok": _commit_effect,
}


def make_adapter(ir: Any) -> SettlementCreatePoolApplyWitnessV1NativeAdapter:
    return SettlementCreatePoolApplyWitnessV1NativeAdapter(ir=ir)
