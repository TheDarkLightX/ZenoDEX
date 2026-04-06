"""Native (non-interpreter) shell adapter for `zusd_liquidation_sp_absorb_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/zusd_liquidation_sp_absorb_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/zusd_liquidation_sp_absorb_v1.yaml --adapter <this>:make_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


BPS_SCALE = 10_000
E8 = 100_000_000
# Derived from:
# `python3 -m ESSO validate src/kernels/dex/zusd_liquidation_sp_absorb_v1.yaml`.
IR_HASH = "sha256:83c108590a245103c131bb3f8c3c36f5b5ace3b2681b1ce469399c8119f14a29"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


def _under_mcr(*, collateral_e8: int, debt_e8: int, price_pending_e8: int, mcr_bps: int) -> bool:
    return (collateral_e8 * price_pending_e8 * BPS_SCALE) < (debt_e8 * mcr_bps * E8)


@dataclass
class ZUSDLiquidationSPAbsorbV1NativeAdapter:
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


def _handle_apply_liquidation_sp_absorb(adapter: ZUSDLiquidationSPAbsorbV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    action_id = "apply_liquidation_sp_absorb"

    price_pending_e8 = int(s["price_pending_e8"])
    collateral_e8 = int(s["collateral_e8"])
    debt_e8 = int(s["debt_e8"])
    sp_debt_e8 = int(s["sp_debt_e8"])
    sp_coll_e8 = int(s["sp_coll_e8"])
    max_sp_coll_e8 = int(s["max_sp_coll_e8"])
    mcr_bps = int(s["mcr_bps"])

    if debt_e8 <= 0:
        return _guard_false(action_id)
    if not _under_mcr(
        collateral_e8=collateral_e8,
        debt_e8=debt_e8,
        price_pending_e8=price_pending_e8,
        mcr_bps=mcr_bps,
    ):
        return _guard_false(action_id)
    if debt_e8 > sp_debt_e8:
        return _guard_false(action_id)
    if sp_coll_e8 + collateral_e8 > max_sp_coll_e8:
        return _guard_false(action_id)

    post = dict(s)
    post["debt_before"] = debt_e8
    post["collateral_before"] = collateral_e8
    post["debt_e8"] = 0
    post["collateral_e8"] = 0
    post["sp_debt_e8"] = sp_debt_e8 - debt_e8
    post["sp_coll_e8"] = sp_coll_e8 + collateral_e8

    effects = {
        "liquidated_debt_e8": int(debt_e8),
        "liquidated_collateral_e8": int(collateral_e8),
        "sp_debt_after": int(post["sp_debt_e8"]),
        "sp_coll_after": int(post["sp_coll_e8"]),
        "under_mcr": True,
    }
    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: ZUSDLiquidationSPAbsorbV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ZUSDLiquidationSPAbsorbV1NativeAdapter, Any], Any]] = {
    "apply_liquidation_sp_absorb": _handle_apply_liquidation_sp_absorb,
}

EFFECT_HANDLERS: dict[str, Callable[[ZUSDLiquidationSPAbsorbV1NativeAdapter, str, Any], None]] = {
    "liquidated_debt_e8": _commit_effect,
    "liquidated_collateral_e8": _commit_effect,
    "sp_debt_after": _commit_effect,
    "sp_coll_after": _commit_effect,
    "under_mcr": _commit_effect,
}


def make_adapter(ir: Any) -> ZUSDLiquidationSPAbsorbV1NativeAdapter:
    return ZUSDLiquidationSPAbsorbV1NativeAdapter(ir=ir)
