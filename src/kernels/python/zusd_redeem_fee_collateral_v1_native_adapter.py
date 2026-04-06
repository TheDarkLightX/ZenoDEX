"""Native (non-interpreter) shell adapter for `zusd_redeem_fee_collateral_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/zusd_redeem_fee_collateral_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/zusd_redeem_fee_collateral_v1.yaml --adapter <this>:make_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


BPS_SCALE = 10_000
E8 = 100_000_000
# Derived from:
# `python3 -m ESSO validate src/kernels/dex/zusd_redeem_fee_collateral_v1.yaml`.
IR_HASH = "sha256:fd361c9dd8a00abb604ab78c2df921c2c085fd974b2feedb4996c91d61b154b0"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


def _mcr_ok(*, collateral_e8: int, debt_e8: int, price_e8: int, mcr_bps: int) -> bool:
    if debt_e8 == 0:
        return True
    return (collateral_e8 * price_e8 * BPS_SCALE) >= (debt_e8 * mcr_bps * E8)


@dataclass
class ZUSDRedeemFeeCollateralV1NativeAdapter:
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


def _handle_apply_redeem_fee_collateral(adapter: ZUSDRedeemFeeCollateralV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    args = dict(getattr(command, "args", {}) or {})
    action_id = "apply_redeem_fee_collateral"

    amount_e8 = int(args["amount_e8"])
    fee_bps = int(args["fee_bps"])
    gross_collateral_e8 = int(args["gross_collateral_e8"])
    redemption_fee_collateral_e8 = int(args["redemption_fee_collateral_e8"])
    collateral_out_e8 = int(args["collateral_out_e8"])

    price_e8 = int(s["price_e8"])
    collateral_e8 = int(s["collateral_e8"])
    debt_e8 = int(s["debt_e8"])
    free_debt_e8 = int(s["free_debt_e8"])
    protocol_collateral_e8 = int(s["protocol_collateral_e8"])
    max_protocol_coll_e8 = int(s["max_protocol_coll_e8"])
    mcr_bps = int(s["mcr_bps"])
    floor_bps = int(s["redemption_fee_floor_bps"])
    max_bps = int(s["redemption_fee_max_bps"])
    decayed_base_rate_bps = int(s["decayed_base_rate_bps"])

    if amount_e8 > debt_e8 or amount_e8 > free_debt_e8:
        return _guard_false(action_id)
    if gross_collateral_e8 != (amount_e8 * E8) // price_e8:
        return _guard_false(action_id)
    if gross_collateral_e8 <= 0 or gross_collateral_e8 > collateral_e8:
        return _guard_false(action_id)

    expected_fee_bps = floor_bps + decayed_base_rate_bps
    if expected_fee_bps > max_bps:
        expected_fee_bps = max_bps
    if expected_fee_bps > BPS_SCALE:
        expected_fee_bps = BPS_SCALE
    if fee_bps != expected_fee_bps:
        return _guard_false(action_id)

    expected_fee_coll = ((gross_collateral_e8 * fee_bps) + (BPS_SCALE - 1)) // BPS_SCALE
    if redemption_fee_collateral_e8 != expected_fee_coll:
        return _guard_false(action_id)
    if redemption_fee_collateral_e8 >= gross_collateral_e8:
        return _guard_false(action_id)
    if collateral_out_e8 != gross_collateral_e8 - redemption_fee_collateral_e8:
        return _guard_false(action_id)
    if protocol_collateral_e8 + redemption_fee_collateral_e8 > max_protocol_coll_e8:
        return _guard_false(action_id)

    post_debt = debt_e8 - amount_e8
    post_collateral = collateral_e8 - gross_collateral_e8
    if not _mcr_ok(collateral_e8=post_collateral, debt_e8=post_debt, price_e8=price_e8, mcr_bps=mcr_bps):
        return _guard_false(action_id)

    post = dict(s)
    post["debt_e8"] = post_debt
    post["free_debt_e8"] = free_debt_e8 - amount_e8
    post["collateral_e8"] = post_collateral
    post["protocol_collateral_e8"] = protocol_collateral_e8 + redemption_fee_collateral_e8

    effects = {
        "redeemed_zusd_e8": int(amount_e8),
        "redeemed_collateral_gross_e8": int(gross_collateral_e8),
        "redeemed_collateral_out_e8": int(collateral_out_e8),
        "redemption_fee_collateral_e8": int(redemption_fee_collateral_e8),
        "redemption_fee_bps": int(fee_bps),
        "mcr_post_ok": True,
    }
    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: ZUSDRedeemFeeCollateralV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ZUSDRedeemFeeCollateralV1NativeAdapter, Any], Any]] = {
    "apply_redeem_fee_collateral": _handle_apply_redeem_fee_collateral,
}

EFFECT_HANDLERS: dict[str, Callable[[ZUSDRedeemFeeCollateralV1NativeAdapter, str, Any], None]] = {
    "redeemed_zusd_e8": _commit_effect,
    "redeemed_collateral_gross_e8": _commit_effect,
    "redeemed_collateral_out_e8": _commit_effect,
    "redemption_fee_collateral_e8": _commit_effect,
    "redemption_fee_bps": _commit_effect,
    "mcr_post_ok": _commit_effect,
}


def make_adapter(ir: Any) -> ZUSDRedeemFeeCollateralV1NativeAdapter:
    return ZUSDRedeemFeeCollateralV1NativeAdapter(ir=ir)
