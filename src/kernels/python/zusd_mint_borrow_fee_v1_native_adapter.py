"""Native (non-interpreter) shell adapter for `zusd_mint_borrow_fee_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/zusd_mint_borrow_fee_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/zusd_mint_borrow_fee_v1.yaml --adapter <this>:make_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


BPS_SCALE = 10_000
E8 = 100_000_000
# Derived from:
# `python3 -m ESSO validate src/kernels/dex/zusd_mint_borrow_fee_v1.yaml`.
IR_HASH = "sha256:13f07960142112df016410ce82160e64891ef1ea52e4e488c84020f3008c31a5"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


def _mul_div_up(a: int, b: int, den: int) -> int:
    return ((a * b) + den - 1) // den


def _decayed_base_rate_bps(*, base_rate_bps: int, now_epoch: int, last_epoch: int, decay_per_epoch_bps: int) -> int:
    elapsed = now_epoch - last_epoch
    decay = decay_per_epoch_bps * elapsed
    if decay > base_rate_bps:
        return 0
    return base_rate_bps - decay


def _effective_fee_bps(*, decayed_base_rate_bps: int, floor_bps: int, max_bps: int) -> int:
    fee_bps = floor_bps + decayed_base_rate_bps
    if fee_bps > max_bps:
        fee_bps = max_bps
    if fee_bps > BPS_SCALE:
        fee_bps = BPS_SCALE
    return fee_bps


def _mcr_ok(*, collateral_e8: int, debt_e8: int, price_e8: int, mcr_bps: int) -> bool:
    return (collateral_e8 * price_e8 * BPS_SCALE) >= (debt_e8 * mcr_bps * E8)


@dataclass
class ZUSDMintBorrowFeeV1NativeAdapter:
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


def _handle_apply_mint_borrow_fee(adapter: ZUSDMintBorrowFeeV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    args = dict(getattr(command, "args", {}) or {})
    action_id = "apply_mint_borrow_fee"

    amount_e8 = int(args["amount_e8"])
    now_epoch = int(s["now_epoch"])
    price_e8 = int(s["price_e8"])
    collateral_e8 = int(s["collateral_e8"])
    debt_e8 = int(s["debt_e8"])
    free_debt_e8 = int(s["free_debt_e8"])
    max_debt_e8 = int(s["max_debt_e8"])
    max_debt_supply_e8 = int(s["max_debt_supply_e8"])
    mcr_bps = int(s["mcr_bps"])
    min_debt_open_e8 = int(s["min_debt_open_e8"])
    base_rate_bps = int(s["base_rate_bps"])
    base_rate_last_epoch = int(s["base_rate_last_epoch"])
    base_rate_decay_per_epoch_bps = int(s["base_rate_decay_per_epoch_bps"])
    base_rate_borrow_bump_bps = int(s["base_rate_borrow_bump_bps"])
    borrow_fee_floor_bps = int(s["borrow_fee_floor_bps"])
    borrow_fee_max_bps = int(s["borrow_fee_max_bps"])

    if debt_e8 == 0 and amount_e8 < min_debt_open_e8:
        return _guard_false(action_id)

    decayed_base_rate_bps = _decayed_base_rate_bps(
        base_rate_bps=base_rate_bps,
        now_epoch=now_epoch,
        last_epoch=base_rate_last_epoch,
        decay_per_epoch_bps=base_rate_decay_per_epoch_bps,
    )
    fee_bps = _effective_fee_bps(
        decayed_base_rate_bps=decayed_base_rate_bps,
        floor_bps=borrow_fee_floor_bps,
        max_bps=borrow_fee_max_bps,
    )
    fee_e8 = _mul_div_up(amount_e8, fee_bps, BPS_SCALE)
    debt_delta_e8 = amount_e8 + fee_e8
    post_debt_e8 = debt_e8 + debt_delta_e8
    post_free_debt_e8 = free_debt_e8 + debt_delta_e8
    post_base_rate_bps = decayed_base_rate_bps + base_rate_borrow_bump_bps
    if post_base_rate_bps > BPS_SCALE:
        post_base_rate_bps = BPS_SCALE

    if post_debt_e8 > max_debt_e8:
        return _guard_false(action_id)
    if post_free_debt_e8 > max_debt_supply_e8:
        return _guard_false(action_id)
    if not _mcr_ok(collateral_e8=collateral_e8, debt_e8=post_debt_e8, price_e8=price_e8, mcr_bps=mcr_bps):
        return _guard_false(action_id)

    post = dict(s)
    post["debt_e8"] = post_debt_e8
    post["free_debt_e8"] = post_free_debt_e8
    post["base_rate_bps"] = post_base_rate_bps
    post["base_rate_last_epoch"] = now_epoch

    effects = {
        "principal_e8": int(amount_e8),
        "mint_fee_e8": int(fee_e8),
        "mint_fee_bps": int(fee_bps),
        "debt_delta_e8": int(debt_delta_e8),
        "debt_after_e8": int(post_debt_e8),
        "free_debt_after_e8": int(post_free_debt_e8),
        "decayed_base_rate_bps": int(decayed_base_rate_bps),
        "base_rate_after_bps": int(post_base_rate_bps),
        "base_rate_last_epoch_after": int(now_epoch),
        "mcr_post_ok": True,
    }
    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: ZUSDMintBorrowFeeV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ZUSDMintBorrowFeeV1NativeAdapter, Any], Any]] = {
    "apply_mint_borrow_fee": _handle_apply_mint_borrow_fee,
}

EFFECT_HANDLERS: dict[str, Callable[[ZUSDMintBorrowFeeV1NativeAdapter, str, Any], None]] = {
    "principal_e8": _commit_effect,
    "mint_fee_e8": _commit_effect,
    "mint_fee_bps": _commit_effect,
    "debt_delta_e8": _commit_effect,
    "debt_after_e8": _commit_effect,
    "free_debt_after_e8": _commit_effect,
    "decayed_base_rate_bps": _commit_effect,
    "base_rate_after_bps": _commit_effect,
    "base_rate_last_epoch_after": _commit_effect,
    "mcr_post_ok": _commit_effect,
}


def make_adapter(ir: Any) -> ZUSDMintBorrowFeeV1NativeAdapter:
    return ZUSDMintBorrowFeeV1NativeAdapter(ir=ir)
