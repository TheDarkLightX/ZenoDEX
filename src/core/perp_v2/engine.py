"""Dispatch-table engine for `perp_v2`.

``step(state, params)`` is the single entry point. It:

1. Validates parameter domains (from YAML type bounds).
2. Dispatches to the correct guard / update / effect functions.
3. Checks all invariants on the post-state.
4. Returns a ``StepResult`` (accepted or rejected with reason).

The authoritative spec is `src/kernels/dex/perp_epoch_isolated_v2.yaml`; keep
this module in sync and use parity tests against generated refs when updating.
"""

from __future__ import annotations

from typing import Callable

from .effects import (
    effect_advance_epoch,
    effect_apply_funding,
    effect_apply_insurance_claim,
    effect_clear_breaker,
    effect_deposit_collateral,
    effect_deposit_insurance,
    effect_publish_clearing_price,
    effect_set_position,
    effect_settle_epoch,
    effect_withdraw_collateral,
)
from .guards import (
    guard_advance_epoch,
    guard_apply_funding,
    guard_apply_insurance_claim,
    guard_clear_breaker,
    guard_deposit_collateral,
    guard_deposit_insurance,
    guard_publish_clearing_price,
    guard_set_position,
    guard_settle_epoch,
    guard_withdraw_collateral,
)
from .errors import PerpGuardError, PerpInvariantError, PerpOverflowError
from .invariants import check_all
from .types import Action, ActionParams, Effect, PerpState, StepResult
from .updates import (
    apply_advance_epoch,
    apply_clear_breaker,
    apply_deposit_collateral,
    apply_deposit_insurance,
    apply_funding,
    apply_insurance_claim,
    apply_publish_clearing_price,
    apply_set_position,
    apply_settle_epoch,
    apply_withdraw_collateral,
)

GuardFn = Callable[[PerpState, ActionParams], bool]
UpdateFn = Callable[[PerpState, ActionParams], PerpState]
EffectFn = Callable[[PerpState, ActionParams], Effect]

_DISPATCH: dict[Action, tuple[GuardFn, UpdateFn, EffectFn]] = {
    Action.ADVANCE_EPOCH: (
        guard_advance_epoch, apply_advance_epoch, effect_advance_epoch,
    ),
    Action.PUBLISH_CLEARING_PRICE: (
        guard_publish_clearing_price, apply_publish_clearing_price, effect_publish_clearing_price,
    ),
    Action.SETTLE_EPOCH: (
        guard_settle_epoch, apply_settle_epoch, effect_settle_epoch,
    ),
    Action.DEPOSIT_COLLATERAL: (
        guard_deposit_collateral, apply_deposit_collateral, effect_deposit_collateral,
    ),
    Action.WITHDRAW_COLLATERAL: (
        guard_withdraw_collateral, apply_withdraw_collateral, effect_withdraw_collateral,
    ),
    Action.SET_POSITION: (
        guard_set_position, apply_set_position, effect_set_position,
    ),
    Action.CLEAR_BREAKER: (
        guard_clear_breaker, apply_clear_breaker, effect_clear_breaker,
    ),
    Action.APPLY_FUNDING: (
        guard_apply_funding, apply_funding, effect_apply_funding,
    ),
    Action.DEPOSIT_INSURANCE: (
        guard_deposit_insurance, apply_deposit_insurance, effect_deposit_insurance,
    ),
    Action.APPLY_INSURANCE_CLAIM: (
        guard_apply_insurance_claim, apply_insurance_claim, effect_apply_insurance_claim,
    ),
}

# -- Parameter domain bounds (from YAML param type specs) --------------------

MAX_PARAM_AMOUNT: int = 1_000_000_000_000  # shared max for amounts/prices
MAX_DELTA: int = 10_000
MAX_POSITION: int = 1_000_000
MAX_RATE_BPS: int = 10_000

# Per-action bounds: list of (field_name, min_val, max_val).
_PARAM_BOUNDS: dict[Action, list[tuple[str, int, int]]] = {
    Action.ADVANCE_EPOCH: [
        ("delta", 1, MAX_DELTA),
    ],
    Action.PUBLISH_CLEARING_PRICE: [
        ("price_e8", 1, MAX_PARAM_AMOUNT),
    ],
    Action.SETTLE_EPOCH: [],
    Action.DEPOSIT_COLLATERAL: [
        ("amount", 1, MAX_PARAM_AMOUNT),
    ],
    Action.WITHDRAW_COLLATERAL: [
        ("amount", 1, MAX_PARAM_AMOUNT),
    ],
    Action.SET_POSITION: [
        ("new_position_base", -MAX_POSITION, MAX_POSITION),
    ],
    Action.CLEAR_BREAKER: [],
    Action.APPLY_FUNDING: [
        ("new_rate_bps", -MAX_RATE_BPS, MAX_RATE_BPS),
    ],
    Action.DEPOSIT_INSURANCE: [
        ("amount", 1, MAX_PARAM_AMOUNT),
    ],
    Action.APPLY_INSURANCE_CLAIM: [
        ("claim_amount", 1, MAX_PARAM_AMOUNT),
    ],
}


def _validate_params(params: ActionParams) -> str | None:
    """Check parameter domain bounds. Returns rejection reason or None."""
    bounds = _PARAM_BOUNDS.get(params.action)
    if bounds is None:
        return None
    for field, lo, hi in bounds:
        val = getattr(params, field)
        if val < lo or val > hi:
            return f"param_domain:{field}"
    return None


def step(state: PerpState, params: ActionParams) -> StepResult:
    """Execute one action against the given state.

    Returns ``StepResult`` with ``accepted=True`` on success,
    or ``accepted=False`` with a ``rejection`` reason string.
    """
    entry = _DISPATCH.get(params.action)
    if entry is None:
        return StepResult(accepted=False, rejection=f"unknown_action:{params.action}")

    domain_err = _validate_params(params)
    if domain_err is not None:
        return StepResult(accepted=False, rejection=domain_err)

    guard_fn, update_fn, effect_fn = entry

    if not guard_fn(state, params):
        return StepResult(accepted=False, rejection="guard")

    new_state = update_fn(state, params)

    violations = check_all(new_state)
    if violations:
        return StepResult(
            accepted=False,
            rejection=f"invariant:{','.join(violations)}",
        )

    effect = effect_fn(new_state, params)
    return StepResult(accepted=True, state=new_state, effect=effect)


def step_or_raise(state: PerpState, params: ActionParams) -> StepResult:
    """Like ``step()`` but raises on rejection instead of returning a result.

    Raises:
        PerpOverflowError: Parameter outside YAML domain bounds.
        PerpGuardError: Guard condition not satisfied.
        PerpInvariantError: Post-state violates one or more invariants.
    """
    result = step(state, params)
    if result.accepted:
        return result

    reason = result.rejection or ""
    if reason.startswith("param_domain:"):
        raise PerpOverflowError(reason)
    if reason.startswith("invariant:"):
        violations = reason.removeprefix("invariant:").split(",")
        raise PerpInvariantError(violations)
    raise PerpGuardError(reason)
