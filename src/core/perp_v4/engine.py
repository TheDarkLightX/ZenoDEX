"""Dispatch-table engine for the versioned v4 perps kernel.

``step(state, params)`` is the single entry point. It:

1. Validates the exact pre-state domain and invariants.
2. Validates parameter domains (from YAML type bounds).
3. Applies the shared cross-action epoch lifecycle guard.
4. Dispatches to the correct action guard / update / effect functions.
5. Checks all invariants on the post-state.
6. Returns a ``StepResult`` (accepted or rejected with reason).

The authoritative spec is `src/kernels/dex/perp_epoch_isolated_v4.yaml`; keep
this module in sync and use parity tests against generated refs when updating.
"""

from __future__ import annotations

from typing import Callable

from ..domain_limits import (
    PERP_ADVANCE_EPOCH_DELTA_MAX,
    PERP_PARAM_AMOUNT_MAX,
    PERP_POSITION_MAX,
    PERP_RATE_BPS_MAX,
    is_strict_int,
)
from ..perp_epoch_lifecycle import epoch_lifecycle_reject_reason
from ..perp_v2.errors import PerpGuardError, PerpInvariantError, PerpOverflowError
from ..perp_v2.types import Action, ActionParams, Effect, PerpState, StepResult
from .effects import (
    effect_advance_epoch,
    effect_apply_funding,
    effect_apply_insurance_claim,
    effect_clear_breaker,
    effect_deposit_collateral,
    effect_deposit_insurance,
    effect_partial_liquidate,
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
    guard_partial_liquidate,
    guard_publish_clearing_price,
    guard_set_position,
    guard_settle_epoch,
    guard_withdraw_collateral,
)
from .invariants import check_all
from .updates import (
    apply_advance_epoch,
    apply_clear_breaker,
    apply_deposit_collateral,
    apply_deposit_insurance,
    apply_funding,
    apply_insurance_claim,
    apply_partial_liquidate,
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
    Action.PARTIAL_LIQUIDATE: (
        guard_partial_liquidate, apply_partial_liquidate, effect_partial_liquidate,
    ),
}

# -- Parameter domain bounds (from YAML param type specs) --------------------

# Per-action bounds: list of (field_name, min_val, max_val).
_PARAM_BOUNDS: dict[Action, list[tuple[str, int, int]]] = {
    Action.ADVANCE_EPOCH: [
        ("delta", 1, PERP_ADVANCE_EPOCH_DELTA_MAX),
    ],
    Action.PUBLISH_CLEARING_PRICE: [
        ("price_e8", 1, PERP_PARAM_AMOUNT_MAX),
    ],
    Action.SETTLE_EPOCH: [],
    Action.DEPOSIT_COLLATERAL: [
        ("amount", 1, PERP_PARAM_AMOUNT_MAX),
    ],
    Action.WITHDRAW_COLLATERAL: [
        ("amount", 1, PERP_PARAM_AMOUNT_MAX),
    ],
    Action.SET_POSITION: [
        ("new_position_base", -PERP_POSITION_MAX, PERP_POSITION_MAX),
    ],
    Action.CLEAR_BREAKER: [],
    Action.APPLY_FUNDING: [
        ("new_rate_bps", -PERP_RATE_BPS_MAX, PERP_RATE_BPS_MAX),
    ],
    Action.DEPOSIT_INSURANCE: [
        ("amount", 1, PERP_PARAM_AMOUNT_MAX),
    ],
    Action.APPLY_INSURANCE_CLAIM: [
        ("claim_amount", 1, PERP_PARAM_AMOUNT_MAX),
    ],
    Action.PARTIAL_LIQUIDATE: [
        ("fraction_bps", 0, PERP_RATE_BPS_MAX),
    ],
}

# Actions that consume `auth_ok` as a consensus-relevant guard input.
_AUTH_ACTIONS: set[Action] = {
    Action.DEPOSIT_COLLATERAL,
    Action.WITHDRAW_COLLATERAL,
    Action.SET_POSITION,
    Action.CLEAR_BREAKER,
    Action.APPLY_FUNDING,
    Action.APPLY_INSURANCE_CLAIM,
    Action.PARTIAL_LIQUIDATE,
}


def _validate_params(params: ActionParams) -> str | None:
    """Check exact command shape and parameter domain bounds."""
    if type(params) is not ActionParams or type(params.action) is not Action:
        return "param_shape:action_params"
    if params.action in _AUTH_ACTIONS and type(params.auth_ok) is not bool:
        return "param_domain:auth_ok"

    bounds = _PARAM_BOUNDS.get(params.action)
    if bounds is None:
        return None
    for field, lo, hi in bounds:
        val = getattr(params, field)
        if not is_strict_int(val):
            return f"param_domain:{field}"
        if val < lo or val > hi:
            return f"param_domain:{field}"
    return None


def step(state: PerpState, params: ActionParams) -> StepResult:
    """Execute one action against an exact valid pre-state.

    Rejection never carries a candidate state or effect, so malformed pre-state,
    lifecycle, guard, and post-invariant failures are complete no-ops.
    """
    pre_violations = check_all(state)
    if pre_violations:
        return StepResult(
            accepted=False,
            rejection=f"pre_invariant:{','.join(pre_violations)}",
        )

    domain_err = _validate_params(params)
    if domain_err is not None:
        return StepResult(accepted=False, rejection=domain_err)

    entry = _DISPATCH.get(params.action)
    if entry is None:
        return StepResult(accepted=False, rejection=f"unknown_action:{params.action}")

    if epoch_lifecycle_reject_reason(state, params.action) is not None:
        return StepResult(accepted=False, rejection="guard")

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
        PerpGuardError: Command shape or guard condition not satisfied.
        PerpInvariantError: Pre-state or post-state violates an invariant.
    """
    result = step(state, params)
    if result.accepted:
        return result

    reason = result.rejection or ""
    if reason.startswith("param_domain:"):
        raise PerpOverflowError(reason)
    if reason.startswith("pre_invariant:"):
        violations = reason.removeprefix("pre_invariant:").split(",")
        raise PerpInvariantError(violations)
    if reason.startswith("invariant:"):
        violations = reason.removeprefix("invariant:").split(",")
        raise PerpInvariantError(violations)
    raise PerpGuardError(reason)
