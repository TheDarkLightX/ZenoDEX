"""Volatility tier controller adapter for dynamic fee tiers.

Implements the state machine from volatility_tier_controller_v1.yaml as a
Python dispatch-table engine following the perp_v2 pattern:
  guard → update → effects → invariant check.

Two actions:
  - observe(epoch, volatility_bps, data_ok): transition tier based on vol signal
  - configure(new_t1, new_t2, new_t3): admin reconfigures thresholds

Key properties:
  - Fail-closed: data_ok=False → tier 3 (halt)
  - Monotone within epoch: tier can only increase within same epoch
  - De-escalation on epoch advance: tier resets to observed level
  - Fee multiplier monotone in tier: tier 0→1x, 1→2x, 2→3x, 3→halt
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum, unique
from typing import TypeGuard, cast

from ..state.volatility import BPS_DENOM, TierEffects, TierState, tier_effects


@unique
class TierAction(Enum):
    """Actions for the volatility tier controller."""
    OBSERVE = "observe"
    CONFIGURE = "configure"


@dataclass(frozen=True)
class TierActionParams:
    """Parameters for a tier controller action."""

    action: TierAction

    # observe params
    epoch: int = 0
    volatility_bps: int = 0
    data_ok: bool = True

    # configure params
    caller_is_admin: bool = False
    new_t1_bps: int = 0
    new_t2_bps: int = 0
    new_t3_bps: int = 0


@dataclass(frozen=True)
class TierStepResult:
    """Result of a single tier controller step."""

    accepted: bool
    state: TierState | None = None
    effects: TierEffects | None = None
    rejection: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.accepted, bool):
            raise ValueError("accepted must be bool")
        if self.accepted:
            if self.state is None or self.effects is None:
                raise ValueError("accepted tier result must include state and effects")
            if self.rejection is not None:
                raise ValueError("accepted tier result cannot include rejection")
            return

        if self.state is not None or self.effects is not None:
            raise ValueError("rejected tier result cannot include state or effects")
        if not isinstance(self.rejection, str) or not self.rejection:
            raise ValueError("rejected tier result must include a rejection reason")


def _is_plain_int(value: object) -> TypeGuard[int]:
    """Return True for ints but reject bools."""
    return isinstance(value, int) and not isinstance(value, bool)


def _validate_observe_params(params: TierActionParams) -> str | None:
    """Validate observe params against the kernel domain."""
    epoch = cast(object, params.epoch)
    volatility_bps = cast(object, params.volatility_bps)
    data_ok = cast(object, params.data_ok)
    if not _is_plain_int(epoch) or not (0 <= epoch <= 1_000_000_000):
        return "epoch"
    if not _is_plain_int(volatility_bps) or not (0 <= volatility_bps <= BPS_DENOM):
        return "volatility_bps"
    if not isinstance(data_ok, bool):
        return "data_ok"
    return None


def _validate_configure_params(params: TierActionParams) -> str | None:
    """Validate configure params against the kernel domain."""
    caller_is_admin = cast(object, params.caller_is_admin)
    new_t1_bps = cast(object, params.new_t1_bps)
    new_t2_bps = cast(object, params.new_t2_bps)
    new_t3_bps = cast(object, params.new_t3_bps)
    if not isinstance(caller_is_admin, bool):
        return "caller_is_admin"
    if not _is_plain_int(new_t1_bps) or not (0 <= new_t1_bps <= BPS_DENOM):
        return "new_t1_bps"
    if not _is_plain_int(new_t2_bps) or not (0 <= new_t2_bps <= BPS_DENOM):
        return "new_t2_bps"
    if not _is_plain_int(new_t3_bps) or not (0 <= new_t3_bps <= BPS_DENOM):
        return "new_t3_bps"
    return None


def _validate_params(params: TierActionParams) -> str | None:
    """Dispatch action-specific param validation."""
    action = cast(object, params.action)
    if action is TierAction.OBSERVE:
        return _validate_observe_params(params)
    if action is TierAction.CONFIGURE:
        return _validate_configure_params(params)
    return None



# ---------------------------------------------------------------------------
# Guards
# ---------------------------------------------------------------------------

def _guard_observe(state: TierState, params: TierActionParams) -> bool:
    """Observe guard: epoch must not go backwards."""
    return params.epoch >= state.last_epoch


def _guard_configure(state: TierState, params: TierActionParams) -> bool:
    """Configure guard: admin auth + ordered thresholds + in-range values."""
    if not params.caller_is_admin:
        return False
    if not (params.new_t1_bps <= params.new_t2_bps <= params.new_t3_bps):
        return False
    return True


# ---------------------------------------------------------------------------
# Updates
# ---------------------------------------------------------------------------

def _desired_tier(volatility_bps: int, data_ok: bool, state: TierState) -> int:
    """Compute desired tier from volatility observation.

    Fail-closed: if data_ok is False, return tier 3 (halt).
    """
    if not data_ok:
        return 3
    if volatility_bps >= state.t3_bps:
        return 3
    if volatility_bps >= state.t2_bps:
        return 2
    if volatility_bps >= state.t1_bps:
        return 1
    return 0


def _update_observe(state: TierState, params: TierActionParams) -> TierState:
    """Apply observe action: compute new tier with monotone/de-escalation logic."""
    desired = _desired_tier(params.volatility_bps, params.data_ok, state)

    if params.epoch == state.last_epoch:
        # Same epoch: monotone (no de-escalation)
        new_tier = max(desired, state.tier)
    else:
        # Epoch advanced: allow de-escalation
        new_tier = desired

    return replace(state, tier=new_tier, last_epoch=params.epoch)


def _update_configure(state: TierState, params: TierActionParams) -> TierState:
    """Apply configure action: update thresholds."""
    return replace(
        state,
        t1_bps=params.new_t1_bps,
        t2_bps=params.new_t2_bps,
        t3_bps=params.new_t3_bps,
    )


# ---------------------------------------------------------------------------
# Invariant check
# ---------------------------------------------------------------------------

def _check_invariants(state: TierState) -> list[str]:
    """Check all invariants on post-state. Returns list of violation names."""
    violations: list[str] = []
    if not (0 <= state.tier <= 3):
        violations.append("tier_bounded")
    if not (state.t1_bps <= state.t2_bps <= state.t3_bps):
        violations.append("thresholds_ordered")
    return violations


# ---------------------------------------------------------------------------
# Dispatch table
# ---------------------------------------------------------------------------

_DISPATCH = {
    TierAction.OBSERVE: (_guard_observe, _update_observe),
    TierAction.CONFIGURE: (_guard_configure, _update_configure),
}


def step(state: TierState, params: TierActionParams) -> TierStepResult:
    """Execute one tier controller action.

    Returns TierStepResult with accepted=True on success, or
    accepted=False with a rejection reason string.
    """
    entry = _DISPATCH.get(params.action)
    if entry is None:
        return TierStepResult(accepted=False, rejection=f"unknown_action:{params.action}")

    invalid_param = _validate_params(params)
    if invalid_param is not None:
        return TierStepResult(accepted=False, rejection=f"invalid_param:{invalid_param}")

    guard_fn, update_fn = entry

    if not guard_fn(state, params):
        return TierStepResult(accepted=False, rejection="guard")

    new_state = update_fn(state, params)

    violations = _check_invariants(new_state)
    if violations:
        return TierStepResult(
            accepted=False,
            rejection=f"invariant:{','.join(violations)}",
        )

    effects = tier_effects(new_state.tier)
    return TierStepResult(accepted=True, state=new_state, effects=effects)


# ---------------------------------------------------------------------------
# Convenience: effective fee for a pool
# ---------------------------------------------------------------------------

def effective_fee_bps(base_fee_bps: int, tier_state: TierState) -> int:
    """Compute effective fee = base_fee * fee_mult / 10000.

    At tier 3 (halt), returns -1 to signal trading is halted.
    Returns 0 for non-positive base_fee_bps (fail-safe).
    """
    if base_fee_bps <= 0:
        return 0
    effects = tier_effects(tier_state.tier)
    if effects.halt:
        return -1
    return (base_fee_bps * effects.fee_mult_bps) // 10_000


def max_trade_amount(reserve: int, tier_state: TierState) -> int:
    """Compute max trade amount = reserve * max_trade_bps / 10000.

    At tier 3 (halt), returns 0.
    Returns 0 for non-positive reserves (fail-safe).
    """
    if reserve <= 0:
        return 0
    effects = tier_effects(tier_state.tier)
    return (reserve * effects.max_trade_bps) // 10_000
