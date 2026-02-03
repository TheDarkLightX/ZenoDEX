"""Endogenous funding rate market state machine.

Replaces the exogenous (operator-set) funding rate in perp_v2 with a
market-determined rate. Traders buy "rate-up" or "rate-down" positions,
and the equilibrium price becomes the funding rate.

Follows the perp_v2 dispatch-table pattern:
  guard → update → effects → invariant check.

Actions:
  - open_rate_long(amount): Bet that funding rate will be high
  - open_rate_short(amount): Bet that funding rate will be low
  - settle_rate_epoch: Compute realized rate, distribute payoffs, set perp funding
  - advance_rate_epoch: Reset for next epoch
  - emergency_freeze: Circuit breaker
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum, unique


BPS_DENOM = 10_000
MAX_AMOUNT = 1_000_000_000_000
MAX_RATE_BPS = 10_000  # ±100% absolute cap


@unique
class FRMAction(Enum):
    """Actions for the funding rate market."""
    OPEN_RATE_LONG = "open_rate_long"
    OPEN_RATE_SHORT = "open_rate_short"
    SETTLE_RATE_EPOCH = "settle_rate_epoch"
    ADVANCE_RATE_EPOCH = "advance_rate_epoch"
    EMERGENCY_FREEZE = "emergency_freeze"


@unique
class FRMEvent(Enum):
    """Events emitted by the funding rate market."""
    RATE_LONG_OPENED = "RateLongOpened"
    RATE_SHORT_OPENED = "RateShortOpened"
    RATE_EPOCH_SETTLED = "RateEpochSettled"
    RATE_EPOCH_ADVANCED = "RateEpochAdvanced"
    MARKET_FROZEN = "MarketFrozen"


@dataclass(frozen=True)
class FRMState:
    """Complete state of the funding rate market."""

    # Exposure
    rate_long_exposure: int = 0   # total staked on rate-up
    rate_short_exposure: int = 0  # total staked on rate-down

    # Derived rate from exposure ratio
    implied_rate_bps: int = 0     # (long - short) / (long + short) * funding_cap_bps

    # Settlement
    realized_rate_bps: int = 0    # actual basis at settlement
    settlement_epoch: int = 0
    rate_market_epoch: int = 0
    settled_this_epoch: bool = False

    # Financial
    premium_pool: int = 0
    long_payout: int = 0          # last settlement: amount distributed to longs
    short_payout: int = 0         # last settlement: amount distributed to shorts
    protocol_fee_pool: int = 0
    protocol_fee_bps: int = 100   # 1%

    # Constraints
    funding_cap_bps: int = 100    # ±1% max rate (matches perp default)

    # Emergency
    frozen: bool = False

    # Mark and index prices for basis computation (e8 scaled)
    mark_price_e8: int = 0
    index_price_e8: int = 0

    def __post_init__(self) -> None:
        for name in (
            "rate_long_exposure", "rate_short_exposure",
            "premium_pool", "long_payout", "short_payout", "protocol_fee_pool",
        ):
            val = getattr(self, name)
            if not isinstance(val, int) or isinstance(val, bool):
                raise TypeError(f"{name} must be int")
            if val < 0:
                raise ValueError(f"{name} must be non-negative: {val}")


@dataclass(frozen=True)
class FRMActionParams:
    """Parameters for a funding rate market action."""
    action: FRMAction
    amount: int = 0
    auth_ok: bool = False
    # For settlement
    mark_price_e8: int = 0
    index_price_e8: int = 0


@dataclass(frozen=True)
class FRMEffect:
    """Post-state observables."""
    event: FRMEvent
    implied_rate_bps: int = 0
    realized_rate_bps: int = 0
    payout_long: int = 0
    payout_short: int = 0


@dataclass(frozen=True)
class FRMStepResult:
    """Result of a single funding rate market step."""
    accepted: bool
    state: FRMState | None = None
    effect: FRMEffect | None = None
    rejection: str | None = None


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def compute_implied_rate_bps(
    long_exposure: int,
    short_exposure: int,
    funding_cap_bps: int,
) -> int:
    """Derive implied funding rate from exposure imbalance.

    rate = (long - short) / (long + short) * funding_cap_bps

    Positive rate: longs dominate (pay shorts).
    Negative rate: shorts dominate (pay longs).
    Clamped to ±funding_cap_bps.
    """
    total = long_exposure + short_exposure
    if total == 0:
        return 0
    raw = ((long_exposure - short_exposure) * funding_cap_bps) // total
    return max(-funding_cap_bps, min(funding_cap_bps, raw))


def compute_basis_bps(mark_price_e8: int, index_price_e8: int) -> int:
    """Compute basis in bps: (mark - index) / index * 10000.

    Returns 0 if index is zero.
    """
    if index_price_e8 <= 0:
        return 0
    return ((mark_price_e8 - index_price_e8) * BPS_DENOM) // index_price_e8


# ---------------------------------------------------------------------------
# Guards
# ---------------------------------------------------------------------------

def _guard_open_long(state: FRMState, params: FRMActionParams) -> bool:
    if not params.auth_ok:
        return False
    if state.frozen:
        return False
    if state.settled_this_epoch:
        return False
    if params.amount <= 0:
        return False
    if state.rate_long_exposure + params.amount > MAX_AMOUNT:
        return False
    if state.premium_pool + params.amount > MAX_AMOUNT:
        return False
    return True


def _guard_open_short(state: FRMState, params: FRMActionParams) -> bool:
    if not params.auth_ok:
        return False
    if state.frozen:
        return False
    if state.settled_this_epoch:
        return False
    if params.amount <= 0:
        return False
    if state.rate_short_exposure + params.amount > MAX_AMOUNT:
        return False
    if state.premium_pool + params.amount > MAX_AMOUNT:
        return False
    return True


def _guard_settle(state: FRMState, params: FRMActionParams) -> bool:
    if state.frozen:
        return False
    if state.settled_this_epoch:
        return False
    # Need both sides to have exposure for meaningful settlement
    if state.rate_long_exposure == 0 and state.rate_short_exposure == 0:
        return False
    # Need valid prices
    if params.mark_price_e8 <= 0 or params.index_price_e8 <= 0:
        return False
    return True


def _guard_advance(state: FRMState, params: FRMActionParams) -> bool:
    return state.settled_this_epoch


def _guard_freeze(state: FRMState, params: FRMActionParams) -> bool:
    return params.auth_ok and not state.frozen


# ---------------------------------------------------------------------------
# Updates
# ---------------------------------------------------------------------------

def _update_open_long(state: FRMState, params: FRMActionParams) -> FRMState:
    new_long = state.rate_long_exposure + params.amount
    new_implied = compute_implied_rate_bps(
        new_long, state.rate_short_exposure, state.funding_cap_bps,
    )
    return replace(
        state,
        rate_long_exposure=new_long,
        premium_pool=state.premium_pool + params.amount,
        implied_rate_bps=new_implied,
    )


def _update_open_short(state: FRMState, params: FRMActionParams) -> FRMState:
    new_short = state.rate_short_exposure + params.amount
    new_implied = compute_implied_rate_bps(
        state.rate_long_exposure, new_short, state.funding_cap_bps,
    )
    return replace(
        state,
        rate_short_exposure=new_short,
        premium_pool=state.premium_pool + params.amount,
        implied_rate_bps=new_implied,
    )


def _update_settle(state: FRMState, params: FRMActionParams) -> FRMState:
    # Compute realized basis
    realized_bps = compute_basis_bps(params.mark_price_e8, params.index_price_e8)
    clamped_realized = max(-state.funding_cap_bps, min(state.funding_cap_bps, realized_bps))

    # Settlement: compare implied vs realized
    # If implied > realized: shorts win (longs overpaid)
    # If implied < realized: longs win (shorts underpaid)
    implied = state.implied_rate_bps

    total_pool = state.premium_pool
    protocol_fee = (total_pool * state.protocol_fee_bps) // BPS_DENOM
    distributable = total_pool - protocol_fee

    # Payoff: proportional to how close each side was to correct
    # Simplified: if realized ≥ implied, longs get more; else shorts get more
    total_exposure = state.rate_long_exposure + state.rate_short_exposure
    if total_exposure > 0:
        if clamped_realized >= implied:
            # Longs were correct (rate was indeed high)
            long_share = state.rate_long_exposure
            short_share = state.rate_short_exposure
        else:
            # Shorts were correct (rate was low)
            long_share = state.rate_short_exposure
            short_share = state.rate_long_exposure

        payout_long = (distributable * long_share) // total_exposure
        payout_short = distributable - payout_long
    else:
        payout_long = 0
        payout_short = 0

    # Conservation: premium_pool = protocol_fee + payout_long + payout_short
    return replace(
        state,
        realized_rate_bps=clamped_realized,
        settled_this_epoch=True,
        settlement_epoch=state.settlement_epoch + 1,
        long_payout=payout_long,
        short_payout=payout_short,
        premium_pool=0,
        protocol_fee_pool=state.protocol_fee_pool + protocol_fee,
        mark_price_e8=params.mark_price_e8,
        index_price_e8=params.index_price_e8,
    )


def _update_advance(state: FRMState, params: FRMActionParams) -> FRMState:
    return replace(
        state,
        rate_market_epoch=state.rate_market_epoch + 1,
        settled_this_epoch=False,
        rate_long_exposure=0,
        rate_short_exposure=0,
        implied_rate_bps=0,
        realized_rate_bps=0,
        long_payout=0,
        short_payout=0,
        premium_pool=0,
    )


def _update_freeze(state: FRMState, params: FRMActionParams) -> FRMState:
    return replace(state, frozen=True)


# ---------------------------------------------------------------------------
# Effects
# ---------------------------------------------------------------------------

def _effect_open_long(state: FRMState, params: FRMActionParams) -> FRMEffect:
    return FRMEffect(
        event=FRMEvent.RATE_LONG_OPENED,
        implied_rate_bps=state.implied_rate_bps,
    )


def _effect_open_short(state: FRMState, params: FRMActionParams) -> FRMEffect:
    return FRMEffect(
        event=FRMEvent.RATE_SHORT_OPENED,
        implied_rate_bps=state.implied_rate_bps,
    )


def _effect_settle(state: FRMState, params: FRMActionParams) -> FRMEffect:
    return FRMEffect(
        event=FRMEvent.RATE_EPOCH_SETTLED,
        implied_rate_bps=state.implied_rate_bps,
        realized_rate_bps=state.realized_rate_bps,
        payout_long=state.long_payout,
        payout_short=state.short_payout,
    )


def _effect_advance(state: FRMState, params: FRMActionParams) -> FRMEffect:
    return FRMEffect(event=FRMEvent.RATE_EPOCH_ADVANCED)


def _effect_freeze(state: FRMState, params: FRMActionParams) -> FRMEffect:
    return FRMEffect(event=FRMEvent.MARKET_FROZEN)


# ---------------------------------------------------------------------------
# Invariant check
# ---------------------------------------------------------------------------

def _check_invariants(state: FRMState) -> list[str]:
    violations: list[str] = []
    if state.rate_long_exposure < 0:
        violations.append("long_exposure_nonneg")
    if state.rate_short_exposure < 0:
        violations.append("short_exposure_nonneg")
    if state.premium_pool < 0:
        violations.append("premium_pool_nonneg")
    if state.long_payout < 0:
        violations.append("long_payout_nonneg")
    if state.short_payout < 0:
        violations.append("short_payout_nonneg")
    if state.protocol_fee_pool < 0:
        violations.append("protocol_fee_nonneg")
    if abs(state.implied_rate_bps) > state.funding_cap_bps:
        violations.append("rate_bounded")
    return violations


# ---------------------------------------------------------------------------
# Dispatch table
# ---------------------------------------------------------------------------

_DISPATCH = {
    FRMAction.OPEN_RATE_LONG: (_guard_open_long, _update_open_long, _effect_open_long),
    FRMAction.OPEN_RATE_SHORT: (_guard_open_short, _update_open_short, _effect_open_short),
    FRMAction.SETTLE_RATE_EPOCH: (_guard_settle, _update_settle, _effect_settle),
    FRMAction.ADVANCE_RATE_EPOCH: (_guard_advance, _update_advance, _effect_advance),
    FRMAction.EMERGENCY_FREEZE: (_guard_freeze, _update_freeze, _effect_freeze),
}


def step(state: FRMState, params: FRMActionParams) -> FRMStepResult:
    """Execute one funding rate market action."""
    entry = _DISPATCH.get(params.action)
    if entry is None:
        return FRMStepResult(accepted=False, rejection=f"unknown_action:{params.action}")

    guard_fn, update_fn, effect_fn = entry

    if not guard_fn(state, params):
        return FRMStepResult(accepted=False, rejection="guard")

    new_state = update_fn(state, params)

    violations = _check_invariants(new_state)
    if violations:
        return FRMStepResult(
            accepted=False,
            rejection=f"invariant:{','.join(violations)}",
        )

    effect = effect_fn(new_state, params)
    return FRMStepResult(accepted=True, state=new_state, effect=effect)
