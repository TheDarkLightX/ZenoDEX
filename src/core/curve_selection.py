"""Curve selection prediction market state machine.

A meta-market where participants stake on which AMM curve family will
produce the most LP revenue. The winning curve becomes the pool's active curve.

Follows the perp_v2 dispatch-table pattern:
  guard → update → effects → invariant check.

Actions:
  - stake_on_curve(curve_id, amount): Place prediction bet
  - unstake(curve_id, amount): Withdraw with early-exit penalty
  - advance_epoch: Accumulate revenue metrics
  - settle_prediction: Determine winner, distribute payoffs, switch curve
  - admin_set_interval: Governance sets prediction duration
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum, unique


BPS_DENOM = 10_000
MAX_AMOUNT = 1_000_000_000_000
NUM_CURVES = 5
EARLY_EXIT_PENALTY_BPS = 500  # 5% penalty for early exit


@unique
class CSAction(Enum):
    """Actions for the curve selection prediction market."""
    STAKE_ON_CURVE = "stake_on_curve"
    UNSTAKE = "unstake"
    ADVANCE_EPOCH = "advance_epoch"
    SETTLE_PREDICTION = "settle_prediction"
    ADMIN_SET_INTERVAL = "admin_set_interval"


@unique
class CSEvent(Enum):
    """Events emitted by the curve selection market."""
    STAKED = "Staked"
    UNSTAKED = "Unstaked"
    EPOCH_ADVANCED = "EpochAdvanced"
    PREDICTION_SETTLED = "PredictionSettled"
    INTERVAL_SET = "IntervalSet"


@dataclass(frozen=True)
class CSState:
    """Complete state of the curve selection prediction market."""

    # Active curve (0-4)
    active_curve: int = 0

    # Stakes per curve
    stakes_0: int = 0  # CPMM
    stakes_1: int = 0  # cubic_sum
    stakes_2: int = 0  # sum_boost
    stakes_3: int = 0  # quartic_blend
    stakes_4: int = 0  # quintic_blend

    # Revenue per curve for current prediction epoch
    revenue_0: int = 0
    revenue_1: int = 0
    revenue_2: int = 0
    revenue_3: int = 0
    revenue_4: int = 0

    # Epoch management
    prediction_epoch: int = 0
    epochs_since_start: int = 0
    settlement_epoch_interval: int = 10

    # Financial
    total_staked: int = 0
    winner_payout_pool: int = 0
    protocol_fee_pool: int = 0
    protocol_fee_bps: int = 200  # 2%

    def __post_init__(self) -> None:
        if not (0 <= self.active_curve < NUM_CURVES):
            raise ValueError(f"active_curve must be in [0, {NUM_CURVES}): {self.active_curve}")

    def get_stake(self, curve_id: int) -> int:
        return (self.stakes_0, self.stakes_1, self.stakes_2,
                self.stakes_3, self.stakes_4)[curve_id]

    def get_revenue(self, curve_id: int) -> int:
        return (self.revenue_0, self.revenue_1, self.revenue_2,
                self.revenue_3, self.revenue_4)[curve_id]


@dataclass(frozen=True)
class CSActionParams:
    """Parameters for a curve selection action."""
    action: CSAction
    curve_id: int = 0
    amount: int = 0
    auth_ok: bool = False
    # revenue updates (for advance_epoch)
    revenue_deltas: tuple[int, ...] = (0, 0, 0, 0, 0)
    # admin params
    new_interval: int = 0


@dataclass(frozen=True)
class CSEffect:
    """Post-state observables."""
    event: CSEvent
    winning_curve: int = -1
    payout_amount: int = 0
    new_active_curve: int = -1
    returned_amount: int = 0   # amount returned on unstake (after penalty)
    penalty_amount: int = 0    # early-exit penalty on unstake


@dataclass(frozen=True)
class CSStepResult:
    """Result of a single curve selection step."""
    accepted: bool
    state: CSState | None = None
    effect: CSEffect | None = None
    rejection: str | None = None


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _set_stake(state: CSState, curve_id: int, value: int) -> CSState:
    """Return new state with one curve's stake updated."""
    fields = {f"stakes_{curve_id}": value}
    return replace(state, **fields)


def _set_revenue(state: CSState, curve_id: int, value: int) -> CSState:
    """Return new state with one curve's revenue updated."""
    fields = {f"revenue_{curve_id}": value}
    return replace(state, **fields)


# ---------------------------------------------------------------------------
# Guards
# ---------------------------------------------------------------------------

def _guard_stake(state: CSState, params: CSActionParams) -> bool:
    if not params.auth_ok:
        return False
    if not (0 <= params.curve_id < NUM_CURVES):
        return False
    if params.amount <= 0:
        return False
    if state.total_staked + params.amount > MAX_AMOUNT:
        return False
    return True


def _guard_unstake(state: CSState, params: CSActionParams) -> bool:
    if not params.auth_ok:
        return False
    if not (0 <= params.curve_id < NUM_CURVES):
        return False
    if params.amount <= 0:
        return False
    if state.get_stake(params.curve_id) < params.amount:
        return False
    return True


def _guard_advance(state: CSState, params: CSActionParams) -> bool:
    if len(params.revenue_deltas) != NUM_CURVES:
        return False
    return True


def _guard_settle(state: CSState, params: CSActionParams) -> bool:
    return state.epochs_since_start >= state.settlement_epoch_interval


def _guard_admin_set(state: CSState, params: CSActionParams) -> bool:
    if not params.auth_ok:
        return False
    return params.new_interval > 0


# ---------------------------------------------------------------------------
# Updates
# ---------------------------------------------------------------------------

def _update_stake(state: CSState, params: CSActionParams) -> CSState:
    old = state.get_stake(params.curve_id)
    s = _set_stake(state, params.curve_id, old + params.amount)
    return replace(s, total_staked=state.total_staked + params.amount)


def _update_unstake(state: CSState, params: CSActionParams) -> CSState:
    old = state.get_stake(params.curve_id)
    penalty = (params.amount * EARLY_EXIT_PENALTY_BPS) // BPS_DENOM
    s = _set_stake(state, params.curve_id, old - params.amount)
    return replace(
        s,
        total_staked=state.total_staked - params.amount,
        protocol_fee_pool=state.protocol_fee_pool + penalty,
    )


def _update_advance(state: CSState, params: CSActionParams) -> CSState:
    s = state
    for cid in range(NUM_CURVES):
        old_rev = s.get_revenue(cid)
        delta = params.revenue_deltas[cid] if cid < len(params.revenue_deltas) else 0
        s = _set_revenue(s, cid, old_rev + max(0, delta))
    return replace(s, epochs_since_start=s.epochs_since_start + 1)


def _update_settle(state: CSState, params: CSActionParams) -> CSState:
    # Find winning curve (highest revenue, tie-break lowest id)
    best_id = 0
    best_rev = state.get_revenue(0)
    for cid in range(1, NUM_CURVES):
        rev = state.get_revenue(cid)
        if rev > best_rev:
            best_id = cid
            best_rev = rev

    # Calculate payoffs: winners get losing stakes minus protocol fee
    winner_stake = state.get_stake(best_id)
    losing_stakes = state.total_staked - winner_stake
    protocol_fee = (losing_stakes * state.protocol_fee_bps) // BPS_DENOM
    payout = losing_stakes - protocol_fee

    # Zero all losing stakes, keep only winner stake.
    # Conservation: losing_stakes = payout + protocol_fee
    # total_staked goes from (winner + losers) → winner only
    s = replace(
        state,
        active_curve=best_id,
        prediction_epoch=state.prediction_epoch + 1,
        epochs_since_start=0,
        total_staked=winner_stake,
        winner_payout_pool=payout,
        protocol_fee_pool=state.protocol_fee_pool + protocol_fee,
        stakes_0=state.get_stake(0) if 0 == best_id else 0,
        stakes_1=state.get_stake(1) if 1 == best_id else 0,
        stakes_2=state.get_stake(2) if 2 == best_id else 0,
        stakes_3=state.get_stake(3) if 3 == best_id else 0,
        stakes_4=state.get_stake(4) if 4 == best_id else 0,
        revenue_0=0,
        revenue_1=0,
        revenue_2=0,
        revenue_3=0,
        revenue_4=0,
    )
    return s


def _update_admin_set(state: CSState, params: CSActionParams) -> CSState:
    return replace(state, settlement_epoch_interval=params.new_interval)


# ---------------------------------------------------------------------------
# Effects
# ---------------------------------------------------------------------------

def _effect_stake(state: CSState, params: CSActionParams) -> CSEffect:
    return CSEffect(event=CSEvent.STAKED)


def _effect_unstake(state: CSState, params: CSActionParams) -> CSEffect:
    penalty = (params.amount * EARLY_EXIT_PENALTY_BPS) // BPS_DENOM
    returned = params.amount - penalty
    return CSEffect(
        event=CSEvent.UNSTAKED,
        returned_amount=returned,
        penalty_amount=penalty,
    )


def _effect_advance(state: CSState, params: CSActionParams) -> CSEffect:
    return CSEffect(event=CSEvent.EPOCH_ADVANCED)


def _effect_settle(state: CSState, params: CSActionParams) -> CSEffect:
    return CSEffect(
        event=CSEvent.PREDICTION_SETTLED,
        winning_curve=state.active_curve,
        payout_amount=state.winner_payout_pool,
        new_active_curve=state.active_curve,
    )


def _effect_admin_set(state: CSState, params: CSActionParams) -> CSEffect:
    return CSEffect(event=CSEvent.INTERVAL_SET)


# ---------------------------------------------------------------------------
# Invariant check
# ---------------------------------------------------------------------------

def _check_invariants(state: CSState) -> list[str]:
    violations: list[str] = []
    if not (0 <= state.active_curve < NUM_CURVES):
        violations.append("curve_valid")
    if state.total_staked < 0:
        violations.append("total_staked_nonneg")
    # total_staked must equal sum of individual stakes
    sum_stakes = sum(state.get_stake(cid) for cid in range(NUM_CURVES))
    if state.total_staked != sum_stakes:
        violations.append("total_staked_consistent")
    for cid in range(NUM_CURVES):
        if state.get_stake(cid) < 0:
            violations.append(f"stake_{cid}_nonneg")
    if state.protocol_fee_pool < 0:
        violations.append("protocol_fee_nonneg")
    if state.winner_payout_pool < 0:
        violations.append("winner_payout_nonneg")
    for cid in range(NUM_CURVES):
        if state.get_revenue(cid) < 0:
            violations.append(f"revenue_{cid}_nonneg")
    return violations


# ---------------------------------------------------------------------------
# Dispatch table
# ---------------------------------------------------------------------------

_DISPATCH = {
    CSAction.STAKE_ON_CURVE: (_guard_stake, _update_stake, _effect_stake),
    CSAction.UNSTAKE: (_guard_unstake, _update_unstake, _effect_unstake),
    CSAction.ADVANCE_EPOCH: (_guard_advance, _update_advance, _effect_advance),
    CSAction.SETTLE_PREDICTION: (_guard_settle, _update_settle, _effect_settle),
    CSAction.ADMIN_SET_INTERVAL: (_guard_admin_set, _update_admin_set, _effect_admin_set),
}


def step(state: CSState, params: CSActionParams) -> CSStepResult:
    """Execute one curve selection action."""
    entry = _DISPATCH.get(params.action)
    if entry is None:
        return CSStepResult(accepted=False, rejection=f"unknown_action:{params.action}")

    guard_fn, update_fn, effect_fn = entry

    if not guard_fn(state, params):
        return CSStepResult(accepted=False, rejection="guard")

    new_state = update_fn(state, params)

    violations = _check_invariants(new_state)
    if violations:
        return CSStepResult(
            accepted=False,
            rejection=f"invariant:{','.join(violations)}",
        )

    effect = effect_fn(new_state, params)
    return CSStepResult(accepted=True, state=new_state, effect=effect)
