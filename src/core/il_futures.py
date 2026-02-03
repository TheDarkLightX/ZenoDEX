"""IL Futures Market state machine.

A two-sided market where LPs buy IL protection and speculators sell it.
IL risk becomes a tradeable commodity with on-chain settlement.

Follows the perp_v2 dispatch-table pattern:
  guard → update → effects → invariant check.

Actions:
  - open_long_il: LP buys IL protection (stakes collateral)
  - open_short_il: Speculator sells IL protection (posts margin)
  - close_position: Exit before settlement
  - snapshot_epoch_start: Record pool state at epoch boundary
  - settle_il_epoch: Compute realized IL, distribute payoffs
  - advance_epoch: Move to next epoch
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum, unique

from .il_futures_math import compute_il_bps, compute_payout


BPS_DENOM = 10_000
MAX_AMOUNT = 1_000_000_000_000


@unique
class ILFAction(Enum):
    """Actions for the IL futures market."""
    OPEN_LONG_IL = "open_long_il"
    OPEN_SHORT_IL = "open_short_il"
    CLOSE_POSITION = "close_position"
    SNAPSHOT_EPOCH_START = "snapshot_epoch_start"
    SETTLE_IL_EPOCH = "settle_il_epoch"
    ADVANCE_EPOCH = "advance_epoch"


@unique
class ILFEvent(Enum):
    """Events emitted by the IL futures market."""
    LONG_OPENED = "LongOpened"
    SHORT_OPENED = "ShortOpened"
    POSITION_CLOSED = "PositionClosed"
    EPOCH_SNAPSHOTTED = "EpochSnapshotted"
    EPOCH_SETTLED = "EpochSettled"
    EPOCH_ADVANCED = "EpochAdvanced"


@dataclass(frozen=True)
class ILFState:
    """Complete state of the IL futures market."""

    # Epoch management
    epoch: int = 0
    settled_this_epoch: bool = False
    snapshot_taken: bool = False

    # Pool snapshot at epoch start (settlement reference)
    pool_snapshot_reserve_x: int = 0
    pool_snapshot_reserve_y: int = 0

    # Exposure tracking
    long_exposure: int = 0   # Total protection bought (LP side)
    short_exposure: int = 0  # Total protection sold (speculator side)

    # Financial pools
    premium_pool: int = 0        # Premiums from long-side opening
    margin_pool: int = 0         # Short-side margin (always == short_exposure)
    protocol_fee_pool: int = 0   # Protocol fees accumulated

    # Settlement
    realized_il_bps: int = 0     # Actual IL at epoch end
    settlement_price_bps: int = 0  # Market-determined IL price
    last_net_payout: int = 0     # Net payout to longs from last settlement
    last_protocol_fee: int = 0   # Protocol fee from last settlement

    # Control parameters
    max_leverage_bps: int = 20000  # 2x: long_exposure <= short_exposure * 2
    protocol_fee_bps: int = 100    # 1% protocol fee on payoffs
    coverage_ratio_bps: int = 8000  # 80% coverage

    def __post_init__(self) -> None:
        if not (0 <= self.protocol_fee_bps <= BPS_DENOM):
            raise ValueError(f"protocol_fee_bps must be in [0, {BPS_DENOM}]: {self.protocol_fee_bps}")
        if not (0 <= self.coverage_ratio_bps <= BPS_DENOM):
            raise ValueError(f"coverage_ratio_bps must be in [0, {BPS_DENOM}]: {self.coverage_ratio_bps}")
        if self.max_leverage_bps <= 0:
            raise ValueError(f"max_leverage_bps must be positive: {self.max_leverage_bps}")


@dataclass(frozen=True)
class ILFActionParams:
    """Parameters for an IL futures action."""
    action: ILFAction
    amount: int = 0            # collateral/margin amount
    premium_amount: int = 0    # premium for opening position
    auth_ok: bool = False
    close_long: bool = False   # close from long side
    close_short: bool = False  # close from short side

    # snapshot params
    reserve_x: int = 0
    reserve_y: int = 0

    # settlement params
    current_reserve_x: int = 0
    current_reserve_y: int = 0


@dataclass(frozen=True)
class ILFEffect:
    """Post-state observables."""
    event: ILFEvent
    il_bps: int = 0
    net_payout: int = 0         # net payout to long holders
    protocol_fee: int = 0       # protocol fee taken from payout
    premium_collected: int = 0  # premium from opening position


@dataclass(frozen=True)
class ILFStepResult:
    """Result of a single IL futures step."""
    accepted: bool
    state: ILFState | None = None
    effect: ILFEffect | None = None
    rejection: str | None = None


# ---------------------------------------------------------------------------
# Guards
# ---------------------------------------------------------------------------

def _guard_open_long(state: ILFState, params: ILFActionParams) -> bool:
    if not params.auth_ok:
        return False
    if state.snapshot_taken:
        return False  # exposure frozen from snapshot through end of epoch
    if params.amount <= 0 or params.premium_amount <= 0:
        return False
    if state.long_exposure + params.amount > MAX_AMOUNT:
        return False
    if state.premium_pool + params.premium_amount > MAX_AMOUNT:
        return False
    # Leverage check: long_exposure <= short_exposure * max_leverage / 10000
    # When short_exposure == 0, no longs can open (need shorts first)
    new_long = state.long_exposure + params.amount
    if state.short_exposure == 0:
        return False
    max_long = (state.short_exposure * state.max_leverage_bps) // BPS_DENOM
    if new_long > max_long:
        return False
    return True


def _guard_open_short(state: ILFState, params: ILFActionParams) -> bool:
    if not params.auth_ok:
        return False
    if state.snapshot_taken:
        return False  # exposure frozen from snapshot through end of epoch
    if params.amount <= 0:
        return False
    if state.short_exposure + params.amount > MAX_AMOUNT:
        return False
    if state.margin_pool + params.amount > MAX_AMOUNT:
        return False
    return True


def _guard_close_position(state: ILFState, params: ILFActionParams) -> bool:
    if not params.auth_ok:
        return False
    # Frozen between snapshot and settlement; allowed after settlement
    # so shorts can withdraw remaining margin before next epoch.
    if state.snapshot_taken and not state.settled_this_epoch:
        return False
    if params.amount <= 0:
        return False
    # Must specify exactly one side
    if params.close_long == params.close_short:
        return False
    if params.close_long and params.amount > state.long_exposure:
        return False
    if params.close_short and params.amount > state.short_exposure:
        return False
    return True


def _guard_snapshot(state: ILFState, params: ILFActionParams) -> bool:
    if not params.auth_ok:
        return False
    if state.snapshot_taken:
        return False
    if params.reserve_x <= 0 or params.reserve_y <= 0:
        return False
    return True


def _guard_settle(state: ILFState, params: ILFActionParams) -> bool:
    if not params.auth_ok:
        return False
    if state.settled_this_epoch:
        return False
    if not state.snapshot_taken:
        return False
    if params.current_reserve_x <= 0 or params.current_reserve_y <= 0:
        return False
    return True


def _guard_advance(state: ILFState, params: ILFActionParams) -> bool:
    return state.settled_this_epoch


# ---------------------------------------------------------------------------
# Updates
# ---------------------------------------------------------------------------

def _update_open_long(state: ILFState, params: ILFActionParams) -> ILFState:
    return replace(
        state,
        long_exposure=state.long_exposure + params.amount,
        premium_pool=state.premium_pool + params.premium_amount,
    )


def _update_open_short(state: ILFState, params: ILFActionParams) -> ILFState:
    return replace(
        state,
        short_exposure=state.short_exposure + params.amount,
        margin_pool=state.margin_pool + params.amount,
    )


def _update_close_position(state: ILFState, params: ILFActionParams) -> ILFState:
    if params.close_long:
        return replace(state, long_exposure=state.long_exposure - params.amount)
    else:
        return replace(
            state,
            short_exposure=state.short_exposure - params.amount,
            margin_pool=state.margin_pool - params.amount,
        )


def _update_snapshot(state: ILFState, params: ILFActionParams) -> ILFState:
    return replace(
        state,
        snapshot_taken=True,
        pool_snapshot_reserve_x=params.reserve_x,
        pool_snapshot_reserve_y=params.reserve_y,
    )


def _update_settle(state: ILFState, params: ILFActionParams) -> ILFState:
    il_bps = compute_il_bps(
        state.pool_snapshot_reserve_x,
        state.pool_snapshot_reserve_y,
        params.current_reserve_x,
        params.current_reserve_y,
    )

    # Total long payoff = long_exposure * il_bps * coverage / (10000^2)
    total_long_payout = compute_payout(
        il_bps, state.long_exposure, state.coverage_ratio_bps,
    )

    # Cap total outflow to available pools (premium + margin)
    available = state.premium_pool + state.margin_pool
    capped_payout = min(total_long_payout, available)

    # Protocol fee taken from the capped payout (fee + net are sourced from same pool)
    protocol_fee = (capped_payout * state.protocol_fee_bps) // BPS_DENOM
    net_payout = capped_payout - protocol_fee

    # Total deducted from pools = net_payout + protocol_fee = capped_payout
    # Deduct from margin first, then premium
    total_deduct = net_payout + protocol_fee  # == capped_payout
    margin_deduct = min(total_deduct, state.margin_pool)
    premium_deduct = total_deduct - margin_deduct

    new_margin = state.margin_pool - margin_deduct
    new_premium = state.premium_pool - premium_deduct

    # Settlement closes all positions: longs received payout, shorts absorbed loss.
    # Reduce exposures to match remaining pool balances.
    # margin_pool was deposited 1:1 with short_exposure.
    new_short = new_margin
    # Long positions are fully settled; zero exposure to avoid leverage_no_shorts.
    new_long = 0

    return replace(
        state,
        settled_this_epoch=True,
        realized_il_bps=il_bps,
        settlement_price_bps=il_bps,
        long_exposure=new_long,
        short_exposure=new_short,
        margin_pool=new_margin,
        premium_pool=new_premium,
        protocol_fee_pool=state.protocol_fee_pool + protocol_fee,
        last_net_payout=net_payout,
        last_protocol_fee=protocol_fee,
    )


def _update_advance(state: ILFState, params: ILFActionParams) -> ILFState:
    return replace(
        state,
        epoch=state.epoch + 1,
        settled_this_epoch=False,
        snapshot_taken=False,
        realized_il_bps=0,
    )


# ---------------------------------------------------------------------------
# Effects
# ---------------------------------------------------------------------------

def _effect_open_long(state: ILFState, params: ILFActionParams) -> ILFEffect:
    return ILFEffect(event=ILFEvent.LONG_OPENED, premium_collected=params.premium_amount)


def _effect_open_short(state: ILFState, params: ILFActionParams) -> ILFEffect:
    return ILFEffect(event=ILFEvent.SHORT_OPENED)


def _effect_close(state: ILFState, params: ILFActionParams) -> ILFEffect:
    return ILFEffect(event=ILFEvent.POSITION_CLOSED)


def _effect_snapshot(state: ILFState, params: ILFActionParams) -> ILFEffect:
    return ILFEffect(event=ILFEvent.EPOCH_SNAPSHOTTED)


def _effect_settle(state: ILFState, params: ILFActionParams) -> ILFEffect:
    return ILFEffect(
        event=ILFEvent.EPOCH_SETTLED,
        il_bps=state.realized_il_bps,
        net_payout=state.last_net_payout,
        protocol_fee=state.last_protocol_fee,
    )


def _effect_advance(state: ILFState, params: ILFActionParams) -> ILFEffect:
    return ILFEffect(event=ILFEvent.EPOCH_ADVANCED)


# ---------------------------------------------------------------------------
# Invariant check
# ---------------------------------------------------------------------------

def _check_invariants(state: ILFState) -> list[str]:
    violations: list[str] = []
    if state.long_exposure < 0:
        violations.append("long_exposure_nonneg")
    if state.short_exposure < 0:
        violations.append("short_exposure_nonneg")
    if state.premium_pool < 0:
        violations.append("premium_pool_nonneg")
    if state.margin_pool < 0:
        violations.append("margin_pool_nonneg")
    if state.protocol_fee_pool < 0:
        violations.append("protocol_fee_nonneg")
    if state.protocol_fee_pool > MAX_AMOUNT:
        violations.append("protocol_fee_overflow")
    # margin_pool must equal short_exposure (deposited 1:1)
    if state.margin_pool != state.short_exposure:
        violations.append("margin_short_consistent")
    # Leverage: long_exposure ≤ short_exposure * max_leverage / 10000
    # (skip if short == 0 and long == 0 — both zero is valid initial state)
    if state.short_exposure > 0:
        max_long = (state.short_exposure * state.max_leverage_bps) // BPS_DENOM
        if state.long_exposure > max_long:
            violations.append("leverage_exceeded")
    elif state.long_exposure > 0:
        violations.append("leverage_no_shorts")
    return violations


# ---------------------------------------------------------------------------
# Dispatch table
# ---------------------------------------------------------------------------

_DISPATCH = {
    ILFAction.OPEN_LONG_IL: (_guard_open_long, _update_open_long, _effect_open_long),
    ILFAction.OPEN_SHORT_IL: (_guard_open_short, _update_open_short, _effect_open_short),
    ILFAction.CLOSE_POSITION: (_guard_close_position, _update_close_position, _effect_close),
    ILFAction.SNAPSHOT_EPOCH_START: (_guard_snapshot, _update_snapshot, _effect_snapshot),
    ILFAction.SETTLE_IL_EPOCH: (_guard_settle, _update_settle, _effect_settle),
    ILFAction.ADVANCE_EPOCH: (_guard_advance, _update_advance, _effect_advance),
}


def step(state: ILFState, params: ILFActionParams) -> ILFStepResult:
    """Execute one IL futures action."""
    entry = _DISPATCH.get(params.action)
    if entry is None:
        return ILFStepResult(accepted=False, rejection=f"unknown_action:{params.action}")

    guard_fn, update_fn, effect_fn = entry

    if not guard_fn(state, params):
        return ILFStepResult(accepted=False, rejection="guard")

    new_state = update_fn(state, params)

    violations = _check_invariants(new_state)
    if violations:
        return ILFStepResult(
            accepted=False,
            rejection=f"invariant:{','.join(violations)}",
        )

    effect = effect_fn(new_state, params)
    return ILFStepResult(accepted=True, state=new_state, effect=effect)
