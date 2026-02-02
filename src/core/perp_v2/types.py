"""Data types for the `perp_v2` risk engine.

All types are frozen dataclasses (immutable). Field names and defaults match
`src/kernels/dex/perp_epoch_isolated_v2.yaml`.

Units/conventions:
- `*_e8` prices are quote-per-base scaled by 1e8.
- `*_bps` rates are basis points (1/10_000).
- `position_base` is signed base units (long > 0, short < 0).
- `*_quote` values are integer quote units.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, unique


@unique
class Action(Enum):
    """One member per ESSO action id."""
    ADVANCE_EPOCH = "advance_epoch"
    PUBLISH_CLEARING_PRICE = "publish_clearing_price"
    SETTLE_EPOCH = "settle_epoch"
    DEPOSIT_COLLATERAL = "deposit_collateral"
    WITHDRAW_COLLATERAL = "withdraw_collateral"
    SET_POSITION = "set_position"
    CLEAR_BREAKER = "clear_breaker"
    APPLY_FUNDING = "apply_funding"
    DEPOSIT_INSURANCE = "deposit_insurance"
    APPLY_INSURANCE_CLAIM = "apply_insurance_claim"


@unique
class Event(Enum):
    """One member per ESSO effect event type."""
    EPOCH_ADVANCED = "EpochAdvanced"
    CLEARING_PRICE_PUBLISHED = "ClearingPricePublished"
    EPOCH_SETTLED = "EpochSettled"
    COLLATERAL_DEPOSITED = "CollateralDeposited"
    COLLATERAL_WITHDRAWN = "CollateralWithdrawn"
    POSITION_SET = "PositionSet"
    BREAKER_CLEARED = "BreakerCleared"
    FUNDING_APPLIED = "FundingApplied"
    INSURANCE_DEPOSITED = "InsuranceDeposited"
    INSURANCE_CLAIM_PAID = "InsuranceClaimPaid"


@dataclass(frozen=True)
class PerpState:
    """Complete state of the single-account `perp_epoch_isolated_v2` kernel."""

    # Epoch
    now_epoch: int = 0

    # Circuit breaker
    breaker_active: bool = False
    breaker_last_trigger_epoch: int = 0

    # Clearing price oracle
    clearing_price_seen: bool = False
    clearing_price_epoch: int = 0
    clearing_price_e8: int = 0

    # Index/mark oracle
    oracle_seen: bool = False
    oracle_last_update_epoch: int = 0
    index_price_e8: int = 0

    # Control parameters
    max_oracle_staleness_epochs: int = 100
    max_oracle_move_bps: int = 500
    initial_margin_bps: int = 1000
    maintenance_margin_bps: int = 500
    depeg_buffer_bps: int = 100
    liquidation_penalty_bps: int = 50
    max_position_abs: int = 1000000

    # Position + collateral
    position_base: int = 0
    entry_price_e8: int = 0
    collateral_quote: int = 0
    fee_pool_quote: int = 0

    # Funding (v2)
    funding_rate_bps: int = 0
    funding_cap_bps: int = 100
    funding_paid_cumulative: int = 0

    # Insurance (v2)
    insurance_balance: int = 0
    initial_insurance: int = 0
    fee_income: int = 0
    claims_paid: int = 0

    # Anti-bounty-farming (v2)
    min_notional_for_bounty: int = 100000000

    # Epoch gate for funding (v2)
    funding_last_applied_epoch: int = 0

    # Liquidation tracking (v2)
    liquidated_this_step: bool = False


@dataclass(frozen=True)
class ActionParams:
    """Parameters for an action. Unused fields default to 0/False."""

    action: Action
    delta: int = 0                # advance_epoch
    price_e8: int = 0             # publish_clearing_price
    amount: int = 0               # deposit_collateral / withdraw_collateral / deposit_insurance
    new_position_base: int = 0    # set_position
    new_rate_bps: int = 0         # apply_funding
    claim_amount: int = 0         # apply_insurance_claim
    auth_ok: bool = False         # shared: deposit/withdraw/set_position/clear/funding/claim


@dataclass(frozen=True)
class Effect:
    """Post-state observables emitted after a successful step."""

    event: Event
    oracle_fresh: bool = False
    notional_quote: int = 0
    effective_maint_bps: int = 0
    maint_req_quote: int = 0
    init_req_quote: int = 0
    margin_ok: bool = True
    liquidated: bool = False
    collateral_after: int = 0
    fee_pool_after: int = 0
    insurance_after: int = 0


@dataclass(frozen=True)
class StepResult:
    """Result of a single engine step."""

    accepted: bool
    state: PerpState | None = None
    effect: Effect | None = None
    rejection: str | None = None
