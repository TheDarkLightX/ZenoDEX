"""Pure integer decision procedure for zUSD redemption admission."""

from __future__ import annotations

from dataclasses import dataclass

E8 = 100_000_000
BPS_SCALE = 10_000
MAX_TCR_BPS = 1_000_000


def _require_int(
    value: object,
    *,
    name: str,
    minimum: int = 0,
    maximum: int | None = None,
) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    value_i = int(value)
    if value_i < minimum:
        raise ValueError(f"{name} must be >= {minimum}")
    if maximum is not None and value_i > maximum:
        raise ValueError(f"{name} must be <= {maximum}")
    return value_i


def _ratio_at_least(
    *,
    collateral_e8: int,
    debt_e8: int,
    price_e8: int,
    threshold_bps: int,
) -> bool:
    if debt_e8 == 0:
        return True
    return (
        collateral_e8 * price_e8 * BPS_SCALE
        >= debt_e8 * threshold_bps * E8
    )


@dataclass(frozen=True)
class ZUSDRedemptionGuardDecision:
    """Complete, replayable decision vector for one redemption."""

    branch_tcr_ok: bool
    post_tcr_ok: bool
    epoch_cap_ok: bool
    no_liquidation_priority: bool
    epoch_cap_e8: int

    @property
    def accepted(self) -> bool:
        return (
            self.branch_tcr_ok
            and self.post_tcr_ok
            and self.epoch_cap_ok
            and self.no_liquidation_priority
        )

    @property
    def error(self) -> str | None:
        if not self.branch_tcr_ok:
            return "redemption blocked: branch below shutdown TCR"
        if not self.no_liquidation_priority:
            return "redemption blocked: liquidation has priority"
        if not self.epoch_cap_ok:
            return "redemption blocked: epoch cap exceeded"
        if not self.post_tcr_ok:
            return "redemption blocked: post-redemption TCR below floor"
        return None


@dataclass(frozen=True)
class ZUSDLiquityV1RedemptionDecision:
    """Source-exact global admission decision for the minimum V1 profile.

    Liquity V1 has one global collateralization guard before redemption
    traversal: the complete system TCR must be at least MCR.  Candidate
    eligibility, dust, hints, balance, fees, and prefix execution belong to
    their own transition stages.  Experimental post-TCR floors and epoch
    throttles have no fields in this decision and therefore cannot acquire
    baseline admission authority.
    """

    pre_system_tcr_at_least_mcr: bool

    @property
    def accepted(self) -> bool:
        return self.pre_system_tcr_at_least_mcr

    @property
    def error(self) -> str | None:
        if not self.pre_system_tcr_at_least_mcr:
            return "redemption blocked: system TCR below MCR"
        return None


@dataclass(frozen=True)
class ZUSDUnmountedRedemptionDrainGuardContext:
    """All state and policy owned by the unmounted drain-guard experiment.

    This type has no embedding in ``ZUSDState`` or ``ZUSDMultiState`` and no
    mounted command constructs it. It provides arithmetic research coverage
    only. Promotion requires a distinct versioned protocol profile, state
    machine, route grammar, and refinement proof.
    """

    epoch_redemption_used_e8: int
    branch_tcr_floor_bps: int
    min_post_tcr_bps: int
    max_epoch_redemption_fraction_bps: int

    def __post_init__(self) -> None:
        _require_int(
            self.epoch_redemption_used_e8,
            name="epoch_redemption_used_e8",
        )
        _require_int(
            self.branch_tcr_floor_bps,
            name="branch_tcr_floor_bps",
            maximum=MAX_TCR_BPS,
        )
        _require_int(
            self.min_post_tcr_bps,
            name="min_post_tcr_bps",
            maximum=MAX_TCR_BPS,
        )
        _require_int(
            self.max_epoch_redemption_fraction_bps,
            name="max_epoch_redemption_fraction_bps",
            maximum=BPS_SCALE,
        )


def evaluate_liquity_v1_minimum_redemption_guard(
    *,
    system_collateral_e8: int,
    system_debt_e8: int,
    price_e8: int,
    mcr_bps: int,
) -> ZUSDLiquityV1RedemptionDecision:
    """Check the complete Liquity V1 global redemption gate.

    Inputs are explicit non-negative E8 quantities and a positive E8 price.
    Zero debt satisfies the ratio predicate, matching the source ratio helper;
    later amount and balance guards reject an impossible positive redemption.
    """

    collateral = _require_int(
        system_collateral_e8,
        name="system_collateral_e8",
    )
    debt = _require_int(system_debt_e8, name="system_debt_e8")
    price = _require_int(price_e8, name="price_e8", minimum=1)
    mcr = _require_int(
        mcr_bps,
        name="mcr_bps",
        minimum=1,
        maximum=MAX_TCR_BPS,
    )
    return ZUSDLiquityV1RedemptionDecision(
        pre_system_tcr_at_least_mcr=_ratio_at_least(
            collateral_e8=collateral,
            debt_e8=debt,
            price_e8=price,
            threshold_bps=mcr,
        )
    )


def evaluate_redemption_guard(
    *,
    collateral_e8: int,
    debt_e8: int,
    price_e8: int,
    post_collateral_e8: int,
    post_debt_e8: int,
    redeem_e8: int,
    extension_context: ZUSDUnmountedRedemptionDrainGuardContext,
    no_liquidation_priority: bool,
) -> ZUSDRedemptionGuardDecision:
    """Evaluate the unmounted experimental drain-guard profile.

    The epoch cap is derived from the pre-transition branch debt. The caller
    supplies post-state active collateral and debt, which are bound here to
    monotone debt reduction before their ratio is checked.  This decision is
    intentionally absent from the Liquity V1 minimum transition union because
    its extra rejects narrow the pinned source liveness contract.
    """

    collateral = _require_int(collateral_e8, name="collateral_e8")
    debt = _require_int(debt_e8, name="debt_e8", minimum=1)
    price = _require_int(price_e8, name="price_e8", minimum=1)
    post_collateral = _require_int(
        post_collateral_e8,
        name="post_collateral_e8",
    )
    post_debt = _require_int(post_debt_e8, name="post_debt_e8")
    redeem = _require_int(redeem_e8, name="redeem_e8", minimum=1)
    if type(extension_context) is not ZUSDUnmountedRedemptionDrainGuardContext:
        raise TypeError(
            "extension_context must be a ZUSDUnmountedRedemptionDrainGuardContext"
        )
    if type(no_liquidation_priority) is not bool:
        raise TypeError("no_liquidation_priority must be a bool")
    if redeem > debt:
        raise ValueError("redeem_e8 cannot exceed debt_e8")
    if post_debt != debt - redeem:
        raise ValueError("post_debt_e8 must equal debt_e8 - redeem_e8")
    if post_collateral > collateral:
        raise ValueError("post_collateral_e8 cannot exceed collateral_e8")

    epoch_cap = (
        debt * extension_context.max_epoch_redemption_fraction_bps // BPS_SCALE
    )
    return ZUSDRedemptionGuardDecision(
        branch_tcr_ok=_ratio_at_least(
            collateral_e8=collateral,
            debt_e8=debt,
            price_e8=price,
            threshold_bps=extension_context.branch_tcr_floor_bps,
        ),
        post_tcr_ok=_ratio_at_least(
            collateral_e8=post_collateral,
            debt_e8=post_debt,
            price_e8=price,
            threshold_bps=extension_context.min_post_tcr_bps,
        ),
        epoch_cap_ok=(
            extension_context.epoch_redemption_used_e8 + redeem <= epoch_cap
        ),
        no_liquidation_priority=no_liquidation_priority,
        epoch_cap_e8=epoch_cap,
    )
