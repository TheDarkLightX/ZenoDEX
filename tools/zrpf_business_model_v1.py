"""Exact research model for ZRPF fees, procurement, and ZDEX incentives.

The module is an advisory functional core.  It uses checked integer arithmetic
and grants no fee, payment, proof-admission, burn, finality, or release
authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from typing import Final

BPS: Final = 10_000
MAX_ATOMS: Final = 2**256 - 1
ZDEX_SCALE: Final = 10**18
ZDEX_INITIAL_SUPPLY_ATOMS: Final = 2_000_000_000 * ZDEX_SCALE
ZDEX_ACTIVE_FLOOR_ATOMS: Final = 200_000_000 * ZDEX_SCALE
PROOF_RESERVE_INITIAL_ATOMS: Final = 30_000_000 * ZDEX_SCALE
PROOF_RESERVE_FLOOR_ATOMS: Final = 1


def _exact_nonnegative(value: int, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_ATOMS:
        raise ValueError(f"{name} must be an exact integer in [0, 2^256-1]")
    return value


def ceil_div(numerator: int, denominator: int) -> int:
    _exact_nonnegative(numerator, "numerator")
    if type(denominator) is not int or denominator <= 0:
        raise ValueError("denominator must be a positive exact integer")
    return (numerator + denominator - 1) // denominator


def floor_bps(amount_atoms: int, rate_bps: int) -> int:
    _exact_nonnegative(amount_atoms, "amount_atoms")
    if type(rate_bps) is not int or not 0 <= rate_bps <= BPS:
        raise ValueError("rate_bps must be an exact integer in [0, 10000]")
    return amount_atoms * rate_bps // BPS


def ceil_bps(amount_atoms: int, rate_bps: int) -> int:
    _exact_nonnegative(amount_atoms, "amount_atoms")
    if type(rate_bps) is not int or rate_bps < 0:
        raise ValueError("rate_bps must be a nonnegative exact integer")
    return ceil_div(amount_atoms * rate_bps, BPS)


@dataclass(frozen=True, slots=True)
class ProofCostProfileV1:
    fixed_batch_atoms: int
    publication_atoms: int
    variable_atoms_per_resource_unit: int
    direct_atoms_per_resource_unit: int
    maximum_resource_units: int = 1_024


@dataclass(frozen=True, slots=True)
class ProofBatchAssessmentV1:
    resource_units: int
    raw_proof_cost_atoms: int
    maximum_proof_liability_atoms: int
    direct_cost_atoms: int
    charged_atoms_per_resource_unit: int
    collected_resource_fee_atoms: int
    refundable_rounding_atoms: int
    zrpf_economic: bool


def assess_proof_batch(
    profile: ProofCostProfileV1,
    resource_units: int,
    proof_cost_multiplier_bps: int,
    contingency_bps: int,
) -> ProofBatchAssessmentV1:
    """Compare a prefunded ZRPF batch with the same-unit direct fallback."""

    for name, value in (
        ("fixed_batch_atoms", profile.fixed_batch_atoms),
        ("publication_atoms", profile.publication_atoms),
        ("variable_atoms_per_resource_unit", profile.variable_atoms_per_resource_unit),
        ("direct_atoms_per_resource_unit", profile.direct_atoms_per_resource_unit),
        ("maximum_resource_units", profile.maximum_resource_units),
        ("resource_units", resource_units),
    ):
        _exact_nonnegative(value, name)
    if resource_units == 0 or resource_units > profile.maximum_resource_units:
        raise ValueError("resource_units must be in the selected batch domain")
    if type(proof_cost_multiplier_bps) is not int or proof_cost_multiplier_bps <= 0:
        raise ValueError("proof_cost_multiplier_bps must be positive")
    if type(contingency_bps) is not int or contingency_bps < 0:
        raise ValueError("contingency_bps must be nonnegative")

    base_cost_atoms = (
        profile.fixed_batch_atoms
        + profile.publication_atoms
        + profile.variable_atoms_per_resource_unit * resource_units
    )
    raw_proof_cost_atoms = ceil_bps(base_cost_atoms, proof_cost_multiplier_bps)
    maximum_proof_liability_atoms = ceil_bps(
        raw_proof_cost_atoms, BPS + contingency_bps
    )
    direct_cost_atoms = profile.direct_atoms_per_resource_unit * resource_units
    charged_atoms_per_resource_unit = ceil_div(
        maximum_proof_liability_atoms, resource_units
    )
    collected_resource_fee_atoms = charged_atoms_per_resource_unit * resource_units
    return ProofBatchAssessmentV1(
        resource_units=resource_units,
        raw_proof_cost_atoms=raw_proof_cost_atoms,
        maximum_proof_liability_atoms=maximum_proof_liability_atoms,
        direct_cost_atoms=direct_cost_atoms,
        charged_atoms_per_resource_unit=charged_atoms_per_resource_unit,
        collected_resource_fee_atoms=collected_resource_fee_atoms,
        refundable_rounding_atoms=(
            collected_resource_fee_atoms - maximum_proof_liability_atoms
        ),
        zrpf_economic=maximum_proof_liability_atoms <= direct_cost_atoms,
    )


def minimum_economic_batch_units(
    profile: ProofCostProfileV1,
    proof_cost_multiplier_bps: int,
    contingency_bps: int,
) -> int | None:
    """Return the first exact bounded occupancy where ZRPF beats direct mode."""

    for resource_units in range(1, profile.maximum_resource_units + 1):
        assessment = assess_proof_batch(
            profile,
            resource_units,
            proof_cost_multiplier_bps,
            contingency_bps,
        )
        if assessment.zrpf_economic:
            return resource_units
    return None


class ProcurementKindV1(StrEnum):
    FIRST_VALID_RACE = "FIRST_VALID_RACE"
    REVERSE_DUTCH_LOCK = "REVERSE_DUTCH_LOCK"
    PAY_AS_BID = "PAY_AS_BID"
    SECOND_PRICE = "SECOND_PRICE"


@dataclass(frozen=True, slots=True)
class ProverV1:
    prover_id: str
    cost_atoms: int
    latency_rank: int
    beneficial_owner_id: str
    failure_domain_id: str


@dataclass(frozen=True, slots=True)
class ProcurementOutcomeV1:
    kind: ProcurementKindV1
    winner_id: str | None
    payment_atoms: int
    useful_compute_cost_atoms: int
    total_compute_cost_atoms: int
    duplicate_compute_waste_atoms: int
    fallback_required: bool


def _validate_provers(provers: tuple[ProverV1, ...]) -> None:
    if not provers:
        raise ValueError("at least one prover is required")
    if len({prover.prover_id for prover in provers}) != len(provers):
        raise ValueError("prover IDs must be unique")
    for prover in provers:
        _exact_nonnegative(prover.cost_atoms, "prover.cost_atoms")
        if prover.cost_atoms == 0 or prover.latency_rank <= 0:
            raise ValueError("prover cost and latency rank must be positive")


def first_valid_race(
    provers: tuple[ProverV1, ...], reward_atoms: int
) -> ProcurementOutcomeV1:
    """Model the duplicate-compute cost of an open first-valid race."""

    _validate_provers(provers)
    _exact_nonnegative(reward_atoms, "reward_atoms")
    winner = min(provers, key=lambda prover: (prover.latency_rank, prover.prover_id))
    total_compute_cost_atoms = sum(prover.cost_atoms for prover in provers)
    return ProcurementOutcomeV1(
        kind=ProcurementKindV1.FIRST_VALID_RACE,
        winner_id=winner.prover_id,
        payment_atoms=reward_atoms,
        useful_compute_cost_atoms=winner.cost_atoms,
        total_compute_cost_atoms=total_compute_cost_atoms,
        duplicate_compute_waste_atoms=total_compute_cost_atoms - winner.cost_atoms,
        fallback_required=False,
    )


def reverse_dutch_lock(
    provers: tuple[ProverV1, ...],
    minimum_price_atoms: int,
    maximum_price_atoms: int,
    price_step_atoms: int,
    *,
    collusive_wait: bool = False,
) -> ProcurementOutcomeV1:
    """Model a rising-price lock auction with one assigned computation."""

    _validate_provers(provers)
    for name, value in (
        ("minimum_price_atoms", minimum_price_atoms),
        ("maximum_price_atoms", maximum_price_atoms),
        ("price_step_atoms", price_step_atoms),
    ):
        _exact_nonnegative(value, name)
    if price_step_atoms == 0 or minimum_price_atoms > maximum_price_atoms:
        raise ValueError("invalid reverse-Dutch price interval")
    eligible = tuple(
        prover for prover in provers if prover.cost_atoms <= maximum_price_atoms
    )
    if not eligible:
        return ProcurementOutcomeV1(
            kind=ProcurementKindV1.REVERSE_DUTCH_LOCK,
            winner_id=None,
            payment_atoms=0,
            useful_compute_cost_atoms=0,
            total_compute_cost_atoms=0,
            duplicate_compute_waste_atoms=0,
            fallback_required=True,
        )
    winner = min(eligible, key=lambda prover: (prover.cost_atoms, prover.prover_id))
    if collusive_wait:
        payment_atoms = maximum_price_atoms
    else:
        steps = ceil_div(
            max(0, winner.cost_atoms - minimum_price_atoms), price_step_atoms
        )
        payment_atoms = min(
            maximum_price_atoms, minimum_price_atoms + steps * price_step_atoms
        )
    return ProcurementOutcomeV1(
        kind=ProcurementKindV1.REVERSE_DUTCH_LOCK,
        winner_id=winner.prover_id,
        payment_atoms=payment_atoms,
        useful_compute_cost_atoms=winner.cost_atoms,
        total_compute_cost_atoms=winner.cost_atoms,
        duplicate_compute_waste_atoms=0,
        fallback_required=False,
    )


def sealed_bid_procurement(
    provers: tuple[ProverV1, ...],
    bids_atoms: dict[str, int],
    maximum_price_atoms: int,
    kind: ProcurementKindV1,
) -> ProcurementOutcomeV1:
    """Evaluate bounded pay-as-bid or second-price proof procurement."""

    _validate_provers(provers)
    if kind not in {ProcurementKindV1.PAY_AS_BID, ProcurementKindV1.SECOND_PRICE}:
        raise ValueError("sealed bid kind must be pay-as-bid or second-price")
    _exact_nonnegative(maximum_price_atoms, "maximum_price_atoms")
    if set(bids_atoms) != {prover.prover_id for prover in provers}:
        raise ValueError("every prover must have exactly one bid")
    ranked: list[tuple[int, str, ProverV1]] = []
    by_id = {prover.prover_id: prover for prover in provers}
    for prover_id, bid_atoms in bids_atoms.items():
        _exact_nonnegative(bid_atoms, "bid_atoms")
        if bid_atoms <= maximum_price_atoms:
            ranked.append((bid_atoms, prover_id, by_id[prover_id]))
    ranked.sort(key=lambda item: (item[0], item[1]))
    if not ranked:
        return ProcurementOutcomeV1(kind, None, 0, 0, 0, 0, True)
    winning_bid, _, winner = ranked[0]
    if kind is ProcurementKindV1.SECOND_PRICE and len(ranked) > 1:
        payment_atoms = ranked[1][0]
    else:
        payment_atoms = winning_bid
    return ProcurementOutcomeV1(
        kind=kind,
        winner_id=winner.prover_id,
        payment_atoms=payment_atoms,
        useful_compute_cost_atoms=winner.cost_atoms,
        total_compute_cost_atoms=winner.cost_atoms,
        duplicate_compute_waste_atoms=0,
        fallback_required=False,
    )


def bond_covers_default(
    maximum_defect_gain_atoms: int,
    slash_atoms: int,
    future_value_lost_atoms: int,
    detection_probability_bps: int,
) -> bool:
    """Cross-multiplied skin-in-the-game condition from the mechanism contract."""

    for name, value in (
        ("maximum_defect_gain_atoms", maximum_defect_gain_atoms),
        ("slash_atoms", slash_atoms),
        ("future_value_lost_atoms", future_value_lost_atoms),
    ):
        _exact_nonnegative(value, name)
    if not 0 <= detection_probability_bps <= BPS:
        raise ValueError("detection_probability_bps is outside [0, 10000]")
    downside = (
        detection_probability_bps * slash_atoms + BPS * future_value_lost_atoms
    )
    return downside >= BPS * maximum_defect_gain_atoms


@dataclass(frozen=True, slots=True)
class FeeWaterfallInputV1:
    finalized_protocol_revenue_atoms: int
    unrestricted_carry_atoms: int
    safety_reserve_gap_atoms: int
    critical_service_prefund_gap_atoms: int
    operations_prefund_gap_atoms: int
    admitted_growth_budget_cap_atoms: int
    buyburn_active: bool


@dataclass(frozen=True, slots=True)
class FeeWaterfallOutcomeV1:
    available_atoms: int
    safety_atoms: int
    critical_service_atoms: int
    operations_atoms: int
    growth_atoms: int
    burn_atoms: int
    carry_atoms: int
    all_required_prefunded: bool


def allocate_fee_waterfall(request: FeeWaterfallInputV1) -> FeeWaterfallOutcomeV1:
    """Allocate finalized unrestricted revenue in strict liability-first order."""

    for field_name in (
        "finalized_protocol_revenue_atoms",
        "unrestricted_carry_atoms",
        "safety_reserve_gap_atoms",
        "critical_service_prefund_gap_atoms",
        "operations_prefund_gap_atoms",
        "admitted_growth_budget_cap_atoms",
    ):
        _exact_nonnegative(getattr(request, field_name), field_name)
    available_atoms = (
        request.finalized_protocol_revenue_atoms + request.unrestricted_carry_atoms
    )
    safety_atoms = min(available_atoms, request.safety_reserve_gap_atoms)
    remaining_atoms = available_atoms - safety_atoms
    critical_service_atoms = min(
        remaining_atoms, request.critical_service_prefund_gap_atoms
    )
    remaining_atoms -= critical_service_atoms
    operations_atoms = min(remaining_atoms, request.operations_prefund_gap_atoms)
    remaining_atoms -= operations_atoms
    all_required_prefunded = (
        safety_atoms == request.safety_reserve_gap_atoms
        and critical_service_atoms == request.critical_service_prefund_gap_atoms
        and operations_atoms == request.operations_prefund_gap_atoms
    )
    if not all_required_prefunded:
        growth_atoms = 0
        burn_atoms = 0
        carry_atoms = remaining_atoms
    else:
        growth_atoms = min(remaining_atoms, request.admitted_growth_budget_cap_atoms)
        remaining_atoms -= growth_atoms
        burn_atoms = remaining_atoms if request.buyburn_active else 0
        carry_atoms = 0 if request.buyburn_active else remaining_atoms
    return FeeWaterfallOutcomeV1(
        available_atoms=available_atoms,
        safety_atoms=safety_atoms,
        critical_service_atoms=critical_service_atoms,
        operations_atoms=operations_atoms,
        growth_atoms=growth_atoms,
        burn_atoms=burn_atoms,
        carry_atoms=carry_atoms,
        all_required_prefunded=all_required_prefunded,
    )


def gross_revenue_burn_mutant(
    available_atoms: int, gross_burn_bps: int
) -> tuple[int, int]:
    """Unsafe comparator: burn a fixed gross share before paying obligations."""

    burn_atoms = floor_bps(available_atoms, gross_burn_bps)
    return burn_atoms, available_atoms - burn_atoms


def maximum_zdex_burn_atoms(supply_before_atoms: int) -> int:
    """Zeno cap: every burn leaves strictly positive excess over the floor."""

    _exact_nonnegative(supply_before_atoms, "supply_before_atoms")
    if supply_before_atoms <= ZDEX_ACTIVE_FLOOR_ATOMS:
        return 0
    return (supply_before_atoms - ZDEX_ACTIVE_FLOOR_ATOMS) // 2


def required_fee_credit_volume_lift_bps(credit_bps: int) -> int | None:
    """Minimum gross-fee volume lift needed to offset a fully redeemed credit."""

    if type(credit_bps) is not int or not 0 <= credit_bps <= BPS:
        raise ValueError("credit_bps must be in [0, 10000]")
    if credit_bps == BPS:
        return None
    retained_bps = BPS - credit_bps
    return ceil_div(BPS * BPS, retained_bps) - BPS


def wash_round_trip_profit_atoms(
    irreversible_protocol_fee_atoms: int, credit_bps: int
) -> int:
    """Upper-bound direct farming profit before gas, slippage, and capital cost."""

    credit_atoms = floor_bps(irreversible_protocol_fee_atoms, credit_bps)
    return credit_atoms - irreversible_protocol_fee_atoms


def break_even_annual_volume_atoms(
    annual_fixed_cost_atoms: int, net_protocol_take_bps: int
) -> int:
    _exact_nonnegative(annual_fixed_cost_atoms, "annual_fixed_cost_atoms")
    if type(net_protocol_take_bps) is not int or net_protocol_take_bps <= 0:
        raise ValueError("net_protocol_take_bps must be positive")
    return ceil_div(annual_fixed_cost_atoms * BPS, net_protocol_take_bps)


def subsidy_runway_days(
    reserve_whole_zdex: int,
    quote_atoms_per_zdex: int,
    daily_shortfall_quote_atoms: int,
) -> int | None:
    """Illustrate why a volatile token reserve cannot prove recurring solvency."""

    for name, value in (
        ("reserve_whole_zdex", reserve_whole_zdex),
        ("quote_atoms_per_zdex", quote_atoms_per_zdex),
        ("daily_shortfall_quote_atoms", daily_shortfall_quote_atoms),
    ):
        _exact_nonnegative(value, name)
    if daily_shortfall_quote_atoms == 0:
        return None
    return reserve_whole_zdex * quote_atoms_per_zdex // daily_shortfall_quote_atoms


def stress_runway_baseline_cost_months(
    stress_months: int,
    revenue_multiplier_bps: int,
    cost_multiplier_bps: int,
) -> int:
    """Return required runway in 1/10000 baseline-month units at break-even."""

    for name, value in (
        ("stress_months", stress_months),
        ("revenue_multiplier_bps", revenue_multiplier_bps),
        ("cost_multiplier_bps", cost_multiplier_bps),
    ):
        _exact_nonnegative(value, name)
    monthly_draw_bps = max(0, cost_multiplier_bps - revenue_multiplier_bps)
    return stress_months * monthly_draw_bps


@dataclass(frozen=True, slots=True)
class ProofBonusScheduleV1:
    opening_reserve_atoms: int
    reserve_floor_atoms: int
    daily_release_bps: int


@dataclass(frozen=True, slots=True)
class ProofBonusSimulationV1:
    epochs: int
    released_atoms: int
    closing_reserve_atoms: int
    zero_release_epoch: int | None


def simulate_proof_bonus(
    policy: ProofBonusScheduleV1, epochs: int
) -> ProofBonusSimulationV1:
    """Release a geometric, work-contingent bonus without crossing its floor."""

    for name, value in (
        ("opening_reserve_atoms", policy.opening_reserve_atoms),
        ("reserve_floor_atoms", policy.reserve_floor_atoms),
        ("daily_release_bps", policy.daily_release_bps),
        ("epochs", epochs),
    ):
        _exact_nonnegative(value, name)
    if policy.reserve_floor_atoms > policy.opening_reserve_atoms:
        raise ValueError("proof reserve floor exceeds the opening reserve")
    if not 0 <= policy.daily_release_bps <= BPS:
        raise ValueError("daily_release_bps must be in [0, 10000]")
    reserve_atoms = policy.opening_reserve_atoms
    released_atoms = 0
    zero_release_epoch: int | None = None
    for epoch in range(1, epochs + 1):
        excess_atoms = reserve_atoms - policy.reserve_floor_atoms
        release_atoms = floor_bps(excess_atoms, policy.daily_release_bps)
        if release_atoms == 0 and zero_release_epoch is None:
            zero_release_epoch = epoch
        reserve_atoms -= release_atoms
        released_atoms += release_atoms
    return ProofBonusSimulationV1(
        epochs=epochs,
        released_atoms=released_atoms,
        closing_reserve_atoms=reserve_atoms,
        zero_release_epoch=zero_release_epoch,
    )
