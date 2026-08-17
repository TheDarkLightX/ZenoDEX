"""Exact research calibration for ZenoProof auction and capacity parameters.

All monetary quantities use integer micro-USD atoms.  The module performs no
I/O and grants no pricing, payment, proof-admission, scheduling, or settlement
authority.  Its source-informed scenarios are sensitivity inputs rather than
live-market measurements.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from typing import Final, Iterable

BPS: Final = 10_000
MICRO_USD_PER_USD: Final = 1_000_000
SECONDS_PER_HOUR: Final = 3_600
MAX_ATOMS: Final = 2**256 - 1


def exact_nonnegative(value: int, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_ATOMS:
        raise ValueError(f"{name} must be an exact integer in [0, 2^256-1]")
    return value


def ceil_div(numerator: int, denominator: int) -> int:
    exact_nonnegative(numerator, "numerator")
    if (
        type(denominator) is not int
        or denominator <= 0
        or denominator > MAX_ATOMS
    ):
        raise ValueError("denominator must be a positive exact integer")
    return numerator // denominator + int(numerator % denominator != 0)


def floor_bps(amount: int, rate_bps: int) -> int:
    exact_nonnegative(amount, "amount")
    if type(rate_bps) is not int or not 0 <= rate_bps <= MAX_ATOMS:
        raise ValueError("rate_bps must be a nonnegative exact integer")
    amount_whole, amount_remainder = divmod(amount, BPS)
    if amount_whole and rate_bps > MAX_ATOMS // amount_whole:
        raise ValueError("amount_times_rate_bps must fit after basis-point scaling")

    rate_whole, rate_remainder = divmod(rate_bps, BPS)
    whole_scaled = amount_whole * rate_bps
    remainder_scaled = amount_remainder * rate_whole + (
        amount_remainder * rate_remainder
    ) // BPS
    if remainder_scaled > MAX_ATOMS - whole_scaled:
        raise ValueError("amount_times_rate_bps must fit after basis-point scaling")
    return whole_scaled + remainder_scaled


def ceil_bps(amount: int, rate_bps: int) -> int:
    rounded_down = floor_bps(amount, rate_bps)
    has_remainder = (amount % BPS) * (rate_bps % BPS) % BPS != 0
    if has_remainder and rounded_down == MAX_ATOMS:
        raise ValueError("amount_times_rate_bps must fit after basis-point scaling")
    return rounded_down + int(has_remainder)


class BondRuleV1(StrEnum):
    LOSS_BASED = "LOSS_BASED"
    STATIC_MULTIPLE = "STATIC_MULTIPLE"


@dataclass(frozen=True, slots=True)
class WorkloadClassV1:
    workload_id: str
    weight_bps: int
    mcycles: int
    buyer_delay_damage_atoms: int
    reprocurement_coverage_bps: int


@dataclass(frozen=True, slots=True)
class CostShockV1:
    shock_id: str
    weight_bps: int
    compute_cost_multiplier_bps: int
    throughput_multiplier_bps: int
    failure_probability_add_bps: int


@dataclass(frozen=True, slots=True)
class ProverProfileV1:
    prover_id: str
    beneficial_owner_id: str
    throughput_khz: int
    hourly_compute_cost_atoms: int
    fixed_job_cost_atoms: int
    maximum_lock_bond_atoms: int
    failure_probability_bps: int
    minimum_margin_bps: int


@dataclass(frozen=True, slots=True)
class AuctionPolicyV1:
    policy_id: str
    minimum_price_cost_bps: int
    maximum_price_cost_bps: int
    primary_window_factor_bps: int
    ramp_duration_factor_bps: int
    publication_buffer_seconds: int
    bond_rule: BondRuleV1
    static_bond_multiple_bps: int


@dataclass(frozen=True, slots=True)
class ProverBidAssessmentV1:
    prover_id: str
    beneficial_owner_id: str
    proving_seconds: int
    compute_cost_atoms: int
    bond_atoms: int
    reservation_price_atoms: int
    lock_elapsed_seconds: int
    effective_work_seconds: int
    required_work_seconds: int
    eligible: bool
    rejection_codes: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class AuctionScenarioOutcomeV1:
    scenario_id: str
    scenario_weight_bps: int
    workload_id: str
    shock_id: str
    reference_cost_atoms: int
    minimum_price_atoms: int
    maximum_price_atoms: int
    required_bond_atoms: int
    offered_bond_atoms: int
    competitive_winner_id: str | None
    competitive_winner_owner_id: str | None
    competitive_payment_atoms: int
    collusive_payment_atoms: int
    collusive_uplift_atoms: int
    eligible_owner_count: int
    bond_excluded_prover_count: int
    price_excluded_prover_count: int
    window_excluded_prover_count: int
    admitted_late_prover_count: int
    fallback_required: bool
    bids: tuple[ProverBidAssessmentV1, ...]


@dataclass(frozen=True, slots=True)
class AuctionPolicyEvaluationV1:
    policy_id: str
    fulfillment_bps: int
    fallback_bps: int
    average_competitive_payment_atoms: int
    average_price_to_reference_bps: int
    collusive_uplift_bps: int
    average_eligible_owner_fraction_bps: int
    maximum_winner_owner_share_bps: int
    bond_exclusion_bps: int
    price_exclusion_bps: int
    window_exclusion_bps: int
    admitted_late_count: int
    outcomes: tuple[AuctionScenarioOutcomeV1, ...]


def _validate_weight(weight_bps: int, name: str) -> None:
    if type(weight_bps) is not int or not 0 <= weight_bps <= BPS:
        raise ValueError(f"{name} must be in [0, 10000]")


def _validate_workload(workload: WorkloadClassV1) -> None:
    if not workload.workload_id:
        raise ValueError("workload_id must be nonempty")
    _validate_weight(workload.weight_bps, "workload.weight_bps")
    for field_name in ("mcycles", "buyer_delay_damage_atoms"):
        exact_nonnegative(getattr(workload, field_name), f"workload.{field_name}")
    if workload.mcycles == 0:
        raise ValueError("workload.mcycles must be positive")
    if workload.reprocurement_coverage_bps < BPS:
        raise ValueError("reprocurement coverage must be at least 10000 bps")


def _validate_shock(shock: CostShockV1) -> None:
    if not shock.shock_id:
        raise ValueError("shock_id must be nonempty")
    _validate_weight(shock.weight_bps, "shock.weight_bps")
    if shock.compute_cost_multiplier_bps <= 0:
        raise ValueError("compute cost multiplier must be positive")
    if shock.throughput_multiplier_bps <= 0:
        raise ValueError("throughput multiplier must be positive")
    _validate_weight(shock.failure_probability_add_bps, "failure add")


def _validate_prover(prover: ProverProfileV1) -> None:
    if not prover.prover_id or not prover.beneficial_owner_id:
        raise ValueError("prover and beneficial-owner IDs must be nonempty")
    for field_name in (
        "throughput_khz",
        "hourly_compute_cost_atoms",
        "fixed_job_cost_atoms",
        "maximum_lock_bond_atoms",
    ):
        exact_nonnegative(getattr(prover, field_name), f"prover.{field_name}")
    if prover.throughput_khz == 0:
        raise ValueError("prover throughput must be positive")
    _validate_weight(prover.failure_probability_bps, "failure probability")
    _validate_weight(prover.minimum_margin_bps, "minimum margin")


def _validate_policy(policy: AuctionPolicyV1) -> None:
    if not policy.policy_id:
        raise ValueError("policy_id must be nonempty")
    for field_name in (
        "minimum_price_cost_bps",
        "maximum_price_cost_bps",
        "primary_window_factor_bps",
        "ramp_duration_factor_bps",
        "publication_buffer_seconds",
        "static_bond_multiple_bps",
    ):
        exact_nonnegative(getattr(policy, field_name), f"policy.{field_name}")
    if policy.minimum_price_cost_bps > policy.maximum_price_cost_bps:
        raise ValueError("minimum price factor exceeds maximum price factor")
    if policy.primary_window_factor_bps == 0:
        raise ValueError("primary window factor must be positive")
    if policy.bond_rule is BondRuleV1.LOSS_BASED:
        if policy.static_bond_multiple_bps != 0:
            raise ValueError("loss-based bond cannot carry a static multiple")
    elif policy.static_bond_multiple_bps < BPS:
        raise ValueError("static bond multiple must be at least 10000 bps")


def proving_seconds(
    workload: WorkloadClassV1,
    prover: ProverProfileV1,
    shock: CostShockV1,
) -> int:
    """Return ceil(mcycles / shocked throughput), in exact seconds."""

    _validate_workload(workload)
    _validate_prover(prover)
    _validate_shock(shock)
    effective_throughput_khz = floor_bps(
        prover.throughput_khz,
        shock.throughput_multiplier_bps,
    )
    if effective_throughput_khz == 0:
        raise ValueError("shock reduces effective throughput to zero")
    return ceil_div(workload.mcycles * 1_000, effective_throughput_khz)


def compute_cost_atoms(
    workload: WorkloadClassV1,
    prover: ProverProfileV1,
    shock: CostShockV1,
) -> int:
    """Return shocked compute and per-job overhead in micro-USD atoms."""

    seconds = proving_seconds(workload, prover, shock)
    hourly_atoms = ceil_bps(
        prover.hourly_compute_cost_atoms,
        shock.compute_cost_multiplier_bps,
    )
    fixed_atoms = ceil_bps(
        prover.fixed_job_cost_atoms,
        shock.compute_cost_multiplier_bps,
    )
    result = ceil_div(hourly_atoms * seconds, SECONDS_PER_HOUR) + fixed_atoms
    return exact_nonnegative(result, "compute_cost_atoms")


def _base_shock() -> CostShockV1:
    return CostShockV1("REFERENCE_BASE", BPS, BPS, BPS, 0)


def _reference_cost_and_seconds(
    workload: WorkloadClassV1,
    reference_prover: ProverProfileV1,
) -> tuple[int, int]:
    shock = _base_shock()
    return (
        compute_cost_atoms(workload, reference_prover, shock),
        proving_seconds(workload, reference_prover, shock),
    )


def _bond_amounts(
    workload: WorkloadClassV1,
    maximum_price_atoms: int,
    policy: AuctionPolicyV1,
) -> tuple[int, int]:
    reprocurement_atoms = ceil_bps(
        maximum_price_atoms,
        workload.reprocurement_coverage_bps,
    )
    named_loss_atoms = reprocurement_atoms + workload.buyer_delay_damage_atoms
    required_bond_atoms = max(maximum_price_atoms, named_loss_atoms)
    offered_bond_atoms = required_bond_atoms
    if policy.bond_rule is BondRuleV1.STATIC_MULTIPLE:
        offered_bond_atoms = max(
            offered_bond_atoms,
            ceil_bps(maximum_price_atoms, policy.static_bond_multiple_bps),
        )
    return (
        exact_nonnegative(required_bond_atoms, "required_bond_atoms"),
        exact_nonnegative(offered_bond_atoms, "offered_bond_atoms"),
    )


def _lock_elapsed_seconds(
    *,
    reservation_price_atoms: int,
    minimum_price_atoms: int,
    maximum_price_atoms: int,
    ramp_duration_seconds: int,
) -> int:
    if reservation_price_atoms <= minimum_price_atoms:
        return 0
    if reservation_price_atoms >= maximum_price_atoms:
        return ramp_duration_seconds
    price_span_atoms = maximum_price_atoms - minimum_price_atoms
    return ceil_div(
        (reservation_price_atoms - minimum_price_atoms) * ramp_duration_seconds,
        price_span_atoms,
    )


def assess_prover_bid(
    workload: WorkloadClassV1,
    shock: CostShockV1,
    prover: ProverProfileV1,
    policy: AuctionPolicyV1,
    reference_prover: ProverProfileV1,
) -> ProverBidAssessmentV1:
    """Assess price, capital, and remaining-window admission for one prover."""

    _validate_policy(policy)
    reference_cost_atoms, reference_seconds = _reference_cost_and_seconds(
        workload,
        reference_prover,
    )
    minimum_price_atoms = ceil_bps(
        reference_cost_atoms,
        policy.minimum_price_cost_bps,
    )
    maximum_price_atoms = ceil_bps(
        reference_cost_atoms,
        policy.maximum_price_cost_bps,
    )
    _, offered_bond_atoms = _bond_amounts(workload, maximum_price_atoms, policy)
    actual_compute_cost_atoms = compute_cost_atoms(workload, prover, shock)
    proving_time_seconds = proving_seconds(workload, prover, shock)
    failure_bps = prover.failure_probability_bps + shock.failure_probability_add_bps
    if failure_bps >= BPS:
        raise ValueError("combined failure probability must be below 10000 bps")
    margin_atoms = ceil_bps(actual_compute_cost_atoms, prover.minimum_margin_bps)
    reservation_price_atoms = ceil_div(
        (actual_compute_cost_atoms + margin_atoms) * BPS
        + failure_bps * offered_bond_atoms,
        BPS - failure_bps,
    )
    ramp_duration_seconds = ceil_bps(
        reference_seconds,
        policy.ramp_duration_factor_bps,
    )
    initial_work_seconds = (
        ceil_bps(reference_seconds, policy.primary_window_factor_bps)
        + policy.publication_buffer_seconds
    )
    lock_elapsed_seconds = _lock_elapsed_seconds(
        reservation_price_atoms=reservation_price_atoms,
        minimum_price_atoms=minimum_price_atoms,
        maximum_price_atoms=maximum_price_atoms,
        ramp_duration_seconds=ramp_duration_seconds,
    )
    effective_work_seconds = max(0, initial_work_seconds - lock_elapsed_seconds)
    required_work_seconds = proving_time_seconds + policy.publication_buffer_seconds
    rejection_codes: list[str] = []
    if offered_bond_atoms > prover.maximum_lock_bond_atoms:
        rejection_codes.append("BOND_EXCEEDS_PROVER_CAPITAL")
    if reservation_price_atoms > maximum_price_atoms:
        rejection_codes.append("RESERVATION_EXCEEDS_PRICE_CEILING")
    if effective_work_seconds < required_work_seconds:
        rejection_codes.append("INSUFFICIENT_EFFECTIVE_WORK_WINDOW")
    return ProverBidAssessmentV1(
        prover_id=prover.prover_id,
        beneficial_owner_id=prover.beneficial_owner_id,
        proving_seconds=proving_time_seconds,
        compute_cost_atoms=actual_compute_cost_atoms,
        bond_atoms=offered_bond_atoms,
        reservation_price_atoms=reservation_price_atoms,
        lock_elapsed_seconds=lock_elapsed_seconds,
        effective_work_seconds=effective_work_seconds,
        required_work_seconds=required_work_seconds,
        eligible=not rejection_codes,
        rejection_codes=tuple(rejection_codes),
    )


def simulate_auction_scenario(
    workload: WorkloadClassV1,
    shock: CostShockV1,
    provers: tuple[ProverProfileV1, ...],
    policy: AuctionPolicyV1,
    reference_prover: ProverProfileV1,
) -> AuctionScenarioOutcomeV1:
    """Simulate one rising-price lock market with commit-time window checks."""

    if not provers:
        raise ValueError("at least one prover is required")
    if len({row.prover_id for row in provers}) != len(provers):
        raise ValueError("prover IDs must be unique")
    reference_cost_atoms, reference_seconds = _reference_cost_and_seconds(
        workload,
        reference_prover,
    )
    minimum_price_atoms = ceil_bps(
        reference_cost_atoms,
        policy.minimum_price_cost_bps,
    )
    maximum_price_atoms = ceil_bps(
        reference_cost_atoms,
        policy.maximum_price_cost_bps,
    )
    required_bond_atoms, offered_bond_atoms = _bond_amounts(
        workload,
        maximum_price_atoms,
        policy,
    )
    bids = tuple(
        assess_prover_bid(workload, shock, prover, policy, reference_prover)
        for prover in provers
    )
    eligible = sorted(
        (bid for bid in bids if bid.eligible),
        key=lambda row: (row.reservation_price_atoms, row.prover_id),
    )
    winner = eligible[0] if eligible else None
    competitive_payment_atoms = winner.reservation_price_atoms if winner else 0

    ramp_duration_seconds = ceil_bps(
        reference_seconds,
        policy.ramp_duration_factor_bps,
    )
    initial_work_seconds = (
        ceil_bps(reference_seconds, policy.primary_window_factor_bps)
        + policy.publication_buffer_seconds
    )
    collusive_eligible = tuple(
        bid
        for bid in bids
        if bid.bond_atoms
        <= next(
            prover.maximum_lock_bond_atoms
            for prover in provers
            if prover.prover_id == bid.prover_id
        )
        and bid.reservation_price_atoms <= maximum_price_atoms
        and initial_work_seconds - ramp_duration_seconds
        >= bid.required_work_seconds
    )
    collusive_payment_atoms = maximum_price_atoms if collusive_eligible else 0
    collusive_uplift_atoms = max(
        0,
        collusive_payment_atoms - competitive_payment_atoms,
    )
    scenario_weight_bps = workload.weight_bps * shock.weight_bps // BPS
    return AuctionScenarioOutcomeV1(
        scenario_id=f"{workload.workload_id}_{shock.shock_id}",
        scenario_weight_bps=scenario_weight_bps,
        workload_id=workload.workload_id,
        shock_id=shock.shock_id,
        reference_cost_atoms=reference_cost_atoms,
        minimum_price_atoms=minimum_price_atoms,
        maximum_price_atoms=maximum_price_atoms,
        required_bond_atoms=required_bond_atoms,
        offered_bond_atoms=offered_bond_atoms,
        competitive_winner_id=winner.prover_id if winner else None,
        competitive_winner_owner_id=(
            winner.beneficial_owner_id if winner else None
        ),
        competitive_payment_atoms=competitive_payment_atoms,
        collusive_payment_atoms=collusive_payment_atoms,
        collusive_uplift_atoms=collusive_uplift_atoms,
        eligible_owner_count=len({bid.beneficial_owner_id for bid in eligible}),
        bond_excluded_prover_count=sum(
            "BOND_EXCEEDS_PROVER_CAPITAL" in bid.rejection_codes for bid in bids
        ),
        price_excluded_prover_count=sum(
            "RESERVATION_EXCEEDS_PRICE_CEILING" in bid.rejection_codes for bid in bids
        ),
        window_excluded_prover_count=sum(
            "INSUFFICIENT_EFFECTIVE_WORK_WINDOW" in bid.rejection_codes for bid in bids
        ),
        admitted_late_prover_count=sum(
            bid.eligible and bid.effective_work_seconds < bid.required_work_seconds
            for bid in bids
        ),
        fallback_required=winner is None,
        bids=bids,
    )


def evaluate_auction_policy(
    workloads: tuple[WorkloadClassV1, ...],
    shocks: tuple[CostShockV1, ...],
    provers: tuple[ProverProfileV1, ...],
    policy: AuctionPolicyV1,
    reference_prover: ProverProfileV1,
) -> AuctionPolicyEvaluationV1:
    """Evaluate a policy over the exact workload-by-cost scenario product."""

    if sum(row.weight_bps for row in workloads) != BPS:
        raise ValueError("workload weights must sum to 10000 bps")
    if sum(row.weight_bps for row in shocks) != BPS:
        raise ValueError("shock weights must sum to 10000 bps")
    outcomes = tuple(
        simulate_auction_scenario(
            workload,
            shock,
            provers,
            policy,
            reference_prover,
        )
        for workload in workloads
        for shock in shocks
    )
    if sum(row.scenario_weight_bps for row in outcomes) != BPS:
        raise AssertionError("auction scenario weights do not close")
    fulfillment_bps = sum(
        row.scenario_weight_bps for row in outcomes if not row.fallback_required
    )
    fulfilled_weight = max(1, fulfillment_bps)
    payment_weighted = sum(
        row.competitive_payment_atoms * row.scenario_weight_bps
        for row in outcomes
    )
    reference_weighted = sum(
        row.reference_cost_atoms * row.scenario_weight_bps
        for row in outcomes
        if not row.fallback_required
    )
    collusive_uplift_weighted = sum(
        row.collusive_uplift_atoms * row.scenario_weight_bps for row in outcomes
    )
    owner_weights: dict[str, int] = {}
    for row in outcomes:
        if row.competitive_winner_owner_id is not None:
            owner_weights[row.competitive_winner_owner_id] = (
                owner_weights.get(row.competitive_winner_owner_id, 0)
                + row.scenario_weight_bps
            )
    prover_count = len(provers)
    return AuctionPolicyEvaluationV1(
        policy_id=policy.policy_id,
        fulfillment_bps=fulfillment_bps,
        fallback_bps=BPS - fulfillment_bps,
        average_competitive_payment_atoms=payment_weighted // fulfilled_weight,
        average_price_to_reference_bps=(
            payment_weighted * BPS // reference_weighted
            if reference_weighted
            else 0
        ),
        collusive_uplift_bps=(
            collusive_uplift_weighted * BPS // payment_weighted
            if payment_weighted
            else 0
        ),
        average_eligible_owner_fraction_bps=sum(
            row.eligible_owner_count * row.scenario_weight_bps
            for row in outcomes
        )
        * BPS
        // (BPS * prover_count),
        maximum_winner_owner_share_bps=(
            max(owner_weights.values(), default=0) * BPS // fulfilled_weight
        ),
        bond_exclusion_bps=sum(
            row.bond_excluded_prover_count * row.scenario_weight_bps
            for row in outcomes
        )
        // prover_count,
        price_exclusion_bps=sum(
            row.price_excluded_prover_count * row.scenario_weight_bps
            for row in outcomes
        )
        // prover_count,
        window_exclusion_bps=sum(
            row.window_excluded_prover_count * row.scenario_weight_bps
            for row in outcomes
        )
        // prover_count,
        admitted_late_count=sum(row.admitted_late_prover_count for row in outcomes),
        outcomes=outcomes,
    )


@dataclass(frozen=True, slots=True)
class RequestorDemandV1:
    requestor_id: str
    beneficial_owner_id: str
    requested_slots: int


@dataclass(frozen=True, slots=True)
class CapacityDemandScenarioV1:
    scenario_id: str
    weight_bps: int
    priority_requests: tuple[RequestorDemandV1, ...]
    permissionless_demand_slots: int


@dataclass(frozen=True, slots=True)
class CapacityPolicyV1:
    total_slots: int
    permissionless_floor_bps: int
    priority_owner_cap_bps: int


@dataclass(frozen=True, slots=True)
class CapacityScenarioOutcomeV1:
    scenario_id: str
    weight_bps: int
    priority_demand_slots: int
    permissionless_demand_slots: int
    priority_served_slots: int
    permissionless_served_slots: int
    largest_owner_served_slots: int
    total_served_slots: int
    permissionless_floor_slots: int
    priority_reserved_slots: int


@dataclass(frozen=True, slots=True)
class CapacityPolicyEvaluationV1:
    permissionless_service_bps: int
    priority_service_bps: int
    utilization_bps: int
    maximum_priority_owner_share_bps: int
    outcomes: tuple[CapacityScenarioOutcomeV1, ...]


def aggregate_requestor_demands_by_owner(
    requests: Iterable[RequestorDemandV1],
) -> tuple[tuple[str, int], ...]:
    """Aggregate wallet/requestor demand before applying one owner-level cap."""

    by_requestor: set[str] = set()
    by_owner: dict[str, int] = {}
    for request in requests:
        if not request.requestor_id or not request.beneficial_owner_id:
            raise ValueError("requestor and beneficial-owner IDs must be nonempty")
        if request.requestor_id in by_requestor:
            raise ValueError("requestor IDs must be unique")
        by_requestor.add(request.requestor_id)
        exact_nonnegative(request.requested_slots, "requested_slots")
        by_owner[request.beneficial_owner_id] = (
            by_owner.get(request.beneficial_owner_id, 0) + request.requested_slots
        )
        exact_nonnegative(
            by_owner[request.beneficial_owner_id],
            "beneficial_owner_requested_slots",
        )
    return tuple(sorted(by_owner.items()))


def simulate_capacity_scenario(
    scenario: CapacityDemandScenarioV1,
    policy: CapacityPolicyV1,
) -> CapacityScenarioOutcomeV1:
    """Allocate guaranteed permissionless capacity before priority spillover."""

    if not scenario.scenario_id:
        raise ValueError("capacity scenario ID must be nonempty")
    _validate_weight(scenario.weight_bps, "capacity scenario weight")
    exact_nonnegative(scenario.permissionless_demand_slots, "permissionless demand")
    exact_nonnegative(policy.total_slots, "total slots")
    _validate_weight(policy.permissionless_floor_bps, "permissionless floor")
    _validate_weight(policy.priority_owner_cap_bps, "priority owner cap")
    if policy.total_slots == 0:
        raise ValueError("total capacity must be positive")
    if policy.permissionless_floor_bps == 0:
        raise ValueError("permissionless floor must be nonzero")
    if policy.priority_owner_cap_bps == 0:
        raise ValueError("priority owner cap must be nonzero")
    owner_demands = aggregate_requestor_demands_by_owner(
        scenario.priority_requests
    )
    permissionless_floor_slots = max(
        1,
        ceil_bps(policy.total_slots, policy.permissionless_floor_bps),
    )
    priority_reserved_slots = policy.total_slots - permissionless_floor_slots
    owner_cap_slots = max(1, floor_bps(policy.total_slots, policy.priority_owner_cap_bps))
    capped_owner_demands = tuple(
        min(demand_slots, owner_cap_slots) for _, demand_slots in owner_demands
    )
    priority_demand_slots = sum(demand for _, demand in owner_demands)
    priority_served_slots = min(priority_reserved_slots, sum(capped_owner_demands))
    unused_priority_slots = priority_reserved_slots - priority_served_slots
    permissionless_available_slots = permissionless_floor_slots + unused_priority_slots
    permissionless_served_slots = min(
        scenario.permissionless_demand_slots,
        permissionless_available_slots,
    )
    total_served_slots = priority_served_slots + permissionless_served_slots
    return CapacityScenarioOutcomeV1(
        scenario_id=scenario.scenario_id,
        weight_bps=scenario.weight_bps,
        priority_demand_slots=priority_demand_slots,
        permissionless_demand_slots=scenario.permissionless_demand_slots,
        priority_served_slots=priority_served_slots,
        permissionless_served_slots=permissionless_served_slots,
        largest_owner_served_slots=min(
            max(capped_owner_demands, default=0),
            priority_served_slots,
        ),
        total_served_slots=total_served_slots,
        permissionless_floor_slots=permissionless_floor_slots,
        priority_reserved_slots=priority_reserved_slots,
    )


def evaluate_capacity_policy(
    scenarios: tuple[CapacityDemandScenarioV1, ...],
    policy: CapacityPolicyV1,
) -> CapacityPolicyEvaluationV1:
    """Evaluate service, utilization, and owner concentration exactly."""

    if not scenarios or sum(row.weight_bps for row in scenarios) != BPS:
        raise ValueError("capacity scenario weights must sum to 10000 bps")
    outcomes = tuple(simulate_capacity_scenario(row, policy) for row in scenarios)

    def weighted_service(numerator_field: str, denominator_field: str) -> int:
        return sum(
            (
                getattr(outcome, numerator_field) * BPS
                // getattr(outcome, denominator_field)
                if getattr(outcome, denominator_field)
                else BPS
            )
            * outcome.weight_bps
            for outcome in outcomes
        ) // BPS

    maximum_owner_share_bps = max(
        (
            outcome.largest_owner_served_slots * BPS
            // outcome.priority_served_slots
            if outcome.priority_served_slots
            else 0
        )
        for outcome in outcomes
    )
    return CapacityPolicyEvaluationV1(
        permissionless_service_bps=weighted_service(
            "permissionless_served_slots",
            "permissionless_demand_slots",
        ),
        priority_service_bps=weighted_service(
            "priority_served_slots",
            "priority_demand_slots",
        ),
        utilization_bps=sum(
            outcome.total_served_slots * BPS // policy.total_slots
            * outcome.weight_bps
            for outcome in outcomes
        )
        // BPS,
        maximum_priority_owner_share_bps=maximum_owner_share_bps,
        outcomes=outcomes,
    )
