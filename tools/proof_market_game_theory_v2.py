"""Exact bounded games for the research-only ZenoProof procurement design V2.

The module is a deterministic suggestion/evidence core.  It performs no I/O and
grants no scheduling, proof-admission, payment, slashing, settlement, token, or
release authority.  All amounts are exact integer atoms.  Live cost, ownership,
failure-domain, latency, and demand distributions remain external evidence.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product

from tools.proof_market_game_theory_economics_v2 import (  # noqa: F401
    BPS,
    MAX_ATOMS,
    AwardKindV2,
    CartelResultV2,
    DefaultBondDispositionV2,
    DefaultBondRequestV2,
    DefaultLossV2,
    DutchDelayContextV2,
    EconomicWorkDescriptorV2,
    FallbackAwardV2,
    ProofReserveClaimAcceptedV2,
    ProofReserveClaimRejectedV2,
    ProofReserveClaimRejectV2,
    ProofReserveClaimRequestV2,
    ProofReserveClaimStateV2,
    ProofReserveEligibilityV2,
    ProofReserveRequestV2,
    StageWithholdingSearchV2,
    StationaryEqualShareCartelScenarioV2,
    canonical_economic_work_key,
    canonical_economic_work_key_bytes,
    ceil_bps,
    ceil_div,
    claim_proof_reserve_bonus,
    dispose_prover_fault_bond,
    enumerate_single_provider_stage_withholding,
    exact_natural,
    exact_positive,
    maximum_safe_dutch_delay_price,
    next_posted_price_after_round,
    proof_reserve_bonus,
    required_default_bond,
    required_deterrence_bond,
    scarcity_or_direct_award,
    stationary_equal_share_cartel,
    stationary_equal_share_cartel_threshold,
    verifier_fault_bond_return,
    weighted_floor_average,
)


@dataclass(frozen=True, slots=True)
class ProcurementOutcomeV2:
    winner_index: int | None
    payment_atoms: int


def _validate_bids(bids: tuple[int, ...], reserve_atoms: int) -> None:
    if not bids:
        raise ValueError("at least one bid is required")
    exact_natural(reserve_atoms, "reserve_atoms")
    for index, bid in enumerate(bids):
        exact_natural(bid, f"bids[{index}]")


def first_price_procurement(
    bids: tuple[int, ...],
    reserve_atoms: int,
) -> ProcurementOutcomeV2:
    """Return lowest accepted bid with a fixed index tie-break and own-bid pay."""

    _validate_bids(bids, reserve_atoms)
    eligible = tuple(
        (bid, index) for index, bid in enumerate(bids) if bid <= reserve_atoms
    )
    if not eligible:
        return ProcurementOutcomeV2(None, 0)
    winning_bid, winner_index = min(eligible)
    return ProcurementOutcomeV2(winner_index, winning_bid)


def critical_price_procurement(
    bids: tuple[int, ...],
    reserve_atoms: int,
) -> ProcurementOutcomeV2:
    """Return reverse-Vickrey allocation under a buyer-committed reserve.

    The lowest bid at or below the reserve wins.  Its payment is the smaller of
    the reserve and the lowest competing bid.  The fixed index tie-break and the
    bidder set are premises.  The rule is not coalition-proof.  No false-name
    incentive claim is made by this single-job model.
    """

    _validate_bids(bids, reserve_atoms)
    eligible = tuple(
        (bid, index) for index, bid in enumerate(bids) if bid <= reserve_atoms
    )
    if not eligible:
        return ProcurementOutcomeV2(None, 0)
    _, winner_index = min(eligible)
    competing_bids = tuple(
        bid for index, bid in enumerate(bids) if index != winner_index
    )
    threshold = min(competing_bids) if competing_bids else reserve_atoms
    return ProcurementOutcomeV2(winner_index, min(reserve_atoms, threshold))


def bidder_utility(
    *,
    bidder_index: int,
    cost_atoms: int,
    outcome: ProcurementOutcomeV2,
) -> int:
    exact_natural(cost_atoms, "cost_atoms")
    if type(bidder_index) is not int or bidder_index < 0:
        raise ValueError("bidder_index must be a nonnegative exact integer")
    if outcome.winner_index != bidder_index:
        return 0
    return outcome.payment_atoms - cost_atoms


@dataclass(frozen=True, slots=True)
class DominanceSearchResultV2:
    bidder_count: int
    reserve_atoms: int
    report_domain_max_atoms: int
    deviation_queries: int
    truthful_ir_queries: int
    profitable_deviation: tuple[int, tuple[int, ...], int, int, int] | None
    truthful_ir_violation: tuple[int, tuple[int, ...], int] | None

    @property
    def truthful_weakly_dominant(self) -> bool:
        return self.profitable_deviation is None

    @property
    def truthful_ex_post_ir(self) -> bool:
        return self.truthful_ir_violation is None


def _reported_profile(
    *,
    bidder_index: int,
    bidder_count: int,
    own_report: int,
    other_reports: tuple[int, ...],
) -> tuple[int, ...]:
    bids = [0] * bidder_count
    bids[bidder_index] = own_report
    other_indices = (
        index for index in range(bidder_count) if index != bidder_index
    )
    for index, report in zip(other_indices, other_reports, strict=True):
        bids[index] = report
    return tuple(bids)


@dataclass(frozen=True, slots=True)
class _DominanceCase:
    bidder_index: int
    cost_atoms: int
    truthful_bids: tuple[int, ...]
    truthful_utility: int


def _first_profitable_deviation(
    case: _DominanceCase,
    reports: range,
    reserve_atoms: int,
) -> tuple[int, int] | None:
    first: tuple[int, int] | None = None
    for deviation in reports:
        deviating_bids = list(case.truthful_bids)
        deviating_bids[case.bidder_index] = deviation
        deviation_outcome = critical_price_procurement(
            tuple(deviating_bids),
            reserve_atoms,
        )
        deviation_utility = bidder_utility(
            bidder_index=case.bidder_index,
            cost_atoms=case.cost_atoms,
            outcome=deviation_outcome,
        )
        if deviation_utility > case.truthful_utility and first is None:
            first = (deviation, deviation_utility)
    return first


def enumerate_critical_price_dominance(
    *,
    bidder_count: int,
    reserve_atoms: int,
) -> DominanceSearchResultV2:
    """Exhaustively test bounded unilateral truthfulness for fixed identities."""

    if type(bidder_count) is not int or bidder_count < 2:
        raise ValueError("bidder_count must be an exact integer at least two")
    exact_natural(reserve_atoms, "reserve_atoms")
    report_max = reserve_atoms + 1
    if report_max > MAX_ATOMS:
        raise ValueError("reserve_atoms leaves no rejecting report value")
    reports = range(report_max + 1)
    deviation_queries = 0
    truthful_ir_queries = 0
    profitable: tuple[int, tuple[int, ...], int, int, int] | None = None
    ir_violation: tuple[int, tuple[int, ...], int] | None = None

    other_profiles = tuple(product(reports, repeat=bidder_count - 1))
    cases = product(range(bidder_count), reports, other_profiles)
    for bidder_index, cost_atoms, other_reports in cases:
        truthful_bids = _reported_profile(
            bidder_index=bidder_index,
            bidder_count=bidder_count,
            own_report=cost_atoms,
            other_reports=other_reports,
        )
        truthful_outcome = critical_price_procurement(truthful_bids, reserve_atoms)
        truthful_utility = bidder_utility(
            bidder_index=bidder_index,
            cost_atoms=cost_atoms,
            outcome=truthful_outcome,
        )
        truthful_ir_queries += 1
        if truthful_utility < 0 and ir_violation is None:
            ir_violation = (bidder_index, truthful_bids, cost_atoms)
        deviation_queries += len(reports)
        case = _DominanceCase(bidder_index, cost_atoms, truthful_bids, truthful_utility)
        deviation = _first_profitable_deviation(case, reports, reserve_atoms)
        if deviation is not None and profitable is None:
            deviation_report, deviation_utility = deviation
            profitable = (
                bidder_index,
                truthful_bids,
                deviation_report,
                truthful_utility,
                deviation_utility,
            )

    return DominanceSearchResultV2(
        bidder_count,
        reserve_atoms,
        report_max,
        deviation_queries,
        truthful_ir_queries,
        profitable,
        ir_violation,
    )


def first_price_truthfulness_counterexample() -> dict[str, int]:
    truthful = first_price_procurement((1, 3, 4), 4)
    deviating = first_price_procurement((2, 3, 4), 4)
    truthful_utility = bidder_utility(
        bidder_index=0,
        cost_atoms=1,
        outcome=truthful,
    )
    deviation_utility = bidder_utility(
        bidder_index=0,
        cost_atoms=1,
        outcome=deviating,
    )
    return {
        "cost_atoms": 1,
        "next_bid_atoms": 3,
        "truthful_bid_atoms": 1,
        "deviation_bid_atoms": 2,
        "truthful_utility_atoms": truthful_utility,
        "deviation_utility_atoms": deviation_utility,
        "profitable_gain_atoms": deviation_utility - truthful_utility,
    }


def critical_price_coalition_counterexample() -> dict[str, int]:
    truthful = critical_price_procurement((1, 2, 4), 4)
    deviating = critical_price_procurement((1, 4, 4), 4)
    truthful_utility = sum(
        bidder_utility(bidder_index=index, cost_atoms=cost, outcome=truthful)
        for index, cost in ((0, 1), (1, 2))
    )
    deviation_utility = sum(
        bidder_utility(bidder_index=index, cost_atoms=cost, outcome=deviating)
        for index, cost in ((0, 1), (1, 2))
    )
    return {
        "truthful_payment_atoms": truthful.payment_atoms,
        "deviation_payment_atoms": deviating.payment_atoms,
        "truthful_coalition_utility_atoms": truthful_utility,
        "deviation_coalition_utility_atoms": deviation_utility,
        "profitable_gain_atoms": deviation_utility - truthful_utility,
    }


def address_count_diversity_counterexample() -> dict[str, int | bool]:
    """Show that an address-count gate does not establish owner diversity.

    This is an identity-gate counterexample.  It does not show a profitable
    false-name bid deviation for reverse critical-price procurement.
    """

    reserve_atoms = 5
    one_address_bids = (1,)
    alias_bids = (1, 5, 5)
    one_address = critical_price_procurement(one_address_bids, reserve_atoms)
    aliases = critical_price_procurement(alias_bids, reserve_atoms)
    cost_atoms = 1
    one_address_utility = bidder_utility(
        bidder_index=0,
        cost_atoms=cost_atoms,
        outcome=one_address,
    )
    alias_utility = bidder_utility(
        bidder_index=0,
        cost_atoms=cost_atoms,
        outcome=aliases,
    )
    address_gate_passes = len(alias_bids) >= 3
    distinct_owner_gate_passes = len({"ONE_OWNER" for _ in alias_bids}) >= 3
    return {
        "address_count": len(alias_bids),
        "true_owner_count": 1,
        "address_gate_passes": address_gate_passes,
        "distinct_owner_gate_passes": distinct_owner_gate_passes,
        "one_address_payment_atoms": one_address.payment_atoms,
        "alias_payment_atoms": aliases.payment_atoms,
        "one_address_utility_atoms": one_address_utility,
        "alias_utility_atoms": alias_utility,
        "false_name_utility_gain_atoms": alias_utility - one_address_utility,
    }


@dataclass(frozen=True, slots=True)
class PostedPriceRequestV2:
    benchmark_atoms: int
    risk_margin_bps: int
    prefund_cap_atoms: int
    buyer_value_cap_atoms: int
    direct_execution_cap_atoms: int


def benchmark_indexed_posted_price(request: PostedPriceRequestV2) -> int:
    """Return a capped price that has no current-round acceptance input."""

    exact_natural(request.benchmark_atoms, "benchmark_atoms")
    exact_natural(request.risk_margin_bps, "risk_margin_bps")
    caps = (
        exact_natural(request.prefund_cap_atoms, "prefund_cap_atoms"),
        exact_natural(request.buyer_value_cap_atoms, "buyer_value_cap_atoms"),
        exact_natural(
            request.direct_execution_cap_atoms,
            "direct_execution_cap_atoms",
        ),
    )
    benchmark_with_margin = exact_natural(
        request.benchmark_atoms
        + ceil_bps(request.benchmark_atoms, request.risk_margin_bps),
        "benchmark_with_margin_atoms",
    )
    return min(benchmark_with_margin, *caps)


@dataclass(frozen=True, slots=True)
class ProviderV2:
    provider_id: str
    owner_id: str
    failure_domain_id: str
    effective_cost_atoms: int
    measured_capacity_units: int
    qualified: bool = True


def _validate_providers(providers: tuple[ProviderV2, ...]) -> None:
    if not providers:
        raise ValueError("at least one provider is required")
    if len({provider.provider_id for provider in providers}) != len(providers):
        raise ValueError("provider IDs must be unique")
    for provider in providers:
        if not provider.provider_id or not provider.owner_id:
            raise ValueError("provider and owner IDs must be nonempty")
        if not provider.failure_domain_id:
            raise ValueError("failure_domain_id must be nonempty")
        exact_natural(provider.effective_cost_atoms, "effective_cost_atoms")
        exact_positive(provider.measured_capacity_units, "measured_capacity_units")
        if type(provider.qualified) is not bool:
            raise ValueError("qualified must be bool")


def posted_price_acceptors(
    providers: tuple[ProviderV2, ...],
    payment_atoms: int,
) -> tuple[ProviderV2, ...]:
    _validate_providers(providers)
    exact_natural(payment_atoms, "payment_atoms")
    return tuple(
        sorted(
            (
                provider
                for provider in providers
                if provider.qualified
                and provider.effective_cost_atoms <= payment_atoms
            ),
            key=lambda provider: provider.provider_id,
        )
    )


def owner_capacity_ticket_counts(
    providers: tuple[ProviderV2, ...],
    payment_atoms: int,
) -> tuple[tuple[str, int], ...]:
    totals: dict[str, int] = {}
    for provider in posted_price_acceptors(providers, payment_atoms):
        totals[provider.owner_id] = exact_natural(
            totals.get(provider.owner_id, 0) + provider.measured_capacity_units,
            f"owner_capacity[{provider.owner_id}]",
        )
    return tuple(sorted(totals.items()))


def rejection_sample_capacity_ticket(
    seed_word: int,
    total_capacity_units: int,
) -> int | None:
    """Map one uniform 256-bit word without modulo bias.

    A rejected word requires a fresh domain-separated beacon/XOF word.  This
    function does not construct or authenticate that randomness transcript.
    """

    exact_natural(seed_word, "seed_word")
    exact_positive(total_capacity_units, "total_capacity_units")
    word_space = MAX_ATOMS + 1
    acceptance_limit = word_space - word_space % total_capacity_units
    if seed_word >= acceptance_limit:
        return None
    return seed_word % total_capacity_units


def select_capacity_ticket(
    providers: tuple[ProviderV2, ...],
    payment_atoms: int,
    uniform_ticket: int,
) -> ProviderV2 | None:
    """Select using an already unbiased ticket in the aggregate capacity range."""

    acceptors = posted_price_acceptors(providers, payment_atoms)
    exact_natural(uniform_ticket, "uniform_ticket")
    if not acceptors:
        return None
    total = exact_natural(
        sum(provider.measured_capacity_units for provider in acceptors),
        "total_measured_capacity_units",
    )
    if uniform_ticket >= total:
        raise ValueError("uniform_ticket must be less than total measured capacity")
    cursor = 0
    for provider in acceptors:
        cursor += provider.measured_capacity_units
        if uniform_ticket < cursor:
            return provider
    raise AssertionError("capacity-ticket selection did not terminate")
