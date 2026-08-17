"""Exact research model for the general ZenoProof marketplace.

The module is an advisory functional core. It models escrow settlement,
proof/counterexample procurement, contribution-locked bootstrap rewards, and
business-model cash flow with exact integers. It grants no proof admission,
payment, token, burn, finality, publication, or release authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from typing import Final, Iterable

BPS: Final = 10_000
MAX_ATOMS: Final = 2**256 - 1
QUOTE_SCALE: Final = 100
ZDEX_SCALE: Final = 10**18
PROOF_RESERVE_ATOMS: Final = 30_000_000 * ZDEX_SCALE


def exact_nonnegative(value: int, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_ATOMS:
        raise ValueError(f"{name} must be an exact integer in [0, 2^256-1]")
    return value


def ceil_div(numerator: int, denominator: int) -> int:
    exact_nonnegative(numerator, "numerator")
    if type(denominator) is not int or denominator <= 0:
        raise ValueError("denominator must be a positive exact integer")
    return (numerator + denominator - 1) // denominator


def floor_bps(amount_atoms: int, rate_bps: int) -> int:
    exact_nonnegative(amount_atoms, "amount_atoms")
    if type(rate_bps) is not int or not 0 <= rate_bps <= BPS:
        raise ValueError("rate_bps must be an exact integer in [0, 10000]")
    return amount_atoms * rate_bps // BPS


def ceil_bps(amount_atoms: int, rate_bps: int) -> int:
    exact_nonnegative(amount_atoms, "amount_atoms")
    if type(rate_bps) is not int or rate_bps < 0:
        raise ValueError("rate_bps must be a nonnegative exact integer")
    return ceil_div(amount_atoms * rate_bps, BPS)


class ProofProductKindV1(StrEnum):
    ASSIGNED_VALIDITY_PROOF = "ASSIGNED_VALIDITY_PROOF"
    OPEN_COUNTEREXAMPLE = "OPEN_COUNTEREXAMPLE"
    IMPROVEMENT_CERTIFICATE = "IMPROVEMENT_CERTIFICATE"
    PUBLIC_GOOD_PROOF = "PUBLIC_GOOD_PROOF"
    MAINTENANCE_REVERIFY = "MAINTENANCE_REVERIFY"
    CATALOG_REUSE = "CATALOG_REUSE"
    ZRPF_BATCH = "ZRPF_BATCH"


class FundingScopeV1(StrEnum):
    EXTERNAL_BUYER = "EXTERNAL_BUYER"
    ZRPF_ANCHOR = "ZRPF_ANCHOR"
    TREASURY_PUBLIC_GOOD = "TREASURY_PUBLIC_GOOD"
    ENTERPRISE_SUBSCRIPTION = "ENTERPRISE_SUBSCRIPTION"


class AccessPolicyV1(StrEnum):
    PUBLIC_CONTENT_ADDRESSED = "PUBLIC_CONTENT_ADDRESSED"
    PRIVATE_DELIVERY = "PRIVATE_DELIVERY"
    EMBARGO_THEN_PUBLIC = "EMBARGO_THEN_PUBLIC"


@dataclass(frozen=True, slots=True)
class AuctionLockScheduleV1:
    auction_start_height: int
    lock_height: int
    primary_deadline_height: int
    final_deadline_height: int
    estimated_proving_blocks: int
    safety_margin_blocks: int


@dataclass(frozen=True, slots=True)
class AuctionLockAssessmentV1:
    effective_work_blocks: int
    required_work_blocks: int
    fallback_reprocurement_blocks: int
    admissible: bool
    rejection_codes: tuple[str, ...]


def assess_auction_lock(schedule: AuctionLockScheduleV1) -> AuctionLockAssessmentV1:
    """Check the locker's actual service window using canonical ledger heights."""

    for field_name in (
        "auction_start_height",
        "lock_height",
        "primary_deadline_height",
        "final_deadline_height",
        "estimated_proving_blocks",
        "safety_margin_blocks",
    ):
        exact_nonnegative(getattr(schedule, field_name), field_name)
    required_work_blocks = (
        schedule.estimated_proving_blocks + schedule.safety_margin_blocks
    )
    exact_nonnegative(required_work_blocks, "required_work_blocks")
    effective_work_blocks = max(
        0,
        schedule.primary_deadline_height - schedule.lock_height,
    )
    fallback_reprocurement_blocks = max(
        0,
        schedule.final_deadline_height - schedule.primary_deadline_height,
    )
    rejection_codes: list[str] = []
    if schedule.lock_height < schedule.auction_start_height:
        rejection_codes.append("LOCK_PRECEDES_AUCTION")
    if schedule.lock_height >= schedule.primary_deadline_height:
        rejection_codes.append("LOCK_NOT_BEFORE_PRIMARY_DEADLINE")
    if schedule.primary_deadline_height > schedule.final_deadline_height:
        rejection_codes.append("FINAL_DEADLINE_PRECEDES_PRIMARY")
    if effective_work_blocks < required_work_blocks:
        rejection_codes.append("INSUFFICIENT_EFFECTIVE_WORK_WINDOW")
    return AuctionLockAssessmentV1(
        effective_work_blocks=effective_work_blocks,
        required_work_blocks=required_work_blocks,
        fallback_reprocurement_blocks=fallback_reprocurement_blocks,
        admissible=not rejection_codes,
        rejection_codes=tuple(rejection_codes),
    )


@dataclass(frozen=True, slots=True)
class DefaultBondClaimsV1:
    buyer_restitution_claim_atoms: int
    reprocurement_claim_atoms: int
    insurance_recovery_claim_atoms: int
    residual_burn_cap_atoms: int


@dataclass(frozen=True, slots=True)
class DefaultBondAllocationV1:
    buyer_restitution_atoms: int
    reprocurement_atoms: int
    insurance_recovery_atoms: int
    residual_burn_atoms: int
    seller_return_atoms: int
    unfunded_claim_atoms: int


def allocate_default_bond(
    seller_bond_atoms: int,
    claims: DefaultBondClaimsV1,
) -> DefaultBondAllocationV1:
    """Allocate a defaulted bond by loss priority, with burn last."""

    exact_nonnegative(seller_bond_atoms, "seller_bond_atoms")
    claim_names = (
        "buyer_restitution_claim_atoms",
        "reprocurement_claim_atoms",
        "insurance_recovery_claim_atoms",
        "residual_burn_cap_atoms",
    )
    for field_name in claim_names:
        exact_nonnegative(getattr(claims, field_name), field_name)
    total_loss_claim_atoms = (
        claims.buyer_restitution_claim_atoms
        + claims.reprocurement_claim_atoms
        + claims.insurance_recovery_claim_atoms
    )
    exact_nonnegative(total_loss_claim_atoms, "total_loss_claim_atoms")

    remaining_atoms = seller_bond_atoms
    buyer_restitution_atoms = min(
        remaining_atoms,
        claims.buyer_restitution_claim_atoms,
    )
    remaining_atoms -= buyer_restitution_atoms
    reprocurement_atoms = min(remaining_atoms, claims.reprocurement_claim_atoms)
    remaining_atoms -= reprocurement_atoms
    insurance_recovery_atoms = min(
        remaining_atoms,
        claims.insurance_recovery_claim_atoms,
    )
    remaining_atoms -= insurance_recovery_atoms
    funded_loss_claim_atoms = (
        buyer_restitution_atoms + reprocurement_atoms + insurance_recovery_atoms
    )
    unfunded_claim_atoms = total_loss_claim_atoms - funded_loss_claim_atoms
    residual_burn_atoms = 0
    if unfunded_claim_atoms == 0:
        residual_burn_atoms = min(remaining_atoms, claims.residual_burn_cap_atoms)
        remaining_atoms -= residual_burn_atoms
    return DefaultBondAllocationV1(
        buyer_restitution_atoms=buyer_restitution_atoms,
        reprocurement_atoms=reprocurement_atoms,
        insurance_recovery_atoms=insurance_recovery_atoms,
        residual_burn_atoms=residual_burn_atoms,
        seller_return_atoms=remaining_atoms,
        unfunded_claim_atoms=unfunded_claim_atoms,
    )


@dataclass(frozen=True, slots=True)
class CapacityPartitionPolicyV1:
    total_slots: int
    priority_reserved_slots: int
    permissionless_floor_slots: int
    max_priority_slots_per_requestor: int


@dataclass(frozen=True, slots=True)
class CapacityPartitionAssessmentV1:
    admissible: bool
    unallocated_slots: int
    rejection_codes: tuple[str, ...]


def assess_capacity_partition(
    policy: CapacityPartitionPolicyV1,
) -> CapacityPartitionAssessmentV1:
    """Protect a nonzero permissionless floor from paid-priority exhaustion."""

    for field_name in (
        "total_slots",
        "priority_reserved_slots",
        "permissionless_floor_slots",
        "max_priority_slots_per_requestor",
    ):
        exact_nonnegative(getattr(policy, field_name), field_name)
    rejection_codes: list[str] = []
    if policy.total_slots == 0:
        rejection_codes.append("ZERO_TOTAL_CAPACITY")
    if policy.permissionless_floor_slots == 0:
        rejection_codes.append("ZERO_PERMISSIONLESS_FLOOR")
    committed_slots = (
        policy.priority_reserved_slots + policy.permissionless_floor_slots
    )
    if committed_slots > policy.total_slots:
        rejection_codes.append("CAPACITY_PARTITIONS_EXCEED_TOTAL")
    if policy.max_priority_slots_per_requestor > policy.priority_reserved_slots:
        rejection_codes.append("REQUESTOR_PRIORITY_CAP_EXCEEDS_RESERVED_CAPACITY")
    return CapacityPartitionAssessmentV1(
        admissible=not rejection_codes,
        unallocated_slots=max(0, policy.total_slots - committed_slots),
        rejection_codes=tuple(rejection_codes),
    )


@dataclass(frozen=True, slots=True)
class ProofAdmissionChecksV1:
    verifier_accepts: bool
    claim_binding_matches: bool
    assumptions_binding_matches: bool
    input_root_matches: bool
    output_root_matches: bool
    verifier_profile_current: bool
    canonical_work_key_unclaimed: bool
    non_vacuity_witness_ok: bool
    request_id_binding_matches: bool
    ordered_batch_binding_matches: bool
    role_signature_domains_separated: bool
    buyer_payment_escrow_committed: bool
    durable_work_receipt_committed: bool
    callback_effect_key_unclaimed: bool

    @property
    def accepted(self) -> bool:
        return all(
            (
                self.verifier_accepts,
                self.claim_binding_matches,
                self.assumptions_binding_matches,
                self.input_root_matches,
                self.output_root_matches,
                self.verifier_profile_current,
                self.canonical_work_key_unclaimed,
                self.non_vacuity_witness_ok,
                self.request_id_binding_matches,
                self.ordered_batch_binding_matches,
                self.role_signature_domains_separated,
                self.buyer_payment_escrow_committed,
                self.durable_work_receipt_committed,
                self.callback_effect_key_unclaimed,
            )
        )


@dataclass(frozen=True, slots=True)
class ProofJobTermsV1:
    product_kind: ProofProductKindV1
    funding_scope: FundingScopeV1
    access_policy: AccessPolicyV1
    maximum_seller_payment_atoms: int
    protocol_success_fee_bps: int
    listing_fee_atoms: int
    verifier_budget_atoms: int
    publication_budget_atoms: int
    seller_bond_atoms: int


@dataclass(frozen=True, slots=True)
class ProofJobSettlementV1:
    accepted: bool
    required_buyer_prefund_atoms: int
    seller_payment_atoms: int
    verifier_payment_atoms: int
    publication_payment_atoms: int
    protocol_revenue_atoms: int
    buyer_refund_atoms: int
    seller_bond_return_atoms: int
    seller_bond_restitution_atoms: int
    seller_bond_reprocurement_atoms: int


def required_buyer_prefund(terms: ProofJobTermsV1) -> int:
    """Maximum buyer liability, excluding the separately posted seller bond."""

    _validate_job_terms(terms)
    maximum_protocol_fee = ceil_bps(
        terms.maximum_seller_payment_atoms,
        terms.protocol_success_fee_bps,
    )
    return (
        terms.maximum_seller_payment_atoms
        + maximum_protocol_fee
        + terms.listing_fee_atoms
        + terms.verifier_budget_atoms
        + terms.publication_budget_atoms
    )


def _validate_job_terms(terms: ProofJobTermsV1) -> None:
    for field_name in (
        "maximum_seller_payment_atoms",
        "listing_fee_atoms",
        "verifier_budget_atoms",
        "publication_budget_atoms",
        "seller_bond_atoms",
    ):
        exact_nonnegative(getattr(terms, field_name), field_name)
    if not 0 <= terms.protocol_success_fee_bps <= BPS:
        raise ValueError("protocol_success_fee_bps must be in [0, 10000]")
    if (
        terms.funding_scope is FundingScopeV1.ZRPF_ANCHOR
        and terms.protocol_success_fee_bps != 0
    ):
        raise ValueError("the internal ZRPF anchor lane cannot charge itself a market take")


def settle_proof_job(
    terms: ProofJobTermsV1,
    checks: ProofAdmissionChecksV1,
    *,
    requested_seller_payment_atoms: int,
    verifier_cost_atoms: int,
    publication_cost_atoms: int,
    seller_default_damage_atoms: int = 0,
    seller_reprocurement_claim_atoms: int = 0,
) -> ProofJobSettlementV1:
    """Settle a prefunded job with objective admission and exact refunds.

    The buyer commits to the verifier policy at listing time. No discretionary
    post-completion buyer veto appears in the settlement rule.
    """

    _validate_job_terms(terms)
    for name, value in (
        ("requested_seller_payment_atoms", requested_seller_payment_atoms),
        ("verifier_cost_atoms", verifier_cost_atoms),
        ("publication_cost_atoms", publication_cost_atoms),
        ("seller_default_damage_atoms", seller_default_damage_atoms),
        ("seller_reprocurement_claim_atoms", seller_reprocurement_claim_atoms),
    ):
        exact_nonnegative(value, name)
    if requested_seller_payment_atoms > terms.maximum_seller_payment_atoms:
        raise ValueError("requested seller payment exceeds the prefunded maximum")
    if verifier_cost_atoms > terms.verifier_budget_atoms:
        raise ValueError("verifier cost exceeds the prefunded verifier budget")
    if publication_cost_atoms > terms.publication_budget_atoms:
        raise ValueError("publication cost exceeds the prefunded publication budget")

    prefund_atoms = required_buyer_prefund(terms)
    if checks.accepted:
        seller_payment_atoms = requested_seller_payment_atoms
        publication_payment_atoms = publication_cost_atoms
        protocol_success_fee_atoms = ceil_bps(
            seller_payment_atoms,
            terms.protocol_success_fee_bps,
        )
        seller_bond_return_atoms = terms.seller_bond_atoms
        seller_bond_restitution_atoms = 0
        seller_bond_reprocurement_atoms = 0
    else:
        seller_payment_atoms = 0
        publication_payment_atoms = 0
        protocol_success_fee_atoms = 0
        bond_allocation = allocate_default_bond(
            terms.seller_bond_atoms,
            DefaultBondClaimsV1(
                buyer_restitution_claim_atoms=seller_default_damage_atoms,
                reprocurement_claim_atoms=seller_reprocurement_claim_atoms,
                insurance_recovery_claim_atoms=0,
                residual_burn_cap_atoms=0,
            ),
        )
        seller_bond_restitution_atoms = bond_allocation.buyer_restitution_atoms
        seller_bond_reprocurement_atoms = bond_allocation.reprocurement_atoms
        seller_bond_return_atoms = bond_allocation.seller_return_atoms

    protocol_revenue_atoms = terms.listing_fee_atoms + protocol_success_fee_atoms
    spent_prefund_atoms = (
        seller_payment_atoms
        + verifier_cost_atoms
        + publication_payment_atoms
        + protocol_revenue_atoms
    )
    if spent_prefund_atoms > prefund_atoms:
        raise ValueError("settlement spends more than the buyer prefund")
    return ProofJobSettlementV1(
        accepted=checks.accepted,
        required_buyer_prefund_atoms=prefund_atoms,
        seller_payment_atoms=seller_payment_atoms,
        verifier_payment_atoms=verifier_cost_atoms,
        publication_payment_atoms=publication_payment_atoms,
        protocol_revenue_atoms=protocol_revenue_atoms,
        buyer_refund_atoms=prefund_atoms - spent_prefund_atoms,
        seller_bond_return_atoms=seller_bond_return_atoms,
        seller_bond_restitution_atoms=seller_bond_restitution_atoms,
        seller_bond_reprocurement_atoms=seller_bond_reprocurement_atoms,
    )


@dataclass(frozen=True, slots=True)
class ContributionBonusRequestV1:
    verified_useful_value_atoms: int
    irreversible_external_fee_atoms: int
    verified_protocol_savings_atoms: int
    scheduled_reserve_cap_atoms: int
    useful_value_bonus_bps: int
    external_fee_capture_cap_bps: int
    savings_capture_cap_bps: int


@dataclass(frozen=True, slots=True)
class ContributionBonusOutcomeV1:
    value_cap_atoms: int
    anti_self_dealing_cap_atoms: int
    bonus_atoms: int


def contribution_locked_bonus(
    request: ContributionBonusRequestV1,
) -> ContributionBonusOutcomeV1:
    """Cap a bootstrap bonus by verified contribution and irreversible value.

    External jobs use irreversible third-party fees as the self-dealing bound.
    Protocol jobs may additionally cite independently verified savings. The
    returned amount remains a requested bonus; a mounted reserve transition and
    release-selected verifier would still be required to pay it.
    """

    for field_name in (
        "verified_useful_value_atoms",
        "irreversible_external_fee_atoms",
        "verified_protocol_savings_atoms",
        "scheduled_reserve_cap_atoms",
    ):
        exact_nonnegative(getattr(request, field_name), field_name)
    for field_name in (
        "useful_value_bonus_bps",
        "external_fee_capture_cap_bps",
        "savings_capture_cap_bps",
    ):
        rate = getattr(request, field_name)
        if type(rate) is not int or not 0 <= rate <= BPS:
            raise ValueError(f"{field_name} must be in [0, 10000]")
    value_cap_atoms = floor_bps(
        request.verified_useful_value_atoms,
        request.useful_value_bonus_bps,
    )
    anti_self_dealing_cap_atoms = (
        floor_bps(
            request.irreversible_external_fee_atoms,
            request.external_fee_capture_cap_bps,
        )
        + floor_bps(
            request.verified_protocol_savings_atoms,
            request.savings_capture_cap_bps,
        )
    )
    bonus_atoms = min(
        request.scheduled_reserve_cap_atoms,
        value_cap_atoms,
        anti_self_dealing_cap_atoms,
    )
    return ContributionBonusOutcomeV1(
        value_cap_atoms=value_cap_atoms,
        anti_self_dealing_cap_atoms=anti_self_dealing_cap_atoms,
        bonus_atoms=bonus_atoms,
    )


def self_dealing_profit_atoms(
    *,
    bonus_atoms: int,
    fee_credit_atoms: int,
    irreversible_fee_atoms: int,
    verification_cost_atoms: int,
    computation_cost_atoms: int,
    expected_penalty_atoms: int,
) -> int:
    """Coalition profit when the same owner controls buyer and seller."""

    for name, value in (
        ("bonus_atoms", bonus_atoms),
        ("fee_credit_atoms", fee_credit_atoms),
        ("irreversible_fee_atoms", irreversible_fee_atoms),
        ("verification_cost_atoms", verification_cost_atoms),
        ("computation_cost_atoms", computation_cost_atoms),
        ("expected_penalty_atoms", expected_penalty_atoms),
    ):
        exact_nonnegative(value, name)
    gain_atoms = bonus_atoms + fee_credit_atoms
    cost_atoms = (
        irreversible_fee_atoms
        + verification_cost_atoms
        + computation_cost_atoms
        + expected_penalty_atoms
    )
    return gain_atoms - cost_atoms


def minimum_sybil_bond_atoms(total_reward_atoms: int, cohort_size: int) -> int:
    """Minimum per-identity bond for the equal-split two-identity attack."""

    exact_nonnegative(total_reward_atoms, "total_reward_atoms")
    if type(cohort_size) is not int or cohort_size < 1:
        raise ValueError("cohort_size must be a positive exact integer")
    numerator = total_reward_atoms * (cohort_size - 1)
    denominator = cohort_size * (cohort_size + 1)
    return ceil_div(numerator, denominator)


@dataclass(frozen=True, slots=True)
class DisputeBondIntervalV1:
    feasible: bool
    minimum_bond_atoms: int
    maximum_bond_atoms: int | None


def dispute_bond_interval(
    *,
    honest_reward_atoms: int,
    honest_external_gain_atoms: int,
    frivolous_external_gain_atoms: int,
) -> DisputeBondIntervalV1:
    """Return integer D satisfying frivolous_gain < D < honest total gain."""

    for name, value in (
        ("honest_reward_atoms", honest_reward_atoms),
        ("honest_external_gain_atoms", honest_external_gain_atoms),
        ("frivolous_external_gain_atoms", frivolous_external_gain_atoms),
    ):
        exact_nonnegative(value, name)
    honest_total_gain_atoms = honest_reward_atoms + honest_external_gain_atoms
    minimum_bond_atoms = frivolous_external_gain_atoms + 1
    maximum_bond_atoms = honest_total_gain_atoms - 1 if honest_total_gain_atoms else None
    feasible = maximum_bond_atoms is not None and minimum_bond_atoms <= maximum_bond_atoms
    return DisputeBondIntervalV1(
        feasible=feasible,
        minimum_bond_atoms=minimum_bond_atoms,
        maximum_bond_atoms=maximum_bond_atoms,
    )


def probabilistic_dispute_feasible(
    *,
    bond_atoms: int,
    honest_reward_atoms: int,
    honest_external_gain_atoms: int,
    frivolous_external_gain_atoms: int,
    honest_accept_probability_bps: int,
    frivolous_accept_probability_bps: int,
) -> bool:
    """Exact BPS version of the internal probabilistic dispute predicate."""

    for name, value in (
        ("bond_atoms", bond_atoms),
        ("honest_reward_atoms", honest_reward_atoms),
        ("honest_external_gain_atoms", honest_external_gain_atoms),
        ("frivolous_external_gain_atoms", frivolous_external_gain_atoms),
    ):
        exact_nonnegative(value, name)
    for name, value in (
        ("honest_accept_probability_bps", honest_accept_probability_bps),
        ("frivolous_accept_probability_bps", frivolous_accept_probability_bps),
    ):
        if type(value) is not int or not 0 <= value <= BPS:
            raise ValueError(f"{name} must be in [0, 10000]")
    total_honest_gain_atoms = honest_reward_atoms + honest_external_gain_atoms
    honest_positive = (
        honest_accept_probability_bps * total_honest_gain_atoms
        > bond_atoms * BPS
    )
    frivolous_expected_gain_scaled = (
        frivolous_accept_probability_bps * total_honest_gain_atoms
        + (BPS - frivolous_accept_probability_bps)
        * frivolous_external_gain_atoms
    )
    frivolous_negative = frivolous_expected_gain_scaled < bond_atoms * BPS
    return honest_positive and frivolous_negative


def linked_assurance_pledge_dominates(
    *,
    buyer_value_atoms: int,
    pledge_atoms: int,
    delay_numerator: int,
    delay_denominator: int,
) -> bool:
    """Subtraction-free Nat condition for funding a non-rival public proof."""

    for name, value in (
        ("buyer_value_atoms", buyer_value_atoms),
        ("pledge_atoms", pledge_atoms),
        ("delay_numerator", delay_numerator),
        ("delay_denominator", delay_denominator),
    ):
        exact_nonnegative(value, name)
    if delay_denominator == 0 or delay_numerator >= delay_denominator:
        raise ValueError("delay ratio must satisfy 0 <= numerator < denominator")
    return (
        buyer_value_atoms * delay_denominator
        >= pledge_atoms * delay_denominator
        + delay_numerator * buyer_value_atoms
    )


def maintenance_subscription_sustainable(
    *,
    maintenance_cost_atoms: int,
    period_payment_atoms: int,
    slash_atoms: int,
    discount_numerator: int,
    discount_denominator: int,
    continuation_surplus_numerator: int,
    continuation_surplus_denominator: int,
) -> bool:
    """Exact one-shot-deviation predicate from the internal Lean candidate."""

    for name, value in (
        ("maintenance_cost_atoms", maintenance_cost_atoms),
        ("period_payment_atoms", period_payment_atoms),
        ("slash_atoms", slash_atoms),
        ("discount_numerator", discount_numerator),
        ("discount_denominator", discount_denominator),
        ("continuation_surplus_numerator", continuation_surplus_numerator),
        ("continuation_surplus_denominator", continuation_surplus_denominator),
    ):
        exact_nonnegative(value, name)
    if discount_denominator == 0 or discount_numerator >= discount_denominator:
        raise ValueError("discount ratio must satisfy 0 <= numerator < denominator")
    if continuation_surplus_denominator == 0:
        raise ValueError("continuation surplus denominator must be positive")
    left = maintenance_cost_atoms * (
        continuation_surplus_denominator
        * (discount_denominator - discount_numerator)
        + continuation_surplus_numerator * discount_numerator
    )
    right = continuation_surplus_numerator * (
        discount_numerator * period_payment_atoms
        + slash_atoms * (discount_denominator - discount_numerator)
    )
    return left <= right


@dataclass(frozen=True, slots=True)
class SearchContributionV1:
    contribution_id: str
    partition_id: str
    submission_epoch: int
    novel_coverage_units: int
    accepted: bool
    terminal_counterexample: bool


@dataclass(frozen=True, slots=True)
class CounterexamplePoolOutcomeV1:
    terminal_winner_id: str | None
    milestone_payments_atoms: tuple[tuple[str, int], ...]
    terminal_payment_atoms: int
    carry_atoms: int


def allocate_counterexample_pool(
    *,
    total_budget_atoms: int,
    milestone_budget_bps: int,
    contributions: tuple[SearchContributionV1, ...],
) -> CounterexamplePoolOutcomeV1:
    """Pay canonical search coverage plus one decisive counterexample.

    Each registry-issued partition may be paid once. Identity or wallet count
    does not appear in the allocation rule.
    """

    exact_nonnegative(total_budget_atoms, "total_budget_atoms")
    if type(milestone_budget_bps) is not int or not 0 <= milestone_budget_bps <= BPS:
        raise ValueError("milestone_budget_bps must be in [0, 10000]")
    if len({item.contribution_id for item in contributions}) != len(contributions):
        raise ValueError("contribution IDs must be unique")
    if len({item.partition_id for item in contributions}) != len(contributions):
        raise ValueError("each canonical partition may appear at most once")
    for item in contributions:
        exact_nonnegative(item.submission_epoch, "submission_epoch")
        exact_nonnegative(item.novel_coverage_units, "novel_coverage_units")

    milestone_budget_atoms = floor_bps(total_budget_atoms, milestone_budget_bps)
    terminal_budget_atoms = total_budget_atoms - milestone_budget_atoms
    terminal_candidates = sorted(
        (
            item
            for item in contributions
            if item.accepted and item.terminal_counterexample
        ),
        key=lambda item: (item.submission_epoch, item.contribution_id),
    )
    terminal_winner = terminal_candidates[0] if terminal_candidates else None
    terminal_payment_atoms = terminal_budget_atoms if terminal_winner else 0

    milestone_candidates = tuple(
        item
        for item in contributions
        if item.accepted
        and not item.terminal_counterexample
        and item.novel_coverage_units > 0
    )
    total_coverage_units = sum(
        item.novel_coverage_units for item in milestone_candidates
    )
    milestone_payments: list[tuple[str, int]] = []
    milestone_paid_atoms = 0
    for item in sorted(milestone_candidates, key=lambda row: row.contribution_id):
        payment_atoms = (
            milestone_budget_atoms * item.novel_coverage_units // total_coverage_units
            if total_coverage_units
            else 0
        )
        milestone_payments.append((item.contribution_id, payment_atoms))
        milestone_paid_atoms += payment_atoms
    carry_atoms = total_budget_atoms - terminal_payment_atoms - milestone_paid_atoms
    return CounterexamplePoolOutcomeV1(
        terminal_winner_id=(
            terminal_winner.contribution_id if terminal_winner is not None else None
        ),
        milestone_payments_atoms=tuple(milestone_payments),
        terminal_payment_atoms=terminal_payment_atoms,
        carry_atoms=carry_atoms,
    )


@dataclass(frozen=True, slots=True)
class MarketCandidateV1:
    candidate_id: str
    external_success_fee_bps: int
    listing_fee_atoms: int
    enterprise_subscription_atoms: int
    catalog_service_fee_atoms: int
    supports_enterprise_sla: bool
    supports_catalog_reuse: bool
    supports_linked_assurance: bool
    raw_volume_bonus_bps: int
    contribution_bonus_bps: int
    complexity_units: int


@dataclass(frozen=True, slots=True)
class MarketMonthScenarioV1:
    scenario_id: str
    weight_bps: int
    external_success_gmv_atoms: int
    successful_external_jobs: int
    external_listings: int
    enterprise_accounts: int
    catalog_service_events: int
    public_good_gmv_atoms: int
    anchor_user_fee_atoms: int
    anchor_proof_cost_atoms: int
    fixed_operations_cost_atoms: int
    variable_cost_per_listing_atoms: int
    variable_cost_per_success_atoms: int
    variable_cost_per_catalog_event_atoms: int
    enterprise_service_cost_per_account_atoms: int


@dataclass(frozen=True, slots=True)
class MarketMonthOutcomeV1:
    candidate_id: str
    scenario_id: str
    external_success_fee_revenue_atoms: int
    listing_revenue_atoms: int
    enterprise_revenue_atoms: int
    catalog_revenue_atoms: int
    external_protocol_revenue_atoms: int
    anchor_net_contribution_atoms: int
    operating_cost_atoms: int
    proof_reserve_bonus_atoms: int
    cash_surplus_atoms: int
    economic_surplus_after_bonus_atoms: int
    raw_volume_self_dealing_safe: bool


def _validate_candidate(candidate: MarketCandidateV1) -> None:
    if not candidate.candidate_id:
        raise ValueError("candidate_id must be nonempty")
    for name in (
        "listing_fee_atoms",
        "enterprise_subscription_atoms",
        "catalog_service_fee_atoms",
        "complexity_units",
    ):
        exact_nonnegative(getattr(candidate, name), name)
    for name in (
        "external_success_fee_bps",
        "raw_volume_bonus_bps",
        "contribution_bonus_bps",
    ):
        rate = getattr(candidate, name)
        if type(rate) is not int or not 0 <= rate <= BPS:
            raise ValueError(f"{name} must be in [0, 10000]")
    if candidate.raw_volume_bonus_bps and candidate.contribution_bonus_bps:
        raise ValueError("a candidate cannot activate both reward rules")


def _validate_scenario(scenario: MarketMonthScenarioV1) -> None:
    if not scenario.scenario_id:
        raise ValueError("scenario_id must be nonempty")
    for field_name in (
        "external_success_gmv_atoms",
        "successful_external_jobs",
        "external_listings",
        "enterprise_accounts",
        "catalog_service_events",
        "public_good_gmv_atoms",
        "anchor_user_fee_atoms",
        "anchor_proof_cost_atoms",
        "fixed_operations_cost_atoms",
        "variable_cost_per_listing_atoms",
        "variable_cost_per_success_atoms",
        "variable_cost_per_catalog_event_atoms",
        "enterprise_service_cost_per_account_atoms",
    ):
        exact_nonnegative(getattr(scenario, field_name), field_name)
    if type(scenario.weight_bps) is not int or not 0 <= scenario.weight_bps <= BPS:
        raise ValueError("weight_bps must be in [0, 10000]")
    if scenario.successful_external_jobs > scenario.external_listings:
        raise ValueError("successful jobs cannot exceed listings")


@dataclass(frozen=True, slots=True)
class _MarketRevenueV1:
    captured_gmv_atoms: int
    success_fee_atoms: int
    listing_atoms: int
    enterprise_atoms: int
    catalog_atoms: int

    @property
    def external_protocol_revenue_atoms(self) -> int:
        return (
            self.success_fee_atoms
            + self.listing_atoms
            + self.enterprise_atoms
            + self.catalog_atoms
        )


def _market_revenue(
    candidate: MarketCandidateV1,
    scenario: MarketMonthScenarioV1,
) -> _MarketRevenueV1:
    captured_gmv_atoms = scenario.external_success_gmv_atoms
    if candidate.supports_linked_assurance:
        captured_gmv_atoms += scenario.public_good_gmv_atoms
    return _MarketRevenueV1(
        captured_gmv_atoms=captured_gmv_atoms,
        success_fee_atoms=floor_bps(
            captured_gmv_atoms, candidate.external_success_fee_bps
        ),
        listing_atoms=scenario.external_listings * candidate.listing_fee_atoms,
        enterprise_atoms=(
            scenario.enterprise_accounts * candidate.enterprise_subscription_atoms
            if candidate.supports_enterprise_sla
            else 0
        ),
        catalog_atoms=(
            scenario.catalog_service_events * candidate.catalog_service_fee_atoms
            if candidate.supports_catalog_reuse
            else 0
        ),
    )


def _market_operating_cost(
    candidate: MarketCandidateV1,
    scenario: MarketMonthScenarioV1,
) -> int:
    catalog_cost_atoms = (
        scenario.catalog_service_events
        * scenario.variable_cost_per_catalog_event_atoms
        if candidate.supports_catalog_reuse
        else 0
    )
    enterprise_cost_atoms = (
        scenario.enterprise_accounts
        * scenario.enterprise_service_cost_per_account_atoms
        if candidate.supports_enterprise_sla
        else 0
    )
    return (
        scenario.fixed_operations_cost_atoms
        + scenario.external_listings * scenario.variable_cost_per_listing_atoms
        + scenario.successful_external_jobs
        * scenario.variable_cost_per_success_atoms
        + catalog_cost_atoms
        + enterprise_cost_atoms
    )


def _market_bonus(
    candidate: MarketCandidateV1,
    revenue: _MarketRevenueV1,
) -> int:
    """Return the external-market bootstrap bonus for one month.

    The general-market simulation cannot use ZRPF savings to enlarge an
    external-job reward.  ZRPF has its own source-bound submodel.  This lane is
    therefore capped at one half of irreversible external success fees even if
    a candidate requests a larger useful-value rate.
    """

    if candidate.raw_volume_bonus_bps:
        return floor_bps(
            revenue.captured_gmv_atoms,
            candidate.raw_volume_bonus_bps,
        )
    if not candidate.contribution_bonus_bps:
        return 0
    return min(
        floor_bps(
            revenue.captured_gmv_atoms,
            candidate.contribution_bonus_bps,
        ),
        floor_bps(revenue.success_fee_atoms, 5_000),
    )


def _raw_volume_self_dealing_safe(
    candidate: MarketCandidateV1,
    scenario: MarketMonthScenarioV1,
    captured_gmv_atoms: int,
) -> bool:
    if not candidate.raw_volume_bonus_bps:
        return True
    average_gmv_atoms = (
        ceil_div(captured_gmv_atoms, scenario.successful_external_jobs)
        if scenario.successful_external_jobs
        else 0
    )
    fee_atoms = floor_bps(average_gmv_atoms, candidate.external_success_fee_bps)
    bonus_atoms = floor_bps(average_gmv_atoms, candidate.raw_volume_bonus_bps)
    return bonus_atoms <= fee_atoms


def simulate_market_month(
    candidate: MarketCandidateV1,
    scenario: MarketMonthScenarioV1,
) -> MarketMonthOutcomeV1:
    """Evaluate one exact monthly cash-flow and manipulation scenario."""

    _validate_candidate(candidate)
    _validate_scenario(scenario)
    revenue = _market_revenue(candidate, scenario)
    anchor_net_contribution_atoms = (
        scenario.anchor_user_fee_atoms - scenario.anchor_proof_cost_atoms
    )
    operating_cost_atoms = _market_operating_cost(candidate, scenario)
    proof_reserve_bonus_atoms = _market_bonus(candidate, revenue)
    cash_surplus_atoms = (
        revenue.external_protocol_revenue_atoms
        + anchor_net_contribution_atoms
        - operating_cost_atoms
    )
    economic_surplus_after_bonus_atoms = cash_surplus_atoms - proof_reserve_bonus_atoms
    return MarketMonthOutcomeV1(
        candidate_id=candidate.candidate_id,
        scenario_id=scenario.scenario_id,
        external_success_fee_revenue_atoms=revenue.success_fee_atoms,
        listing_revenue_atoms=revenue.listing_atoms,
        enterprise_revenue_atoms=revenue.enterprise_atoms,
        catalog_revenue_atoms=revenue.catalog_atoms,
        external_protocol_revenue_atoms=revenue.external_protocol_revenue_atoms,
        anchor_net_contribution_atoms=anchor_net_contribution_atoms,
        operating_cost_atoms=operating_cost_atoms,
        proof_reserve_bonus_atoms=proof_reserve_bonus_atoms,
        cash_surplus_atoms=cash_surplus_atoms,
        economic_surplus_after_bonus_atoms=economic_surplus_after_bonus_atoms,
        raw_volume_self_dealing_safe=_raw_volume_self_dealing_safe(
            candidate,
            scenario,
            revenue.captured_gmv_atoms,
        ),
    )


@dataclass(frozen=True, slots=True)
class CandidateEvaluationV1:
    candidate_id: str
    expected_monthly_surplus_atoms: int
    expected_monthly_surplus_after_bonus_atoms: int
    probability_positive_bps: int
    worst_monthly_loss_atoms: int
    negative_complexity_units: int
    manipulation_safe: bool
    outcomes: tuple[MarketMonthOutcomeV1, ...]


def evaluate_market_candidate(
    candidate: MarketCandidateV1,
    scenarios: tuple[MarketMonthScenarioV1, ...],
) -> CandidateEvaluationV1:
    """Compute exact weighted objectives for a closed scenario set."""

    _validate_candidate(candidate)
    if not scenarios:
        raise ValueError("at least one scenario is required")
    for scenario in scenarios:
        _validate_scenario(scenario)
    if sum(scenario.weight_bps for scenario in scenarios) != BPS:
        raise ValueError("scenario weights must sum to 10000 bps")
    outcomes = tuple(simulate_market_month(candidate, scenario) for scenario in scenarios)
    expected_surplus_atoms = sum(
        outcome.cash_surplus_atoms * scenario.weight_bps
        for outcome, scenario in zip(outcomes, scenarios, strict=True)
    ) // BPS
    expected_surplus_after_bonus_atoms = sum(
        outcome.economic_surplus_after_bonus_atoms * scenario.weight_bps
        for outcome, scenario in zip(outcomes, scenarios, strict=True)
    ) // BPS
    probability_positive_bps = sum(
        scenario.weight_bps
        for outcome, scenario in zip(outcomes, scenarios, strict=True)
        if outcome.cash_surplus_atoms > 0
    )
    worst_monthly_loss_atoms = max(0, -min(outcome.cash_surplus_atoms for outcome in outcomes))
    return CandidateEvaluationV1(
        candidate_id=candidate.candidate_id,
        expected_monthly_surplus_atoms=expected_surplus_atoms,
        expected_monthly_surplus_after_bonus_atoms=expected_surplus_after_bonus_atoms,
        probability_positive_bps=probability_positive_bps,
        worst_monthly_loss_atoms=worst_monthly_loss_atoms,
        negative_complexity_units=-candidate.complexity_units,
        manipulation_safe=all(outcome.raw_volume_self_dealing_safe for outcome in outcomes),
        outcomes=outcomes,
    )


def _dominates(left: CandidateEvaluationV1, right: CandidateEvaluationV1) -> bool:
    if not left.manipulation_safe:
        return False
    if not right.manipulation_safe:
        return True
    left_values = (
        left.expected_monthly_surplus_after_bonus_atoms,
        left.probability_positive_bps,
        -left.worst_monthly_loss_atoms,
        left.negative_complexity_units,
    )
    right_values = (
        right.expected_monthly_surplus_after_bonus_atoms,
        right.probability_positive_bps,
        -right.worst_monthly_loss_atoms,
        right.negative_complexity_units,
    )
    return all(a >= b for a, b in zip(left_values, right_values, strict=True)) and any(
        a > b for a, b in zip(left_values, right_values, strict=True)
    )


def pareto_frontier(
    evaluations: Iterable[CandidateEvaluationV1],
) -> tuple[CandidateEvaluationV1, ...]:
    rows = tuple(evaluations)
    if len({row.candidate_id for row in rows}) != len(rows):
        raise ValueError("candidate IDs must be unique")
    frontier = tuple(
        row
        for row in rows
        if row.manipulation_safe
        and not any(_dominates(other, row) for other in rows if other is not row)
    )
    return tuple(sorted(frontier, key=lambda row: row.candidate_id))


def minimum_external_gmv_for_break_even(
    *,
    monthly_fixed_gap_atoms: int,
    success_fee_bps: int,
) -> int:
    """GMV needed to cover a fixed monthly gap at the declared take rate."""

    exact_nonnegative(monthly_fixed_gap_atoms, "monthly_fixed_gap_atoms")
    if type(success_fee_bps) is not int or success_fee_bps <= 0:
        raise ValueError("success_fee_bps must be positive")
    return ceil_div(monthly_fixed_gap_atoms * BPS, success_fee_bps)
