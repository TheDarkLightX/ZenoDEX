"""Exact bounded accounting helpers for proof-market game theory V2.

This pure research module grants no payment, slashing, reward, or settlement
authority.  All amounts are integer atoms; live parameters remain unselected.
"""

from __future__ import annotations

import hashlib
import unicodedata
from dataclasses import dataclass
from enum import StrEnum
from fractions import Fraction
from itertools import product
from typing import Final, Iterable

BPS: Final = 10_000
MAX_ATOMS: Final = 2**256 - 1
CANONICAL_WORK_KEY_PREFIX_V2: Final = "ewk:v2:"
CANONICAL_WORK_KEY_DOMAIN_V2: Final = b"ZenoDEX/EconomicWorkKey/v2\x00"
MAX_CANONICAL_WORK_FIELD_BYTES_V2: Final = 1_048_576
_ECONOMIC_WORK_FIELDS_V2: Final = (
    "product_kind",
    "claim",
    "assumptions",
    "public_inputs",
    "requested_output",
    "verifier_profile",
    "release",
)


def exact_natural(value: int, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_ATOMS:
        raise ValueError(f"{name} must be an exact integer in [0, 2^256-1]")
    return value


def exact_positive(value: int, name: str) -> int:
    exact_natural(value, name)
    if value == 0:
        raise ValueError(f"{name} must be positive")
    return value


def ceil_div(numerator: int, denominator: int) -> int:
    exact_natural(numerator, "numerator")
    exact_positive(denominator, "denominator")
    result = numerator // denominator + int(numerator % denominator != 0)
    return exact_natural(result, "ceil_div result")


def ceil_bps(amount: int, rate_bps: int) -> int:
    exact_natural(amount, "amount")
    exact_natural(rate_bps, "rate_bps")
    product = amount * rate_bps
    result = product // BPS + int(product % BPS != 0)
    return exact_natural(result, "ceil_bps result")


@dataclass(frozen=True, slots=True)
class EconomicWorkDescriptorV2:
    """Exact textual fields that define one reserve-eligible work unit."""

    product_kind: str
    claim: str
    assumptions: str
    public_inputs: str
    requested_output: str
    verifier_profile: str
    release: str


def _canonical_work_field_bytes(value: str, name: str) -> bytes:
    if type(value) is not str or not value:
        raise ValueError(f"{name} must be a nonempty exact string")
    if value != value.strip():
        raise ValueError(f"{name} must not have leading or trailing whitespace")
    if value != unicodedata.normalize("NFC", value):
        raise ValueError(f"{name} must be NFC-normalized")
    if any(unicodedata.category(character).startswith("C") for character in value):
        raise ValueError(f"{name} must not contain control or format characters")
    encoded = value.encode("utf-8")
    if len(encoded) > MAX_CANONICAL_WORK_FIELD_BYTES_V2:
        raise ValueError(f"{name} exceeds the canonical field byte bound")
    return encoded


def canonical_economic_work_key_bytes(
    descriptor: EconomicWorkDescriptorV2,
) -> bytes:
    """Encode a work descriptor into its exact domain-separated bytes.

    The encoding is domain-separated and length-prefixed.  Field order is the
    order declared in ``_ECONOMIC_WORK_FIELDS_V2``; each field name and value is
    encoded as a four-byte big-endian length followed by UTF-8 bytes.  Inputs
    must already be NFC-normalized, so this helper never silently rewrites a
    caller's work description.  Semantic equivalence remains outside this
    exact-encoding contract.
    """

    if type(descriptor) is not EconomicWorkDescriptorV2:
        raise ValueError("descriptor must be an exact EconomicWorkDescriptorV2")
    encoded = bytearray(CANONICAL_WORK_KEY_DOMAIN_V2)
    for field_name in _ECONOMIC_WORK_FIELDS_V2:
        field_name_bytes = field_name.encode("ascii")
        field_value_bytes = _canonical_work_field_bytes(
            getattr(descriptor, field_name),
            field_name,
        )
        for field_bytes in (field_name_bytes, field_value_bytes):
            encoded.extend(len(field_bytes).to_bytes(4, "big"))
            encoded.extend(field_bytes)
    return bytes(encoded)


def canonical_economic_work_key(
    descriptor: EconomicWorkDescriptorV2,
) -> str:
    """Return the lowercase SHA-256 key for canonical work bytes."""

    digest = hashlib.sha256(canonical_economic_work_key_bytes(descriptor)).hexdigest()
    return f"{CANONICAL_WORK_KEY_PREFIX_V2}{digest}"


@dataclass(frozen=True, slots=True)
class CartelResultV2:
    cooperate_present_value: Fraction
    deviate_present_value: Fraction
    sustainable: bool


@dataclass(frozen=True, slots=True)
class StationaryEqualShareCartelScenarioV2:
    prover_count: int
    discount_numerator: int
    discount_denominator: int
    monopoly_margin_atoms: int
    punishment_margin_atoms: int


def stationary_equal_share_cartel(
    scenario: StationaryEqualShareCartelScenarioV2,
) -> CartelResultV2:
    """Evaluate a stationary equal-share cartel against one-shot capture.

    The cooperative continuation value assumes an enforceable equal expected
    share in every period (for example, transfers or a stationary fair lottery).
    It is not the continuation value of a member at an arbitrary position in a
    deterministic rotation.
    """

    if type(scenario.prover_count) is not int or scenario.prover_count < 2:
        raise ValueError("prover_count must be an exact integer at least two")
    exact_natural(scenario.discount_numerator, "discount_numerator")
    exact_positive(scenario.discount_denominator, "discount_denominator")
    if scenario.discount_numerator >= scenario.discount_denominator:
        raise ValueError("discount factor must be in [0, 1)")
    exact_natural(scenario.monopoly_margin_atoms, "monopoly_margin_atoms")
    exact_natural(scenario.punishment_margin_atoms, "punishment_margin_atoms")
    discount = Fraction(
        scenario.discount_numerator,
        scenario.discount_denominator,
    )
    cooperative_flow = Fraction(
        scenario.monopoly_margin_atoms,
        scenario.prover_count,
    )
    cooperate_pv = cooperative_flow / (1 - discount)
    deviate_pv = Fraction(scenario.monopoly_margin_atoms) + (
        discount * scenario.punishment_margin_atoms / (1 - discount)
    )
    return CartelResultV2(
        cooperate_present_value=cooperate_pv,
        deviate_present_value=deviate_pv,
        sustainable=cooperate_pv >= deviate_pv,
    )


def stationary_equal_share_cartel_threshold(prover_count: int) -> Fraction:
    if type(prover_count) is not int or prover_count < 2:
        raise ValueError("prover_count must be an exact integer at least two")
    return Fraction(prover_count - 1, prover_count)


@dataclass(frozen=True, slots=True)
class DefaultLossV2:
    replacement_premium_atoms: int
    standardized_delay_loss_atoms: int
    verifier_waste_atoms: int
    standby_activation_atoms: int

    @property
    def restitution_atoms(self) -> int:
        values = (
            self.replacement_premium_atoms,
            self.standardized_delay_loss_atoms,
            self.verifier_waste_atoms,
            self.standby_activation_atoms,
        )
        for index, value in enumerate(values):
            exact_natural(value, f"default_loss[{index}]")
        return exact_natural(sum(values), "restitution_atoms")


@dataclass(frozen=True, slots=True)
class DefaultBondRequestV2:
    loss: DefaultLossV2
    avoidable_cost_atoms: int
    bounded_sabotage_gain_atoms: int
    future_value_lost_atoms: int
    detection_probability_bps: int


def required_deterrence_bond(
    *,
    avoidable_cost_atoms: int,
    bounded_sabotage_gain_atoms: int,
    future_value_lost_atoms: int,
    detection_probability_bps: int,
) -> int:
    """Return the least slash satisfying the declared bounded deviation model."""

    exact_natural(avoidable_cost_atoms, "avoidable_cost_atoms")
    exact_natural(bounded_sabotage_gain_atoms, "bounded_sabotage_gain_atoms")
    exact_natural(future_value_lost_atoms, "future_value_lost_atoms")
    exact_positive(detection_probability_bps, "detection_probability_bps")
    if detection_probability_bps > BPS:
        raise ValueError("detection_probability_bps must be at most 10000")
    gross_gain = avoidable_cost_atoms + bounded_sabotage_gain_atoms
    uncovered_gain = max(0, gross_gain - future_value_lost_atoms)
    numerator = uncovered_gain * BPS
    result = numerator // detection_probability_bps + int(
        numerator % detection_probability_bps != 0
    )
    return exact_natural(result, "required_deterrence_bond")


def required_default_bond(
    request: DefaultBondRequestV2,
) -> int:
    deterrence = required_deterrence_bond(
        avoidable_cost_atoms=request.avoidable_cost_atoms,
        bounded_sabotage_gain_atoms=request.bounded_sabotage_gain_atoms,
        future_value_lost_atoms=request.future_value_lost_atoms,
        detection_probability_bps=request.detection_probability_bps,
    )
    return max(request.loss.restitution_atoms, deterrence)


@dataclass(frozen=True, slots=True)
class DefaultBondDispositionV2:
    replacement_premium_atoms: int
    standardized_delay_loss_atoms: int
    verifier_waste_atoms: int
    standby_activation_atoms: int
    residual_penalty_insurance_atoms: int
    seller_return_atoms: int

    @property
    def total_atoms(self) -> int:
        return sum(
            (
                self.replacement_premium_atoms,
                self.standardized_delay_loss_atoms,
                self.verifier_waste_atoms,
                self.standby_activation_atoms,
                self.residual_penalty_insurance_atoms,
                self.seller_return_atoms,
            )
        )


def dispose_prover_fault_bond(
    bond_atoms: int,
    loss: DefaultLossV2,
) -> DefaultBondDispositionV2:
    """Fully slash proven prover-fault bond after funding named losses."""

    exact_natural(bond_atoms, "bond_atoms")
    if bond_atoms < loss.restitution_atoms:
        raise ValueError("bond does not cover named restitution")
    return DefaultBondDispositionV2(
        replacement_premium_atoms=loss.replacement_premium_atoms,
        standardized_delay_loss_atoms=loss.standardized_delay_loss_atoms,
        verifier_waste_atoms=loss.verifier_waste_atoms,
        standby_activation_atoms=loss.standby_activation_atoms,
        residual_penalty_insurance_atoms=bond_atoms - loss.restitution_atoms,
        seller_return_atoms=0,
    )


def verifier_fault_bond_return(bond_atoms: int) -> int:
    """Verifier infrastructure failure carries no prover-fault slash."""

    return exact_natural(bond_atoms, "bond_atoms")


class ProofReserveEligibilityV2(StrEnum):
    INDEPENDENTLY_BASE_FUNDED_VERIFIED_UNCLAIMED_UNRELATED = (
        "INDEPENDENTLY_BASE_FUNDED_VERIFIED_UNCLAIMED_UNRELATED"
    )
    BASE_PAYMENT_UNFUNDED = "BASE_PAYMENT_UNFUNDED"
    WORK_UNVERIFIED = "WORK_UNVERIFIED"
    WORK_KEY_ALREADY_CLAIMED = "WORK_KEY_ALREADY_CLAIMED"
    SELF_DEALING_OR_RELATED_PARTY = "SELF_DEALING_OR_RELATED_PARTY"
    BENEFICIAL_OWNER_EVIDENCE_MISSING = "BENEFICIAL_OWNER_EVIDENCE_MISSING"


@dataclass(frozen=True, slots=True)
class ProofReserveRequestV2:
    reserve_remaining_atoms: int
    job_bonus_cap_atoms: int
    owner_epoch_remaining_atoms: int
    eligibility: ProofReserveEligibilityV2


def proof_reserve_bonus(request: ProofReserveRequestV2) -> int:
    """Return a finite ZDEX bonus cap without consuming reserve state.

    This helper is a pure arithmetic cap.  Claim uniqueness and reserve
    consumption belong to ``claim_proof_reserve_bonus`` below.
    """

    values = (
        exact_natural(request.reserve_remaining_atoms, "reserve_remaining_atoms"),
        exact_natural(request.job_bonus_cap_atoms, "job_bonus_cap_atoms"),
        exact_natural(
            request.owner_epoch_remaining_atoms,
            "owner_epoch_remaining_atoms",
        ),
    )
    if request.eligibility is not (
        ProofReserveEligibilityV2.INDEPENDENTLY_BASE_FUNDED_VERIFIED_UNCLAIMED_UNRELATED
    ):
        return 0
    return min(values)


class ProofReserveClaimRejectV2(StrEnum):
    INVALID_WORK_KEY = "INVALID_WORK_KEY"
    INELIGIBLE = "INELIGIBLE"
    WORK_KEY_ALREADY_CLAIMED = "WORK_KEY_ALREADY_CLAIMED"
    NO_BONUS_CAPACITY = "NO_BONUS_CAPACITY"


@dataclass(frozen=True, slots=True)
class ProofReserveClaimStateV2:
    """Immutable reserve state for exact-key, single-consumption claims."""

    reserve_remaining_atoms: int
    owner_epoch_remaining_atoms: int
    claimed_work_keys: frozenset[str] = frozenset()


@dataclass(frozen=True, slots=True)
class ProofReserveClaimRequestV2:
    work_descriptor: EconomicWorkDescriptorV2
    job_bonus_cap_atoms: int
    eligibility: ProofReserveEligibilityV2

    @property
    def economic_work_key(self) -> str:
        """Derive the nullifier from the descriptor; callers cannot supply it."""

        return canonical_economic_work_key(self.work_descriptor)


@dataclass(frozen=True, slots=True)
class ProofReserveClaimAcceptedV2:
    state: ProofReserveClaimStateV2
    bonus_atoms: int


@dataclass(frozen=True, slots=True)
class ProofReserveClaimRejectedV2:
    reason: ProofReserveClaimRejectV2


ProofReserveClaimDecisionV2 = (
    ProofReserveClaimAcceptedV2 | ProofReserveClaimRejectedV2
)


def _is_canonical_economic_work_key(work_key: object) -> bool:
    if type(work_key) is not str:
        return False
    if not work_key.startswith(CANONICAL_WORK_KEY_PREFIX_V2):
        return False
    digest = work_key[len(CANONICAL_WORK_KEY_PREFIX_V2) :]
    return len(digest) == 64 and all(
        character in "0123456789abcdef" for character in digest
    )


def _validate_economic_work_key(work_key: str) -> str:
    if not _is_canonical_economic_work_key(work_key):
        raise ValueError("economic_work_key must be a canonical ewk:v2 key")
    return work_key


def _validate_proof_reserve_claim_state(
    state: ProofReserveClaimStateV2,
) -> None:
    exact_natural(state.reserve_remaining_atoms, "reserve_remaining_atoms")
    exact_natural(
        state.owner_epoch_remaining_atoms,
        "owner_epoch_remaining_atoms",
    )
    if type(state.claimed_work_keys) is not frozenset:
        raise ValueError("claimed_work_keys must be an exact frozenset")
    for work_key in state.claimed_work_keys:
        _validate_economic_work_key(work_key)


def claim_proof_reserve_bonus(
    state: ProofReserveClaimStateV2,
    request: ProofReserveClaimRequestV2,
) -> ProofReserveClaimDecisionV2:
    """Consume one exact ``EconomicWorkKey`` bonus from immutable reserve state.

    Numeric validation is deterministic and raises ``ValueError`` for malformed
    model inputs.  A valid but ineligible, already-claimed, or zero-capacity
    request returns a typed rejection and leaves the supplied state unchanged.
    Accepted claims decrement both reserve caps and add exactly one key.
    """

    _validate_proof_reserve_claim_state(state)
    try:
        economic_work_key = request.economic_work_key
    except ValueError:
        return ProofReserveClaimRejectedV2(ProofReserveClaimRejectV2.INVALID_WORK_KEY)
    exact_natural(request.job_bonus_cap_atoms, "job_bonus_cap_atoms")
    if request.eligibility is not (
        ProofReserveEligibilityV2
        .INDEPENDENTLY_BASE_FUNDED_VERIFIED_UNCLAIMED_UNRELATED
    ):
        return ProofReserveClaimRejectedV2(ProofReserveClaimRejectV2.INELIGIBLE)
    if economic_work_key in state.claimed_work_keys:
        return ProofReserveClaimRejectedV2(
            ProofReserveClaimRejectV2.WORK_KEY_ALREADY_CLAIMED
        )

    bonus_atoms = proof_reserve_bonus(
        ProofReserveRequestV2(
            state.reserve_remaining_atoms,
            request.job_bonus_cap_atoms,
            state.owner_epoch_remaining_atoms,
            request.eligibility,
        )
    )
    if bonus_atoms == 0:
        return ProofReserveClaimRejectedV2(ProofReserveClaimRejectV2.NO_BONUS_CAPACITY)
    return ProofReserveClaimAcceptedV2(
        state=ProofReserveClaimStateV2(
            reserve_remaining_atoms=state.reserve_remaining_atoms - bonus_atoms,
            owner_epoch_remaining_atoms=(
                state.owner_epoch_remaining_atoms - bonus_atoms
            ),
            claimed_work_keys=state.claimed_work_keys
            | frozenset((economic_work_key,)),
        ),
        bonus_atoms=bonus_atoms,
    )


class AwardKindV2(StrEnum):
    SCARCITY_PROVER = "SCARCITY_PROVER"
    DIRECT_EXECUTION = "DIRECT_EXECUTION"
    UNFUNDED_REJECT = "UNFUNDED_REJECT"


@dataclass(frozen=True, slots=True)
class FallbackAwardV2:
    kind: AwardKindV2
    winner_index: int | None
    payment_atoms: int


@dataclass(frozen=True, slots=True)
class StageWithholdingSearchV2:
    deviation_queries: int
    profitable_deviation: tuple[int, int, int, int, int, int] | None

    @property
    def no_profitable_deviation(self) -> bool:
        return self.profitable_deviation is None


def _lowest_positive_eligible_bid(
    sealed_bids: tuple[int, ...],
    job_cap_atoms: int,
) -> tuple[int, int] | None:
    eligible: list[tuple[int, int]] = []
    for index, bid in enumerate(sealed_bids):
        exact_positive(bid, f"sealed_bids[{index}]")
        if bid <= job_cap_atoms:
            eligible.append((bid, index))
    if not eligible:
        return None
    payment, winner = min(eligible)
    return winner, payment


def scarcity_or_direct_award(
    *,
    sealed_bids: tuple[int, ...],
    posted_price_atoms: int,
    job_cap_atoms: int,
    direct_execution_cost_atoms: int,
) -> FallbackAwardV2:
    """Choose the cheaper same-cap late bid or direct outside option."""

    exact_natural(posted_price_atoms, "posted_price_atoms")
    exact_natural(job_cap_atoms, "job_cap_atoms")
    exact_natural(direct_execution_cost_atoms, "direct_execution_cost_atoms")
    if job_cap_atoms > posted_price_atoms:
        raise ValueError("same-occurrence fallback cap exceeds posted price")
    if any(bid == 0 for bid in sealed_bids):
        raise ValueError("scarcity bids must be positive")
    seller = _lowest_positive_eligible_bid(sealed_bids, job_cap_atoms)
    direct_payment = (
        direct_execution_cost_atoms
        if direct_execution_cost_atoms <= job_cap_atoms
        else None
    )
    seller_payment = seller[1] if seller is not None else None
    if direct_payment is not None and (
        seller_payment is None or direct_payment <= seller_payment
    ):
        return FallbackAwardV2(AwardKindV2.DIRECT_EXECUTION, None, direct_payment)
    if seller is not None:
        return FallbackAwardV2(AwardKindV2.SCARCITY_PROVER, *seller)
    return FallbackAwardV2(AwardKindV2.UNFUNDED_REJECT, None, 0)


def enumerate_single_provider_stage_withholding(
    domain_max_atoms: int,
) -> StageWithholdingSearchV2:
    """Search a one-provider same-occurrence withholding deviation.

    Normal assignment is certain in this bounded game.  Normal and late lanes
    have identical compute, capital-lock, opportunity, bonus, and information
    costs.  The search therefore establishes no claim once those costs or the
    normal assignment probability differ.
    """

    exact_positive(domain_max_atoms, "domain_max_atoms")
    queries = 0
    for posted_price in range(1, domain_max_atoms + 1):
        cases = product(
            range(posted_price + 1),
            range(1, posted_price + 1),
            range(domain_max_atoms + 1),
            range(1, posted_price + 1),
        )
        for cost, cap, direct_cost, late_bid in cases:
            if late_bid > cap:
                continue
            queries += 1
            outcome = scarcity_or_direct_award(
                sealed_bids=(late_bid,),
                posted_price_atoms=posted_price,
                job_cap_atoms=cap,
                direct_execution_cost_atoms=direct_cost,
            )
            late_utility = (
                outcome.payment_atoms - cost
                if outcome.kind is AwardKindV2.SCARCITY_PROVER
                else 0
            )
            normal_utility = posted_price - cost
            if late_utility > normal_utility:
                witness = (
                    posted_price,
                    cost,
                    cap,
                    direct_cost,
                    late_bid,
                    late_utility - normal_utility,
                )
                return StageWithholdingSearchV2(queries, witness)
    return StageWithholdingSearchV2(queries, None)


@dataclass(frozen=True, slots=True)
class DutchDelayContextV2:
    minimum_price_atoms: int
    maximum_price_atoms: int
    ramp_duration_seconds: int
    initial_work_seconds: int
    required_work_seconds: int
    next_acceptance_price_atoms: int | None


def maximum_safe_dutch_delay_price(context: DutchDelayContextV2) -> int:
    """Return the largest price preserving work time and an earlier stop."""

    for name, value in (
        ("minimum_price_atoms", context.minimum_price_atoms),
        ("maximum_price_atoms", context.maximum_price_atoms),
        ("ramp_duration_seconds", context.ramp_duration_seconds),
        ("initial_work_seconds", context.initial_work_seconds),
        ("required_work_seconds", context.required_work_seconds),
    ):
        exact_natural(value, name)
    if context.minimum_price_atoms > context.maximum_price_atoms:
        raise ValueError("minimum price exceeds maximum price")
    if context.next_acceptance_price_atoms is not None:
        exact_natural(
            context.next_acceptance_price_atoms,
            "next_acceptance_price_atoms",
        )
        if context.next_acceptance_price_atoms <= context.minimum_price_atoms:
            raise ValueError(
                "no safe delay exists: no price below the next acceptance"
            )
    if context.initial_work_seconds < context.required_work_seconds:
        raise ValueError("no safe delay exists: required work exceeds remaining window")
    if (
        context.ramp_duration_seconds == 0
        or context.maximum_price_atoms == context.minimum_price_atoms
    ):
        time_cap = context.maximum_price_atoms
    else:
        available_delay = context.initial_work_seconds - context.required_work_seconds
        span = context.maximum_price_atoms - context.minimum_price_atoms
        time_cap = (
            context.minimum_price_atoms
            + available_delay * span // context.ramp_duration_seconds
        )
    competition_cap = context.maximum_price_atoms
    if context.next_acceptance_price_atoms is not None:
        competition_cap = max(
            context.minimum_price_atoms,
            context.next_acceptance_price_atoms
            - int(context.next_acceptance_price_atoms > 0),
        )
    return min(context.maximum_price_atoms, time_cap, competition_cap)


def weighted_floor_average(rows: Iterable[tuple[int, int, int]]) -> int:
    """Average max(reported, minimum), using exact integer weights."""

    total_weight = 0
    total_value = 0
    for reported_atoms, minimum_atoms, weight in rows:
        exact_natural(reported_atoms, "reported_atoms")
        exact_natural(minimum_atoms, "minimum_atoms")
        exact_natural(weight, "weight")
        total_weight += weight
        total_value += max(reported_atoms, minimum_atoms) * weight
    exact_positive(total_weight, "total_weight")
    return total_value // total_weight


def next_posted_price_after_round(
    *,
    current_price_atoms: int,
    acceptance_count: int,
) -> int:
    """Same-round acceptance or boycott cannot ratchet the benchmark price."""

    exact_natural(current_price_atoms, "current_price_atoms")
    exact_natural(acceptance_count, "acceptance_count")
    return current_price_atoms
