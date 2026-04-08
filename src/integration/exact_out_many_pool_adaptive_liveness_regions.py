from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable

from .cantor_prefix_algebra import CantorPrefixRegion, partition_ok
from .exact_out_route_certificate import ExactOutManyPoolAdaptiveLivenessPacket


AdaptiveLivenessWord = tuple[int, int, int, int, int, int, int, int, int, int, int, int, int, int]


@dataclass(frozen=True)
class ExactOutManyPoolAdaptiveLivenessInputs:
    selected_domain_budget_respected: bool
    repaired_selection_budget_respected: bool
    full_domain_pool_budget_respected: bool
    full_domain_candidate_budget_respected: bool
    budget_parameters_bound: bool
    cheap_path_attempted: bool
    cheap_path_success: bool
    fallback_required: bool
    fallback_attempted: bool
    fallback_available: bool
    returned_success: bool
    explicit_failure: bool
    effective_quote_present: bool
    failure_reason_present: bool

    def to_word(self) -> AdaptiveLivenessWord:
        return (
            int(bool(self.selected_domain_budget_respected)),
            int(bool(self.repaired_selection_budget_respected)),
            int(bool(self.full_domain_pool_budget_respected)),
            int(bool(self.full_domain_candidate_budget_respected)),
            int(bool(self.budget_parameters_bound)),
            int(bool(self.cheap_path_attempted)),
            int(bool(self.cheap_path_success)),
            int(bool(self.fallback_required)),
            int(bool(self.fallback_attempted)),
            int(bool(self.fallback_available)),
            int(bool(self.returned_success)),
            int(bool(self.explicit_failure)),
            int(bool(self.effective_quote_present)),
            int(bool(self.failure_reason_present)),
        )

    @classmethod
    def from_word(cls, word: Iterable[int | bool]) -> "ExactOutManyPoolAdaptiveLivenessInputs":
        bits = tuple(int(bool(bit)) for bit in word)
        if len(bits) != 14:
            raise ValueError("exact-out adaptive liveness words must have exactly 14 bits")
        return cls(
            selected_domain_budget_respected=bool(bits[0]),
            repaired_selection_budget_respected=bool(bits[1]),
            full_domain_pool_budget_respected=bool(bits[2]),
            full_domain_candidate_budget_respected=bool(bits[3]),
            budget_parameters_bound=bool(bits[4]),
            cheap_path_attempted=bool(bits[5]),
            cheap_path_success=bool(bits[6]),
            fallback_required=bool(bits[7]),
            fallback_attempted=bool(bits[8]),
            fallback_available=bool(bits[9]),
            returned_success=bool(bits[10]),
            explicit_failure=bool(bits[11]),
            effective_quote_present=bool(bits[12]),
            failure_reason_present=bool(bits[13]),
        )

    @classmethod
    def from_packet(cls, packet: ExactOutManyPoolAdaptiveLivenessPacket) -> "ExactOutManyPoolAdaptiveLivenessInputs":
        contract = packet.audited_bounds_contract
        return cls(
            selected_domain_budget_respected=bool(contract.selected_domain_budget_respected),
            repaired_selection_budget_respected=bool(contract.repaired_selection_budget_respected),
            full_domain_pool_budget_respected=bool(contract.full_domain_pool_budget_respected),
            full_domain_candidate_budget_respected=bool(contract.full_domain_candidate_budget_respected),
            budget_parameters_bound=bool(contract.budget_parameters_bound),
            cheap_path_attempted=bool(packet.cheap_path_attempted),
            cheap_path_success=bool(packet.cheap_path_success),
            fallback_required=bool(packet.fallback_required),
            fallback_attempted=bool(packet.fallback_attempted),
            fallback_available=bool(packet.fallback_available),
            returned_success=bool(packet.returned_success),
            explicit_failure=bool(packet.explicit_failure),
            effective_quote_present=bool(packet.effective_quote is not None),
            failure_reason_present=bool(packet.failure_reason_present),
        )


@dataclass(frozen=True)
class ExactOutManyPoolAdaptiveLivenessRegions:
    budget_facts_ok: CantorPrefixRegion
    attempt_order_ok: CantorPrefixRegion
    outcome_total: CantorPrefixRegion
    success_replayable: CantorPrefixRegion
    failure_total: CantorPrefixRegion
    no_spurious_failure: CantorPrefixRegion
    coherent_surface: CantorPrefixRegion
    liveness_ok: CantorPrefixRegion
    budget_blocked: CantorPrefixRegion
    invalid: CantorPrefixRegion
    returned_success: CantorPrefixRegion
    explicit_failure: CantorPrefixRegion

    def partition_is_total(self) -> bool:
        return partition_ok((self.liveness_ok, self.budget_blocked, self.invalid))


_ALL_WORDS: tuple[AdaptiveLivenessWord, ...] = tuple(
    tuple(int(bit) for bit in bits) for bits in product((0, 1), repeat=14)
)


def _region_from_words(words: Iterable[AdaptiveLivenessWord]) -> CantorPrefixRegion:
    return CantorPrefixRegion(tuple(tuple(int(bit) for bit in word) for word in words))


def budget_facts_ok(inputs: ExactOutManyPoolAdaptiveLivenessInputs) -> bool:
    return (
        inputs.selected_domain_budget_respected
        and inputs.repaired_selection_budget_respected
        and inputs.full_domain_pool_budget_respected
        and inputs.full_domain_candidate_budget_respected
        and inputs.budget_parameters_bound
    )


def attempt_order_ok(inputs: ExactOutManyPoolAdaptiveLivenessInputs) -> bool:
    return (
        inputs.cheap_path_attempted
        and (inputs.fallback_required == (not inputs.cheap_path_success))
        and (inputs.fallback_attempted == inputs.fallback_required)
    )


def outcome_total(inputs: ExactOutManyPoolAdaptiveLivenessInputs) -> bool:
    return inputs.returned_success != inputs.explicit_failure


def success_replayable(inputs: ExactOutManyPoolAdaptiveLivenessInputs) -> bool:
    return (not inputs.returned_success) or inputs.effective_quote_present


def failure_total(inputs: ExactOutManyPoolAdaptiveLivenessInputs) -> bool:
    return (not inputs.explicit_failure) or inputs.failure_reason_present


def no_spurious_failure(inputs: ExactOutManyPoolAdaptiveLivenessInputs) -> bool:
    return (not inputs.explicit_failure) or (not inputs.fallback_available)


def exact_out_many_pool_adaptive_liveness_ok(inputs: ExactOutManyPoolAdaptiveLivenessInputs) -> bool:
    return (
        budget_facts_ok(inputs)
        and attempt_order_ok(inputs)
        and outcome_total(inputs)
        and success_replayable(inputs)
        and failure_total(inputs)
        and no_spurious_failure(inputs)
    )


def coherent_surface(inputs: ExactOutManyPoolAdaptiveLivenessInputs) -> bool:
    return (
        attempt_order_ok(inputs)
        and outcome_total(inputs)
        and success_replayable(inputs)
        and failure_total(inputs)
        and no_spurious_failure(inputs)
    )


def input_region(inputs: ExactOutManyPoolAdaptiveLivenessInputs) -> CantorPrefixRegion:
    return CantorPrefixRegion.from_prefix(inputs.to_word())


def packet_input_region(packet: ExactOutManyPoolAdaptiveLivenessPacket) -> CantorPrefixRegion:
    return input_region(ExactOutManyPoolAdaptiveLivenessInputs.from_packet(packet))


def build_exact_out_many_pool_adaptive_liveness_regions() -> ExactOutManyPoolAdaptiveLivenessRegions:
    budget_facts_ok_region = _region_from_words(
        word for word in _ALL_WORDS if budget_facts_ok(ExactOutManyPoolAdaptiveLivenessInputs.from_word(word))
    )
    attempt_order_ok_region = _region_from_words(
        word for word in _ALL_WORDS if attempt_order_ok(ExactOutManyPoolAdaptiveLivenessInputs.from_word(word))
    )
    outcome_total_region = _region_from_words(
        word for word in _ALL_WORDS if outcome_total(ExactOutManyPoolAdaptiveLivenessInputs.from_word(word))
    )
    success_replayable_region = _region_from_words(
        word for word in _ALL_WORDS if success_replayable(ExactOutManyPoolAdaptiveLivenessInputs.from_word(word))
    )
    failure_total_region = _region_from_words(
        word for word in _ALL_WORDS if failure_total(ExactOutManyPoolAdaptiveLivenessInputs.from_word(word))
    )
    no_spurious_failure_region = _region_from_words(
        word for word in _ALL_WORDS if no_spurious_failure(ExactOutManyPoolAdaptiveLivenessInputs.from_word(word))
    )
    coherent_surface_region = _region_from_words(
        word for word in _ALL_WORDS if coherent_surface(ExactOutManyPoolAdaptiveLivenessInputs.from_word(word))
    )
    liveness_ok_region = _region_from_words(
        word
        for word in _ALL_WORDS
        if exact_out_many_pool_adaptive_liveness_ok(ExactOutManyPoolAdaptiveLivenessInputs.from_word(word))
    )
    budget_blocked_region = coherent_surface_region & ~budget_facts_ok_region
    invalid_region = ~coherent_surface_region
    returned_success_region = _region_from_words(
        word for word in _ALL_WORDS if ExactOutManyPoolAdaptiveLivenessInputs.from_word(word).returned_success
    )
    explicit_failure_region = _region_from_words(
        word for word in _ALL_WORDS if ExactOutManyPoolAdaptiveLivenessInputs.from_word(word).explicit_failure
    )
    return ExactOutManyPoolAdaptiveLivenessRegions(
        budget_facts_ok=budget_facts_ok_region,
        attempt_order_ok=attempt_order_ok_region,
        outcome_total=outcome_total_region,
        success_replayable=success_replayable_region,
        failure_total=failure_total_region,
        no_spurious_failure=no_spurious_failure_region,
        coherent_surface=coherent_surface_region,
        liveness_ok=liveness_ok_region,
        budget_blocked=budget_blocked_region,
        invalid=invalid_region,
        returned_success=returned_success_region,
        explicit_failure=explicit_failure_region,
    )
