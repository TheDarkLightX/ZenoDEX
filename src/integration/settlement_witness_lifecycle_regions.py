from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable

from .cantor_prefix_algebra import CantorPrefixRegion, partition_ok
from .settlement_witness_lifecycle import SettlementWitnessLifecyclePacket


LifecycleWord = tuple[int, int, int, int, int, int, int]


@dataclass(frozen=True)
class SettlementWitnessLifecycleInputs:
    witness_present: bool
    witness_valid: bool
    before_expiry: bool
    end_to_end_packet_ok: bool
    settled: bool
    rejected_with_reason: bool
    rejection_reason_present: bool

    def to_word(self) -> LifecycleWord:
        return (
            int(bool(self.witness_present)),
            int(bool(self.witness_valid)),
            int(bool(self.before_expiry)),
            int(bool(self.end_to_end_packet_ok)),
            int(bool(self.settled)),
            int(bool(self.rejected_with_reason)),
            int(bool(self.rejection_reason_present)),
        )

    @classmethod
    def from_word(cls, word: Iterable[int | bool]) -> "SettlementWitnessLifecycleInputs":
        bits = tuple(int(bool(bit)) for bit in word)
        if len(bits) != 7:
            raise ValueError("settlement witness lifecycle words must have exactly 7 bits")
        return cls(
            witness_present=bool(bits[0]),
            witness_valid=bool(bits[1]),
            before_expiry=bool(bits[2]),
            end_to_end_packet_ok=bool(bits[3]),
            settled=bool(bits[4]),
            rejected_with_reason=bool(bits[5]),
            rejection_reason_present=bool(bits[6]),
        )

    @classmethod
    def from_packet(cls, packet: SettlementWitnessLifecyclePacket) -> "SettlementWitnessLifecycleInputs":
        return cls(
            witness_present=bool(packet.witness_present),
            witness_valid=bool(packet.witness_valid),
            before_expiry=bool(packet.before_expiry),
            end_to_end_packet_ok=bool(packet.end_to_end_packet_ok),
            settled=bool(packet.settled),
            rejected_with_reason=bool(packet.rejected_with_reason),
            rejection_reason_present=bool(packet.rejection_reason_present),
        )


@dataclass(frozen=True)
class SettlementWitnessLifecycleRegions:
    outcome_total: CantorPrefixRegion
    witness_coherent: CantorPrefixRegion
    settled_requires_witness: CantorPrefixRegion
    rejection_total: CantorPrefixRegion
    lifecycle_progress: CantorPrefixRegion
    lifecycle_ok: CantorPrefixRegion
    accepted: CantorPrefixRegion
    rejected: CantorPrefixRegion
    invalid: CantorPrefixRegion

    def partition_is_total(self) -> bool:
        return partition_ok((self.accepted, self.rejected, self.invalid))


_ALL_WORDS: tuple[LifecycleWord, ...] = tuple(
    tuple(int(bit) for bit in bits) for bits in product((0, 1), repeat=7)
)


def _region_from_words(words: Iterable[LifecycleWord]) -> CantorPrefixRegion:
    return CantorPrefixRegion(tuple(tuple(int(bit) for bit in word) for word in words))


def outcome_total(inputs: SettlementWitnessLifecycleInputs) -> bool:
    return bool(inputs.settled) != bool(inputs.rejected_with_reason)


def witness_coherent(inputs: SettlementWitnessLifecycleInputs) -> bool:
    return (not inputs.witness_valid) or inputs.witness_present


def settled_requires_witness(inputs: SettlementWitnessLifecycleInputs) -> bool:
    return (not inputs.settled) or (inputs.witness_valid and inputs.end_to_end_packet_ok)


def rejection_total(inputs: SettlementWitnessLifecycleInputs) -> bool:
    return (not inputs.rejected_with_reason) or inputs.rejection_reason_present


def lifecycle_progress(inputs: SettlementWitnessLifecycleInputs) -> bool:
    return (
        (not inputs.witness_valid)
        or (not inputs.before_expiry)
        or inputs.settled
        or inputs.rejected_with_reason
    )


def settlement_witness_lifecycle_ok(inputs: SettlementWitnessLifecycleInputs) -> bool:
    return (
        outcome_total(inputs)
        and witness_coherent(inputs)
        and settled_requires_witness(inputs)
        and rejection_total(inputs)
        and lifecycle_progress(inputs)
    )


def input_region(inputs: SettlementWitnessLifecycleInputs) -> CantorPrefixRegion:
    return CantorPrefixRegion.from_prefix(inputs.to_word())


def packet_input_region(packet: SettlementWitnessLifecyclePacket) -> CantorPrefixRegion:
    return input_region(SettlementWitnessLifecycleInputs.from_packet(packet))


def build_settlement_witness_lifecycle_regions() -> SettlementWitnessLifecycleRegions:
    outcome_total_region = _region_from_words(
        word for word in _ALL_WORDS if outcome_total(SettlementWitnessLifecycleInputs.from_word(word))
    )
    witness_coherent_region = _region_from_words(
        word for word in _ALL_WORDS if witness_coherent(SettlementWitnessLifecycleInputs.from_word(word))
    )
    settled_requires_witness_region = _region_from_words(
        word for word in _ALL_WORDS if settled_requires_witness(SettlementWitnessLifecycleInputs.from_word(word))
    )
    rejection_total_region = _region_from_words(
        word for word in _ALL_WORDS if rejection_total(SettlementWitnessLifecycleInputs.from_word(word))
    )
    lifecycle_progress_region = _region_from_words(
        word for word in _ALL_WORDS if lifecycle_progress(SettlementWitnessLifecycleInputs.from_word(word))
    )
    lifecycle_ok_region = _region_from_words(
        word for word in _ALL_WORDS if settlement_witness_lifecycle_ok(SettlementWitnessLifecycleInputs.from_word(word))
    )
    accepted_region = _region_from_words(
        word
        for word in _ALL_WORDS
        if settlement_witness_lifecycle_ok(SettlementWitnessLifecycleInputs.from_word(word)) and bool(word[4])
    )
    rejected_region = _region_from_words(
        word
        for word in _ALL_WORDS
        if settlement_witness_lifecycle_ok(SettlementWitnessLifecycleInputs.from_word(word)) and bool(word[5])
    )
    invalid_region = ~lifecycle_ok_region
    return SettlementWitnessLifecycleRegions(
        outcome_total=outcome_total_region,
        witness_coherent=witness_coherent_region,
        settled_requires_witness=settled_requires_witness_region,
        rejection_total=rejection_total_region,
        lifecycle_progress=lifecycle_progress_region,
        lifecycle_ok=lifecycle_ok_region,
        accepted=accepted_region,
        rejected=rejected_region,
        invalid=invalid_region,
    )
