from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable

from .cantor_prefix_algebra import CantorPrefixRegion, partition_ok


ResourceAdmissionWord = tuple[int, int, int, int, int, int, int, int, int, int, int, int]


@dataclass(frozen=True)
class ResourceLoadSheddingRegretGuardInputs:
    resource_admission_ok: bool
    artifact_binding_ok: bool
    user_regret_ok: bool
    user_impact_ok: bool
    quote_fresh_ok: bool
    route_cert_ok: bool
    require_route_cert: bool
    load_shedding_mode: bool
    emergency_override_ok: bool
    strict_regret_mode: bool
    proof_ok: bool
    binding_ok: bool

    def to_word(self) -> ResourceAdmissionWord:
        return (
            int(bool(self.resource_admission_ok)),
            int(bool(self.artifact_binding_ok)),
            int(bool(self.user_regret_ok)),
            int(bool(self.user_impact_ok)),
            int(bool(self.quote_fresh_ok)),
            int(bool(self.route_cert_ok)),
            int(bool(self.require_route_cert)),
            int(bool(self.load_shedding_mode)),
            int(bool(self.emergency_override_ok)),
            int(bool(self.strict_regret_mode)),
            int(bool(self.proof_ok)),
            int(bool(self.binding_ok)),
        )

    @classmethod
    def from_word(cls, word: Iterable[int | bool]) -> "ResourceLoadSheddingRegretGuardInputs":
        bits = tuple(int(bool(bit)) for bit in word)
        if len(bits) != 12:
            raise ValueError("resource load shedding regret guard words must have exactly 12 bits")
        return cls(
            resource_admission_ok=bool(bits[0]),
            artifact_binding_ok=bool(bits[1]),
            user_regret_ok=bool(bits[2]),
            user_impact_ok=bool(bits[3]),
            quote_fresh_ok=bool(bits[4]),
            route_cert_ok=bool(bits[5]),
            require_route_cert=bool(bits[6]),
            load_shedding_mode=bool(bits[7]),
            emergency_override_ok=bool(bits[8]),
            strict_regret_mode=bool(bits[9]),
            proof_ok=bool(bits[10]),
            binding_ok=bool(bits[11]),
        )


@dataclass(frozen=True)
class ResourceLoadSheddingRegretGuardRegions:
    user_safety_ok: CantorPrefixRegion
    certs_ok: CantorPrefixRegion
    normal_path_ok: CantorPrefixRegion
    shed_path_ok: CantorPrefixRegion
    final_admission_ok: CantorPrefixRegion
    proof_gated_final_admission_ok: CantorPrefixRegion
    normal_only: CantorPrefixRegion
    shed_only: CantorPrefixRegion
    admitted_without_proof: CantorPrefixRegion
    denied: CantorPrefixRegion

    def partition_is_total(self) -> bool:
        return partition_ok((self.proof_gated_final_admission_ok, self.admitted_without_proof, self.denied))


_ALL_WORDS: tuple[ResourceAdmissionWord, ...] = tuple(
    tuple(int(bit) for bit in bits) for bits in product((0, 1), repeat=12)
)


def _region_from_words(words: Iterable[ResourceAdmissionWord]) -> CantorPrefixRegion:
    return CantorPrefixRegion(tuple(tuple(int(bit) for bit in word) for word in words))


def optional_req(required: bool, observed_ok: bool) -> bool:
    return (not required) or observed_ok


def user_safety_ok(inputs: ResourceLoadSheddingRegretGuardInputs) -> bool:
    return inputs.user_regret_ok and inputs.user_impact_ok and inputs.quote_fresh_ok


def certs_ok(inputs: ResourceLoadSheddingRegretGuardInputs) -> bool:
    return optional_req(inputs.require_route_cert, inputs.route_cert_ok)


def normal_path_ok(inputs: ResourceLoadSheddingRegretGuardInputs) -> bool:
    return (
        (not inputs.load_shedding_mode)
        and inputs.resource_admission_ok
        and inputs.artifact_binding_ok
        and user_safety_ok(inputs)
        and certs_ok(inputs)
    )


def shed_path_ok(inputs: ResourceLoadSheddingRegretGuardInputs) -> bool:
    return (
        inputs.load_shedding_mode
        and inputs.emergency_override_ok
        and inputs.artifact_binding_ok
        and certs_ok(inputs)
        and ((not inputs.strict_regret_mode) or user_safety_ok(inputs))
    )


def final_admission_ok(inputs: ResourceLoadSheddingRegretGuardInputs) -> bool:
    return normal_path_ok(inputs) or shed_path_ok(inputs)


def proof_gated_final_admission_ok(inputs: ResourceLoadSheddingRegretGuardInputs) -> bool:
    return final_admission_ok(inputs) and inputs.proof_ok and inputs.binding_ok


def input_region(inputs: ResourceLoadSheddingRegretGuardInputs) -> CantorPrefixRegion:
    return CantorPrefixRegion.from_prefix(inputs.to_word())


def build_resource_load_shedding_regret_guard_regions() -> ResourceLoadSheddingRegretGuardRegions:
    user_safety_region = _region_from_words(
        word for word in _ALL_WORDS if user_safety_ok(ResourceLoadSheddingRegretGuardInputs.from_word(word))
    )
    certs_region = _region_from_words(
        word for word in _ALL_WORDS if certs_ok(ResourceLoadSheddingRegretGuardInputs.from_word(word))
    )
    normal_path_region = _region_from_words(
        word for word in _ALL_WORDS if normal_path_ok(ResourceLoadSheddingRegretGuardInputs.from_word(word))
    )
    shed_path_region = _region_from_words(
        word for word in _ALL_WORDS if shed_path_ok(ResourceLoadSheddingRegretGuardInputs.from_word(word))
    )
    final_admission_region = _region_from_words(
        word for word in _ALL_WORDS if final_admission_ok(ResourceLoadSheddingRegretGuardInputs.from_word(word))
    )
    proof_gated_region = _region_from_words(
        word for word in _ALL_WORDS if proof_gated_final_admission_ok(ResourceLoadSheddingRegretGuardInputs.from_word(word))
    )
    normal_only_region = normal_path_region & ~shed_path_region
    shed_only_region = shed_path_region & ~normal_path_region
    admitted_without_proof_region = final_admission_region & ~proof_gated_region
    denied_region = ~final_admission_region
    return ResourceLoadSheddingRegretGuardRegions(
        user_safety_ok=user_safety_region,
        certs_ok=certs_region,
        normal_path_ok=normal_path_region,
        shed_path_ok=shed_path_region,
        final_admission_ok=final_admission_region,
        proof_gated_final_admission_ok=proof_gated_region,
        normal_only=normal_only_region,
        shed_only=shed_only_region,
        admitted_without_proof=admitted_without_proof_region,
        denied=denied_region,
    )
