from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from src.fire.compiler.compiler_registry_v1 import get_fire_compiler_entry
from src.fire.compiler.fmos_file_v1 import bind_fire_math_object_spec_file
from src.fire.compiler.fmos_v1 import FireMathObjectSpec, verify_fmos_composition
from src.fire.pathing_v1 import resolve_fire_spec_path
from src.fire.runtime.common_v1 import require_bounded_int


INDEX_MAX = 1_000


@dataclass(frozen=True)
class BurnIndexTerms:
    burn_final: int

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "burn_final",
            require_bounded_int("burn_final", self.burn_final, minimum=0, maximum=INDEX_MAX),
        )


@dataclass(frozen=True)
class FeeIndexTerms:
    fee_final: int

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "fee_final",
            require_bounded_int("fee_final", self.fee_final, minimum=0, maximum=INDEX_MAX),
        )


@dataclass(frozen=True)
class RewardIndexTerms:
    reward_final: int

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "reward_final",
            require_bounded_int("reward_final", self.reward_final, minimum=0, maximum=INDEX_MAX),
        )


@dataclass(frozen=True)
class HODLValueTerms:
    hodl_lower: int
    hodl_upper: int

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "hodl_lower",
            require_bounded_int("hodl_lower", self.hodl_lower, minimum=0, maximum=INDEX_MAX),
        )
        object.__setattr__(
            self,
            "hodl_upper",
            require_bounded_int("hodl_upper", self.hodl_upper, minimum=0, maximum=INDEX_MAX),
        )
        if self.hodl_lower > self.hodl_upper:
            raise ValueError("hodl interval out of order")


@dataclass(frozen=True)
class LPValueTerms:
    lpv_lower: int
    lpv_upper: int

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "lpv_lower",
            require_bounded_int("lpv_lower", self.lpv_lower, minimum=0, maximum=INDEX_MAX),
        )
        object.__setattr__(
            self,
            "lpv_upper",
            require_bounded_int("lpv_upper", self.lpv_upper, minimum=0, maximum=INDEX_MAX),
        )
        if self.lpv_lower > self.lpv_upper:
            raise ValueError("lpv interval out of order")


def _bind_interface_spec(spec_name: str, terms_type: type) -> FireMathObjectSpec:
    return bind_fire_math_object_spec_file(
        resolve_fire_spec_path(spec_name),
        terms_type=terms_type,
        artifact_type=object,
        compile_state=lambda _: None,
        compiled_state_from_artifact=lambda _: None,
    )


BURN_INDEX_SPEC = _bind_interface_spec("burn_index_v1.json", BurnIndexTerms)
FEE_INDEX_SPEC = _bind_interface_spec("fee_index_v1.json", FeeIndexTerms)
REWARD_INDEX_SPEC = _bind_interface_spec("reward_index_v1.json", RewardIndexTerms)
HODL_VALUE_SPEC = _bind_interface_spec("hodl_value_v1.json", HODLValueTerms)
LP_VALUE_SPEC = _bind_interface_spec("lp_value_v1.json", LPValueTerms)


FIRE_INTERFACE_SPECS: tuple[FireMathObjectSpec, ...] = (
    BURN_INDEX_SPEC,
    FEE_INDEX_SPEC,
    REWARD_INDEX_SPEC,
    HODL_VALUE_SPEC,
    LP_VALUE_SPEC,
)


_FIRE_INTERFACE_SPEC_MAP = {spec.object_id: spec for spec in FIRE_INTERFACE_SPECS}


def list_fire_interface_entries() -> tuple[FireMathObjectSpec, ...]:
    return FIRE_INTERFACE_SPECS


def get_fire_interface_entry(object_id: str) -> FireMathObjectSpec:
    if object_id not in _FIRE_INTERFACE_SPEC_MAP:
        raise KeyError(f"unsupported FIRE interface object_id: {object_id}")
    return _FIRE_INTERFACE_SPEC_MAP[object_id]


def build_fire_interface_terms(object_id: str, raw_terms: Mapping[str, object]) -> Any:
    return get_fire_interface_entry(object_id).build_terms(raw_terms)


def verify_fire_interface_to_object_composition(
    *,
    interface_object_id: str,
    interface_raw_terms: Mapping[str, object],
    consumer_object_id: str,
    consumer_raw_terms: Mapping[str, object],
    bindings: Mapping[str, str],
) -> tuple[bool, str | None]:
    producer_spec = get_fire_interface_entry(interface_object_id)
    producer_terms = producer_spec.build_terms(interface_raw_terms)
    consumer_spec = get_fire_compiler_entry(consumer_object_id)
    consumer_terms = consumer_spec.build_terms(consumer_raw_terms)
    return verify_fmos_composition(
        producer_spec=producer_spec,
        producer_terms=producer_terms,
        consumer_spec=consumer_spec,
        consumer_terms=consumer_terms,
        bindings=bindings,
    )


__all__ = [
    "BURN_INDEX_SPEC",
    "BurnIndexTerms",
    "FEE_INDEX_SPEC",
    "FIRE_INTERFACE_SPECS",
    "FeeIndexTerms",
    "REWARD_INDEX_SPEC",
    "RewardIndexTerms",
    "build_fire_interface_terms",
    "get_fire_interface_entry",
    "HODL_VALUE_SPEC",
    "HODLValueTerms",
    "LP_VALUE_SPEC",
    "LPValueTerms",
    "list_fire_interface_entries",
    "verify_fire_interface_to_object_composition",
]
