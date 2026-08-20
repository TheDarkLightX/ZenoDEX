"""Owned types and closed registries for the research-only V2 delta checker."""

from __future__ import annotations

import re
from dataclasses import dataclass
from enum import Enum
from typing import Final, Mapping, TypeAlias

SCHEMA_V2: Final = "zenodex/global-economic-delta-plan/v2"
ROOT_DOMAIN_V2: Final = b"zenodex:global-economic-delta-plan:v2\0"
I128_MAX: Final = (1 << 127) - 1
MAX_EVENTS_V2: Final = 64
MAX_SOURCE_BINDINGS_V2: Final = 64
MAX_INPUT_BYTES_V2: Final = 1_048_576
_ROOT_RE: Final = re.compile(r"sha256:[0-9a-f]{64}\Z")
_ID_RE: Final = re.compile(r"[a-z0-9][a-z0-9._:-]{0,127}\Z")

ScalarV2: TypeAlias = str | int
OwnedEventV2: TypeAlias = Mapping[str, ScalarV2]


class DeltaRejectCodeV2(str, Enum):
    PLAN_TYPE_INVALID = "PLAN_TYPE_INVALID"
    PLAN_FIELDS_INVALID = "PLAN_FIELDS_INVALID"
    SCHEMA_MISMATCH = "SCHEMA_MISMATCH"
    SCHEMA_TYPE_INVALID = "SCHEMA_TYPE_INVALID"
    DECODE_INVALID = "DECODE_INVALID"
    INPUT_TOO_LARGE = "INPUT_TOO_LARGE"
    EVENTS_TYPE_INVALID = "EVENTS_TYPE_INVALID"
    EMPTY_PLAN = "EMPTY_PLAN"
    EVENT_COUNT_OUT_OF_RANGE = "EVENT_COUNT_OUT_OF_RANGE"
    EVENT_TYPE_INVALID = "EVENT_TYPE_INVALID"
    EVENT_FIELDS_INVALID = "EVENT_FIELDS_INVALID"
    DELTA_CLASS_INVALID = "DELTA_CLASS_INVALID"
    IDENTIFIER_INVALID = "IDENTIFIER_INVALID"
    ROOT_INVALID = "ROOT_INVALID"
    AMOUNT_TYPE_INVALID = "AMOUNT_TYPE_INVALID"
    AMOUNT_OUT_OF_RANGE = "AMOUNT_OUT_OF_RANGE"
    SOURCE_EQUALS_DESTINATION = "SOURCE_EQUALS_DESTINATION"
    LIABILITY_RELATION_INVALID = "LIABILITY_RELATION_INVALID"
    SLASH_PARTITION_MISMATCH = "SLASH_PARTITION_MISMATCH"
    SELF_REFERENTIAL_EVENT = "SELF_REFERENTIAL_EVENT"
    DUPLICATE_EVENT = "DUPLICATE_EVENT"
    NONCANONICAL_EVENT_ORDER = "NONCANONICAL_EVENT_ORDER"
    SOURCE_BINDING_COUNT_OUT_OF_RANGE = "SOURCE_BINDING_COUNT_OUT_OF_RANGE"
    SOURCE_REFERENCE_INVALID = "SOURCE_REFERENCE_INVALID"
    SOURCE_REFERENCE_REUSED = "SOURCE_REFERENCE_REUSED"
    SOURCE_BINDING_UNUSED = "SOURCE_BINDING_UNUSED"
    REFERENCE_ROOT_CONFLICT = "REFERENCE_ROOT_CONFLICT"
    NONCANONICAL_SOURCE_ORDER = "NONCANONICAL_SOURCE_ORDER"
    SOURCE_KIND_INVALID = "SOURCE_KIND_INVALID"
    DIRECTION_INVALID = "DIRECTION_INVALID"


class ZeroPolicyV2(Enum):
    FORBID = "FORBID"
    ALLOW = "ALLOW"


class DeltaValidationErrorV2(ValueError):
    """Typed no-candidate rejection from the independent V2 checker."""

    def __init__(self, code: DeltaRejectCodeV2, detail: str) -> None:
        super().__init__(f"{code.value}: {detail}")
        self.code = code


@dataclass(frozen=True, slots=True)
class _StructuralDeltaPlanDataV2:
    """Defensively owned canonical plan without runtime authority."""

    events: tuple[OwnedEventV2, ...]
    source_bindings: tuple[OwnedEventV2, ...]
    canonical_bytes: bytes
    root: str


_COMMON_FIELDS: Final = frozenset(
    {"delta_class", "economic_event", "asset", "amount_atoms"}
)
_VARIANT_FIELDS: Final[dict[str, frozenset[str]]] = {
    "internal_transfer": _COMMON_FIELDS
    | {
        "source_owner",
        "destination_owner",
        "source_ledger_allocation",
        "destination_ledger_allocation",
    },
    "mint": _COMMON_FIELDS
    | {"issuer_authority", "recipient_owner", "recipient_ledger_allocation"},
    "burn": _COMMON_FIELDS
    | {"burn_authority", "source_owner", "source_ledger_allocation"},
    "liability": _COMMON_FIELDS
    | {"liability_owner", "liability_kind", "direction", "pre_atoms", "post_atoms"},
    "external_in": _COMMON_FIELDS
    | {"source_effect", "destination_owner", "destination_ledger_allocation"},
    "external_out": _COMMON_FIELDS
    | {
        "source_owner",
        "source_ledger_allocation",
        "ancestor_claim_event",
        "destination_effect",
    },
    "refund": _COMMON_FIELDS
    | {
        "source_event",
        "source_owner",
        "source_ledger_allocation",
        "refund_owner",
        "refund_ledger_allocation",
    },
    "slash": _COMMON_FIELDS
    | {
        "slashing_authority",
        "slashed_owner",
        "source_ledger_allocation",
        "beneficiary_owner",
        "beneficiary_ledger_allocation",
        "beneficiary_atoms",
        "residue_owner",
        "residue_ledger_allocation",
        "residue_atoms",
    },
}
_SOURCE_BINDING_FIELDS: Final = frozenset(
    {"source_root", "source_kind", "asset", "amount_atoms"}
)
_SOURCE_KINDS: Final = frozenset(
    {"external_effect", "ancestor_claim", "refundable_event"}
)
_SOURCE_EXPECTATIONS: Final = {
    "external_in": ("source_effect", "external_effect"),
    "external_out": ("ancestor_claim_event", "ancestor_claim"),
    "refund": ("source_event", "refundable_event"),
}
_ROOT_FIELDS: Final = frozenset(
    {
        "economic_event",
        "source_effect",
        "destination_effect",
        "ancestor_claim_event",
        "source_event",
    }
)
_AMOUNT_FIELDS: Final = frozenset(
    {"amount_atoms", "pre_atoms", "post_atoms", "beneficiary_atoms", "residue_atoms"}
)
_ROOT_FIELD_ORDER: Final = (
    "economic_event",
    "source_effect",
    "ancestor_claim_event",
    "destination_effect",
    "source_event",
)
_AMOUNT_FIELD_ORDER: Final = (
    "amount_atoms",
    "pre_atoms",
    "post_atoms",
    "beneficiary_atoms",
    "residue_atoms",
)
