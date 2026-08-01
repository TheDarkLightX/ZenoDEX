"""Closed immutable outbox values for an FCIS atomic commit bundle.

The outbox plan is committed as data. External delivery remains an idempotent
imperative-shell obligation. Production builders derive every record and key
from one committable decision; caller-supplied plans carry no authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import final

from ..state.owned_collections import OwnedEnumV1, OwnedMapV1
from ..state.owned_json import (
    OWNED_JSON_OBJECT_MAP_SCHEMA_ID_V1,
    OwnedJsonObjectV1,
)

FCIS_OUTBOX_PLAN_SCHEMA_ID_V1 = "zenodex/fcis/outbox-plan/v1"
MAX_FCIS_OUTBOX_RECORDS_V1 = 4_096


class OutboxEffectKindV1(Enum):
    """Closed delivery-obligation kinds for the FCIS spot profile."""

    CANONICAL_EVENT = "canonical_event"
    PROOF_REQUEST = "proof_request"
    INDEX_REFRESH = "index_refresh"


@final
@dataclass(frozen=True, slots=True)
class OutboxRecordSourceV1:
    effect_index: object
    effect_kind: object
    effect_identity: object
    payload: object
    idempotency_key: object


@final
@dataclass(frozen=True, slots=True)
class OutboxPlanSourceV1:
    records: object
    authority_normal_form_root: object = None


def _is_digest_v1(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 66
        and value.startswith("0x")
        and all(character in "0123456789abcdef" for character in value[2:])
    )


@final
@dataclass(frozen=True, slots=True)
class OutboxRecordV1:
    """One receipt-bound delivery obligation in canonical effect order."""

    effect_index: int
    effect_kind: OwnedEnumV1
    effect_identity: str
    payload: OwnedJsonObjectV1
    idempotency_key: str

    def __post_init__(self) -> None:
        if (
            type(self.effect_index) is not int
            or not 0 <= self.effect_index < MAX_FCIS_OUTBOX_RECORDS_V1
        ):
            raise TypeError("outbox effect_index must be an exact bounded int")
        if type(self.effect_kind) is not OwnedEnumV1:
            raise TypeError("outbox effect_kind must be an exact owned enum")
        if not _is_digest_v1(self.effect_identity):
            raise TypeError("outbox effect_identity must be a canonical digest")
        if type(self.payload) is not OwnedMapV1:
            raise TypeError("outbox payload must be an exact owned JSON object")
        if self.payload.schema_id != OWNED_JSON_OBJECT_MAP_SCHEMA_ID_V1:
            raise ValueError("outbox payload must use the JSON-object schema")
        if not _is_digest_v1(self.idempotency_key):
            raise TypeError("outbox idempotency_key must be a canonical digest")


@final
@dataclass(frozen=True, slots=True)
class OutboxPlanV1:
    """Canonical, duplicate-free outbox claim data carrying no delivery authority."""

    records: tuple[OutboxRecordV1, ...]
    authority_normal_form_root: str | None = None

    def __post_init__(self) -> None:
        if type(self.records) is not tuple or any(
            type(record) is not OutboxRecordV1 for record in self.records
        ):
            raise TypeError("outbox records must be an exact owned tuple")
        if len(self.records) > MAX_FCIS_OUTBOX_RECORDS_V1:
            raise ValueError("outbox record limit exceeded")
        indices = tuple(record.effect_index for record in self.records)
        if indices != tuple(range(len(self.records))):
            raise ValueError("outbox effect indices must be contiguous protocol order")
        identities = tuple(record.effect_identity for record in self.records)
        if len(identities) != len(set(identities)):
            raise ValueError("outbox effect identities must be unique")
        keys = tuple(record.idempotency_key for record in self.records)
        if len(keys) != len(set(keys)):
            raise ValueError("outbox idempotency keys must be unique")
        if self.authority_normal_form_root is not None and not _is_digest_v1(
            self.authority_normal_form_root
        ):
            raise TypeError("outbox ANF root must be a canonical digest or None")


__all__ = (
    "FCIS_OUTBOX_PLAN_SCHEMA_ID_V1",
    "MAX_FCIS_OUTBOX_RECORDS_V1",
    "OutboxEffectKindV1",
    "OutboxPlanSourceV1",
    "OutboxPlanV1",
    "OutboxRecordSourceV1",
    "OutboxRecordV1",
)
