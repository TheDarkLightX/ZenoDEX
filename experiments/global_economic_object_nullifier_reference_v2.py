"""Bounded, research-only oracle for single-use economic object semantics.

This module has no settlement, proof, publication, persistence, release, or
runtime authority. Its digest is a differential-testing reference and is not a
GlobalSettlementABI commitment.
"""

from __future__ import annotations

import dataclasses
import hashlib
import json
import re
from enum import Enum
from typing import TypeAlias

REFERENCE_SCHEMA_V2 = "zenodex/global-economic-object-nullifier-reference/v2"
REFERENCE_DIGEST_DOMAIN_V2 = b"global-economic-object-nullifier-reference"
REFERENCE_DIGEST_PREFIX_V2 = REFERENCE_DIGEST_DOMAIN_V2 + b"\x00" + b"2\x00"
MAX_REFERENCE_NULLIFIERS_V2 = 4_096
MAX_REFERENCE_CLAIMS_PER_STEP_V2 = 64
MAX_REFERENCE_ARCHIVE_BYTES_V2 = 1_048_576

_CANONICAL_ID_RE = re.compile(r"0x[0-9a-f]{64}")
_ZERO_ID_V2 = "0x" + "0" * 64


def _validate_reference_id_v2(value: object, *, field_name: str) -> None:
    if type(value) is not str:
        raise TypeError(f"{field_name} must be an exact str")
    if _CANONICAL_ID_RE.fullmatch(value) is None:
        raise ValueError(
            f"{field_name} must be lowercase 0x-prefixed 32-byte hexadecimal"
        )
    if value == _ZERO_ID_V2:
        raise ValueError(f"{field_name} must be nonzero")


@dataclasses.dataclass(frozen=True, slots=True)
class ReferenceObjectIdV2:
    """Opaque, already-derived logical object identifier."""

    value: str

    def __post_init__(self) -> None:
        _validate_reference_id_v2(self.value, field_name="object_id")

    @property
    def decoded_bytes(self) -> bytes:
        return bytes.fromhex(self.value[2:])


@dataclasses.dataclass(frozen=True, slots=True)
class ReferenceOccurrenceIdV2:
    """Opaque, already-derived first-consumption occurrence identifier."""

    value: str

    def __post_init__(self) -> None:
        _validate_reference_id_v2(self.value, field_name="occurrence_id")


@dataclasses.dataclass(frozen=True, slots=True)
class ReferenceConsumptionClaimV2:
    object_id: ReferenceObjectIdV2
    consumed_by_occurrence_id: ReferenceOccurrenceIdV2

    def __post_init__(self) -> None:
        if type(self.object_id) is not ReferenceObjectIdV2:
            raise TypeError("object_id must be ReferenceObjectIdV2")
        if type(self.consumed_by_occurrence_id) is not ReferenceOccurrenceIdV2:
            raise TypeError(
                "consumed_by_occurrence_id must be ReferenceOccurrenceIdV2"
            )


@dataclasses.dataclass(frozen=True, slots=True)
class ReferenceNullifierEntryV2:
    object_id: ReferenceObjectIdV2
    first_consumed_by_occurrence_id: ReferenceOccurrenceIdV2

    def __post_init__(self) -> None:
        if type(self.object_id) is not ReferenceObjectIdV2:
            raise TypeError("object_id must be ReferenceObjectIdV2")
        if type(self.first_consumed_by_occurrence_id) is not ReferenceOccurrenceIdV2:
            raise TypeError(
                "first_consumed_by_occurrence_id must be ReferenceOccurrenceIdV2"
            )


def _canonical_archive_bytes_from_entries_v2(
    entries: tuple[ReferenceNullifierEntryV2, ...],
) -> bytes:
    payload = {
        "schema": REFERENCE_SCHEMA_V2,
        "entries": [
            {
                "object_id": entry.object_id.value,
                "first_consumed_by_occurrence_id": entry.first_consumed_by_occurrence_id.value,
            }
            for entry in entries
        ],
    }
    return json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


@dataclasses.dataclass(frozen=True, slots=True)
class CanonicalReferenceNullifierArchiveV2:
    """Bounded complete-disclosure archive used only as a semantic oracle."""

    entries: tuple[ReferenceNullifierEntryV2, ...] = ()

    def __post_init__(self) -> None:
        if type(self.entries) is not tuple:
            raise TypeError("entries must be an exact tuple")
        if len(self.entries) > MAX_REFERENCE_NULLIFIERS_V2:
            raise ValueError("reference archive exceeds entry capacity")
        if any(type(entry) is not ReferenceNullifierEntryV2 for entry in self.entries):
            raise TypeError("entries must contain exact ReferenceNullifierEntryV2 values")

        owned_entries = tuple(
            ReferenceNullifierEntryV2(
                object_id=ReferenceObjectIdV2(entry.object_id.value),
                first_consumed_by_occurrence_id=ReferenceOccurrenceIdV2(
                    entry.first_consumed_by_occurrence_id.value
                ),
            )
            for entry in self.entries
        )
        keys = tuple(entry.object_id.decoded_bytes for entry in owned_entries)
        if any(keys[index] >= keys[index + 1] for index in range(len(keys) - 1)):
            raise ValueError("reference archive entries must be strictly sorted and unique")
        if (
            len(_canonical_archive_bytes_from_entries_v2(owned_entries))
            > MAX_REFERENCE_ARCHIVE_BYTES_V2
        ):
            raise ValueError("reference archive exceeds canonical byte limit")
        object.__setattr__(self, "entries", owned_entries)

    @classmethod
    def empty(cls) -> CanonicalReferenceNullifierArchiveV2:
        return cls()


class ReferenceRejectCodeV2(str, Enum):
    REFERENCE_STEP_LIMIT_EXCEEDED = "REFERENCE_STEP_LIMIT_EXCEEDED"
    REFERENCE_DUPLICATE_IN_BATCH = "REFERENCE_DUPLICATE_IN_BATCH"
    REFERENCE_ALREADY_CONSUMED = "REFERENCE_ALREADY_CONSUMED"
    REFERENCE_ARCHIVE_CAPACITY_EXCEEDED = "REFERENCE_ARCHIVE_CAPACITY_EXCEEDED"
    REFERENCE_ARCHIVE_BYTE_LIMIT_EXCEEDED = (
        "REFERENCE_ARCHIVE_BYTE_LIMIT_EXCEEDED"
    )


def _validate_reference_digest_v2(value: object, *, field_name: str) -> None:
    if type(value) is not str or re.fullmatch(r"0x[0-9a-f]{64}", value) is None:
        raise ValueError(f"{field_name} must be lowercase 0x-prefixed SHA-256")


@dataclasses.dataclass(frozen=True, slots=True)
class ReferenceAcceptedV2:
    pre_reference_archive_digest: str
    post_archive: CanonicalReferenceNullifierArchiveV2

    def __post_init__(self) -> None:
        _validate_reference_digest_v2(
            self.pre_reference_archive_digest,
            field_name="pre_reference_archive_digest",
        )
        if type(self.post_archive) is not CanonicalReferenceNullifierArchiveV2:
            raise TypeError(
                "post_archive must be CanonicalReferenceNullifierArchiveV2"
            )

    @property
    def post_reference_archive_digest(self) -> str:
        return reference_archive_digest_v2(self.post_archive)


@dataclasses.dataclass(frozen=True, slots=True)
class ReferenceRejectedV2:
    code: ReferenceRejectCodeV2
    pre_reference_archive_digest: str
    diagnostic: str

    def __post_init__(self) -> None:
        if type(self.code) is not ReferenceRejectCodeV2:
            raise TypeError("code must be ReferenceRejectCodeV2")
        _validate_reference_digest_v2(
            self.pre_reference_archive_digest,
            field_name="pre_reference_archive_digest",
        )
        if type(self.diagnostic) is not str or not self.diagnostic:
            raise TypeError("diagnostic must be a non-empty exact str")


ReferenceResultV2: TypeAlias = ReferenceAcceptedV2 | ReferenceRejectedV2


def canonical_reference_archive_bytes_v2(
    archive: CanonicalReferenceNullifierArchiveV2,
) -> bytes:
    """Return exact bounded UTF-8 JSON for the research archive."""

    owned_archive = _snapshot_archive_v2(archive)
    return _canonical_archive_bytes_from_entries_v2(owned_archive.entries)


def reference_archive_digest_v2(
    archive: CanonicalReferenceNullifierArchiveV2,
) -> str:
    """Return the versioned reference digest; this is not an ABI state root."""

    canonical_bytes = canonical_reference_archive_bytes_v2(archive)
    return "0x" + hashlib.sha256(
        REFERENCE_DIGEST_PREFIX_V2 + canonical_bytes
    ).hexdigest()


def _reject_reference_step_v2(
    pre_archive: CanonicalReferenceNullifierArchiveV2,
    code: ReferenceRejectCodeV2,
    diagnostic: str,
) -> ReferenceRejectedV2:
    pre_digest = reference_archive_digest_v2(pre_archive)
    return ReferenceRejectedV2(
        code=code,
        pre_reference_archive_digest=pre_digest,
        diagnostic=diagnostic,
    )


def _candidate_entries_v2(
    pre_archive: CanonicalReferenceNullifierArchiveV2,
    claim_by_object: dict[str, ReferenceConsumptionClaimV2],
) -> tuple[ReferenceNullifierEntryV2, ...]:
    fresh_entries = tuple(
        ReferenceNullifierEntryV2(
            object_id=ReferenceObjectIdV2(claim.object_id.value),
            first_consumed_by_occurrence_id=ReferenceOccurrenceIdV2(
                claim.consumed_by_occurrence_id.value
            ),
        )
        for claim in claim_by_object.values()
    )
    return tuple(
        sorted(
            (*pre_archive.entries, *fresh_entries),
            key=lambda entry: entry.object_id.decoded_bytes,
        )
    )


def _require_reference_step_containers_v2(
    pre_archive: object,
    claims: object,
) -> None:
    if type(pre_archive) is not CanonicalReferenceNullifierArchiveV2:
        raise TypeError("pre_archive must be CanonicalReferenceNullifierArchiveV2")
    if type(claims) is not tuple:
        raise TypeError("claims must be an exact tuple")


def _snapshot_archive_v2(
    archive: CanonicalReferenceNullifierArchiveV2,
) -> CanonicalReferenceNullifierArchiveV2:
    if type(archive) is not CanonicalReferenceNullifierArchiveV2:
        raise TypeError("archive must be CanonicalReferenceNullifierArchiveV2")
    if type(archive.entries) is not tuple:
        raise TypeError("archive entries must remain an exact tuple")
    if len(archive.entries) > MAX_REFERENCE_NULLIFIERS_V2:
        raise ValueError("reference archive exceeds entry capacity")
    entries: list[ReferenceNullifierEntryV2] = []
    for entry in archive.entries:
        if type(entry) is not ReferenceNullifierEntryV2:
            raise TypeError("archive entries must remain exact reference entries")
        entries.append(
            ReferenceNullifierEntryV2(
                object_id=ReferenceObjectIdV2(entry.object_id.value),
                first_consumed_by_occurrence_id=ReferenceOccurrenceIdV2(
                    entry.first_consumed_by_occurrence_id.value
                ),
            )
        )
    return CanonicalReferenceNullifierArchiveV2(tuple(entries))


def _snapshot_claims_v2(
    claims: tuple[ReferenceConsumptionClaimV2, ...],
) -> tuple[ReferenceConsumptionClaimV2, ...]:
    owned: list[ReferenceConsumptionClaimV2] = []
    for claim in claims:
        if type(claim) is not ReferenceConsumptionClaimV2:
            raise TypeError("claims must contain exact ReferenceConsumptionClaimV2 values")
        owned.append(
            ReferenceConsumptionClaimV2(
                object_id=ReferenceObjectIdV2(claim.object_id.value),
                consumed_by_occurrence_id=ReferenceOccurrenceIdV2(
                    claim.consumed_by_occurrence_id.value
                ),
            )
        )
    return tuple(owned)


def _accept_candidate_entries_v2(
    pre_archive: CanonicalReferenceNullifierArchiveV2,
    candidate_entries: tuple[ReferenceNullifierEntryV2, ...],
) -> ReferenceResultV2:
    if (
        len(_canonical_archive_bytes_from_entries_v2(candidate_entries))
        > MAX_REFERENCE_ARCHIVE_BYTES_V2
    ):
        return _reject_reference_step_v2(
            pre_archive,
            ReferenceRejectCodeV2.REFERENCE_ARCHIVE_BYTE_LIMIT_EXCEEDED,
            "reference archive successor exceeds canonical byte limit",
        )
    return ReferenceAcceptedV2(
        pre_reference_archive_digest=reference_archive_digest_v2(pre_archive),
        post_archive=CanonicalReferenceNullifierArchiveV2(entries=candidate_entries),
    )


def apply_reference_object_nullifiers_v2(
    pre_archive: CanonicalReferenceNullifierArchiveV2,
    claims: tuple[ReferenceConsumptionClaimV2, ...],
) -> ReferenceResultV2:
    """Apply one bounded logical-consumption step with fixed reject precedence.

    The function is total over its validated immutable input types. Rejection
    exposes no successor. Empty claims return an owned value-equivalent archive.
    """

    _require_reference_step_containers_v2(pre_archive, claims)
    owned_pre_archive = _snapshot_archive_v2(pre_archive)

    claim_count = len(claims)
    if claim_count > MAX_REFERENCE_CLAIMS_PER_STEP_V2:
        return _reject_reference_step_v2(
            owned_pre_archive,
            ReferenceRejectCodeV2.REFERENCE_STEP_LIMIT_EXCEEDED,
            "reference step claim count exceeds 64",
        )

    owned_claims = _snapshot_claims_v2(claims)
    claim_by_object = {claim.object_id.value: claim for claim in owned_claims}
    if len(claim_by_object) != claim_count:
        return _reject_reference_step_v2(
            owned_pre_archive,
            ReferenceRejectCodeV2.REFERENCE_DUPLICATE_IN_BATCH,
            "reference step repeats an object identifier",
        )

    consumed_ids = {entry.object_id.value for entry in owned_pre_archive.entries}
    # MUTATION_ANCHOR:M05_HISTORICAL_BEFORE_CAPACITY
    if any(object_id in consumed_ids for object_id in claim_by_object):
        return _reject_reference_step_v2(
            owned_pre_archive,
            ReferenceRejectCodeV2.REFERENCE_ALREADY_CONSUMED,
            "reference step includes a previously consumed object",
        )

    successor_count = len(owned_pre_archive.entries) + claim_count
    if successor_count > MAX_REFERENCE_NULLIFIERS_V2:
        return _reject_reference_step_v2(
            owned_pre_archive,
            ReferenceRejectCodeV2.REFERENCE_ARCHIVE_CAPACITY_EXCEEDED,
            "reference archive successor exceeds 4096 entries",
        )

    if claim_count == 0:
        return ReferenceAcceptedV2(
            pre_reference_archive_digest=reference_archive_digest_v2(
                owned_pre_archive
            ),
            post_archive=owned_pre_archive,  # Exact value no-op with owned data.
        )

    return _accept_candidate_entries_v2(
        owned_pre_archive,
        _candidate_entries_v2(owned_pre_archive, claim_by_object),
    )


__all__ = [
    "REFERENCE_SCHEMA_V2",
    "MAX_REFERENCE_NULLIFIERS_V2",
    "MAX_REFERENCE_CLAIMS_PER_STEP_V2",
    "MAX_REFERENCE_ARCHIVE_BYTES_V2",
    "ReferenceObjectIdV2",
    "ReferenceOccurrenceIdV2",
    "ReferenceConsumptionClaimV2",
    "ReferenceNullifierEntryV2",
    "CanonicalReferenceNullifierArchiveV2",
    "ReferenceRejectCodeV2",
    "ReferenceAcceptedV2",
    "ReferenceRejectedV2",
    "ReferenceResultV2",
    "canonical_reference_archive_bytes_v2",
    "reference_archive_digest_v2",
    "apply_reference_object_nullifiers_v2",
]
