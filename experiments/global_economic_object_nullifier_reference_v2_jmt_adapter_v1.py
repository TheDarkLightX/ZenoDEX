"""Experimental JMT projection for the V2 object-nullifier reference.

This module is a differential-testing adapter. It has no settlement,
publication, persistence, release, proof, state-root, or production authority.
"""

from __future__ import annotations

import re

from experiments.global_economic_object_nullifier_reference_v2 import (
    CanonicalReferenceNullifierArchiveV2,
    ReferenceObjectIdV2,
    ReferenceOccurrenceIdV2,
)
from src.state.jmt import (
    compute_jmt_root,
    decode_jmt_absence_proof,
    decode_jmt_membership_proof,
    encode_jmt_absence_proof,
    encode_jmt_membership_proof,
    prove_jmt_absence,
    prove_jmt_membership,
    verify_jmt_absence,
    verify_jmt_membership,
)

OBJECT_NULLIFIER_JMT_ADAPTER_VERSION_V1 = 1
MAX_OBJECT_NULLIFIER_JMT_WITNESS_BYTES_V1 = 32_768

_ROOT_RE_V1 = re.compile(r"0x[0-9a-f]{64}")


def _snapshot_archive_v1(
    archive: object,
) -> CanonicalReferenceNullifierArchiveV2:
    if type(archive) is not CanonicalReferenceNullifierArchiveV2:
        raise TypeError(
            "archive must be an exact CanonicalReferenceNullifierArchiveV2"
        )
    try:
        entries = archive.entries
    except AttributeError as exc:
        raise TypeError("archive entries are missing") from exc
    return CanonicalReferenceNullifierArchiveV2(entries=entries)


def _snapshot_object_id_v1(value: object) -> ReferenceObjectIdV2:
    if type(value) is not ReferenceObjectIdV2:
        raise TypeError("object_id must be an exact ReferenceObjectIdV2")
    try:
        raw = value.value
    except AttributeError as exc:
        raise TypeError("object_id value is missing") from exc
    return ReferenceObjectIdV2(raw)


def _snapshot_occurrence_id_v1(value: object) -> ReferenceOccurrenceIdV2:
    if type(value) is not ReferenceOccurrenceIdV2:
        raise TypeError("occurrence_id must be an exact ReferenceOccurrenceIdV2")
    try:
        raw = value.value
    except AttributeError as exc:
        raise TypeError("occurrence_id value is missing") from exc
    return ReferenceOccurrenceIdV2(raw)


def _decoded_id_v1(value: str) -> bytes:
    return bytes.fromhex(value[2:])


def _snapshot_root_v1(root: object) -> str:
    if type(root) is not str or _ROOT_RE_V1.fullmatch(root) is None:
        raise ValueError("candidate_root must be canonical lowercase 0x-prefixed SHA-256")
    return root


def _snapshot_witness_v1(payload: object) -> bytes:
    if type(payload) is not bytes:
        raise TypeError("witness_payload must be exact bytes")
    if len(payload) == 0 or len(payload) > MAX_OBJECT_NULLIFIER_JMT_WITNESS_BYTES_V1:
        raise ValueError("witness_payload exceeds the bounded canonical wire envelope")
    return payload


def project_reference_archive_to_jmt_entries_v1(
    archive: CanonicalReferenceNullifierArchiveV2,
) -> tuple[tuple[bytes, bytes], ...]:
    """Project each validated row to raw object and occurrence ID bytes."""

    owned = _snapshot_archive_v1(archive)
    return tuple(
        (
            _decoded_id_v1(entry.object_id.value),
            _decoded_id_v1(entry.first_consumed_by_occurrence_id.value),
        )
        for entry in owned.entries
    )


def reference_archive_candidate_jmt_root_v1(
    archive: CanonicalReferenceNullifierArchiveV2,
) -> str:
    """Return an experimental candidate root for one reference archive."""

    return compute_jmt_root(project_reference_archive_to_jmt_entries_v1(archive))


def encode_reference_object_membership_witness_v1(
    archive: CanonicalReferenceNullifierArchiveV2,
    object_id: ReferenceObjectIdV2,
) -> bytes:
    """Return one bounded canonical membership transcript as opaque bytes."""

    entries = project_reference_archive_to_jmt_entries_v1(archive)
    key = _decoded_id_v1(_snapshot_object_id_v1(object_id).value)
    payload = encode_jmt_membership_proof(prove_jmt_membership(entries, key))
    return _snapshot_witness_v1(payload)


def verify_reference_object_membership_witness_v1(
    candidate_root: str,
    object_id: ReferenceObjectIdV2,
    first_consumed_by_occurrence_id: ReferenceOccurrenceIdV2,
    witness_payload: bytes,
) -> bool:
    """Fail closed over canonical wire bytes; no proof object crosses this API."""

    try:
        root = _snapshot_root_v1(candidate_root)
        key = _decoded_id_v1(_snapshot_object_id_v1(object_id).value)
        value = _decoded_id_v1(
            _snapshot_occurrence_id_v1(first_consumed_by_occurrence_id).value
        )
        payload = _snapshot_witness_v1(witness_payload)
        proof = decode_jmt_membership_proof(payload)
    except (AttributeError, KeyError, RecursionError, TypeError, ValueError):
        return False
    return verify_jmt_membership(root, key, value, proof)


def encode_reference_object_absence_witness_v1(
    archive: CanonicalReferenceNullifierArchiveV2,
    object_id: ReferenceObjectIdV2,
) -> bytes:
    """Return one bounded canonical absence transcript as opaque bytes."""

    entries = project_reference_archive_to_jmt_entries_v1(archive)
    key = _decoded_id_v1(_snapshot_object_id_v1(object_id).value)
    payload = encode_jmt_absence_proof(prove_jmt_absence(entries, key))
    return _snapshot_witness_v1(payload)


def verify_reference_object_absence_witness_v1(
    candidate_root: str,
    object_id: ReferenceObjectIdV2,
    witness_payload: bytes,
) -> bool:
    """Fail closed over a canonical absence transcript and exact typed key."""

    try:
        root = _snapshot_root_v1(candidate_root)
        key = _decoded_id_v1(_snapshot_object_id_v1(object_id).value)
        payload = _snapshot_witness_v1(witness_payload)
        proof = decode_jmt_absence_proof(payload)
    except (AttributeError, KeyError, RecursionError, TypeError, ValueError):
        return False
    return verify_jmt_absence(root, key, proof)


__all__ = [
    "OBJECT_NULLIFIER_JMT_ADAPTER_VERSION_V1",
    "MAX_OBJECT_NULLIFIER_JMT_WITNESS_BYTES_V1",
    "project_reference_archive_to_jmt_entries_v1",
    "reference_archive_candidate_jmt_root_v1",
    "encode_reference_object_membership_witness_v1",
    "verify_reference_object_membership_witness_v1",
    "encode_reference_object_absence_witness_v1",
    "verify_reference_object_absence_witness_v1",
]
