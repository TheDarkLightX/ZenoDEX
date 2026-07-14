"""Exact SQLite persistence for governed Spot V7 policy provenance."""

from __future__ import annotations

import hashlib
import sqlite3
from typing import cast

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedOperationalPolicyProvenanceV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import _hash_bytes


def _insert_policy_provenance(
    connection: sqlite3.Connection,
    provenance: _GovernedOperationalPolicyProvenanceV1,
) -> None:
    connection.execute(
        """
        INSERT INTO spot_v7_operational_policy_provenance (
            singleton, evidence_root, manifest_sha256, signer_registry_hash,
            signature_quorum_report_hash, policy_revision_be,
            policy_activation_epoch_be, policy_revocation_epoch_be,
            signer_registry_revision_be, signer_registry_activation_epoch_be,
            signer_registry_revocation_epoch_be, evaluation_epoch_be,
            exact_evidence, release_authority, settlement_authority,
            production_authority
        ) VALUES (1, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0)
        """,
        _policy_provenance_storage_values(provenance),
    )


def _read_policy_provenance_row(connection: sqlite3.Connection) -> sqlite3.Row | None:
    return connection.execute(
        "SELECT * FROM spot_v7_operational_policy_provenance WHERE singleton = 1"
    ).fetchone()


def _require_governed_policy_provenance_locked(
    connection: sqlite3.Connection,
    expected: _GovernedOperationalPolicyProvenanceV1,
) -> None:
    if not connection.in_transaction:
        raise ValueError("governed policy provenance check requires a transaction")
    _validate_policy_provenance_row(_read_policy_provenance_row(connection), expected)


def _validate_policy_provenance_row(
    row: sqlite3.Row | None,
    expected: _GovernedOperationalPolicyProvenanceV1,
) -> None:
    if row is None:
        raise ValueError("governed operational policy provenance row is missing")
    _validate_policy_provenance_integrity(row)
    if bytes(row["exact_evidence"]) != expected.exact_evidence_bytes:
        raise ValueError("stored operational policy provenance evidence mismatch")
    if _policy_provenance_row_values(row) != _policy_provenance_storage_values(expected):
        raise ValueError("stored operational policy provenance binding mismatch")


def _validate_policy_provenance_integrity(row: sqlite3.Row) -> None:
    if hashlib.sha256(bytes(row["exact_evidence"])).digest() != bytes(
        row["evidence_root"]
    ):
        raise ValueError("stored operational policy provenance root mismatch")
    if any(
        int(row[field]) != 0
        for field in ("release_authority", "settlement_authority", "production_authority")
    ):
        raise ValueError("operational policy provenance authority non-claim mismatch")


def _policy_provenance_storage_values(
    provenance: _GovernedOperationalPolicyProvenanceV1,
) -> tuple[object, ...]:
    return (
        _hash_bytes(provenance.evidence_root, name="policy provenance root"),
        bytes.fromhex(provenance.manifest_sha256),
        _hash_bytes(provenance.signer_registry_hash, name="policy signer registry"),
        _hash_bytes(
            provenance.signature_quorum_report_hash,
            name="policy signature quorum report",
        ),
        provenance.policy_revision.to_bytes(8, "big"),
        provenance.policy_activation_epoch.to_bytes(8, "big"),
        _optional_u64_storage(provenance.policy_revocation_epoch),
        provenance.signer_registry_revision.to_bytes(8, "big"),
        provenance.signer_registry_activation_epoch.to_bytes(8, "big"),
        _optional_u64_storage(provenance.signer_registry_revocation_epoch),
        provenance.evaluation_epoch.to_bytes(8, "big"),
        provenance.exact_evidence_bytes,
    )


def _policy_provenance_row_values(row: sqlite3.Row) -> tuple[object, ...]:
    return (
        bytes(row["evidence_root"]),
        bytes(row["manifest_sha256"]),
        bytes(row["signer_registry_hash"]),
        bytes(row["signature_quorum_report_hash"]),
        bytes(row["policy_revision_be"]),
        bytes(row["policy_activation_epoch_be"]),
        _optional_blob(row["policy_revocation_epoch_be"]),
        bytes(row["signer_registry_revision_be"]),
        bytes(row["signer_registry_activation_epoch_be"]),
        _optional_blob(row["signer_registry_revocation_epoch_be"]),
        bytes(row["evaluation_epoch_be"]),
        bytes(row["exact_evidence"]),
    )


def _optional_u64_storage(value: int | None) -> bytes | None:
    return None if value is None else value.to_bytes(8, "big")


def _optional_blob(value: object) -> bytes | None:
    if value is None:
        return None
    if not isinstance(value, (bytes, bytearray, memoryview)):
        raise TypeError("stored optional u64 must be bytes or NULL")
    return bytes(cast(bytes | bytearray | memoryview, value))


__all__: list[str] = []
