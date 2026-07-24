"""Exact dormant authority-capable SQLite schema V5 for Spot V7."""

from __future__ import annotations

import sqlite3

from src.integration._zrpf_spot_v7_atomic_settlement_engine_v5 import (
    SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5,
)
from src.integration._zrpf_spot_v7_atomic_settlement_schema import (
    SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1,
    _normalize_sql,
    _opening_storage_row,
    _require_canonical_genesis_cells,
    _validate_genesis_cells,
    _validate_store_identity,
)
from src.integration._zrpf_spot_v7_atomic_settlement_schema_v4 import (
    _V4_EXPECTED_SCHEMA_SQL,
    _insert_policy_v4,
    _require_frozen_v4_base_schema,
    _validate_policy_v4,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
    _require_governed_operational_policy_v3,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    SpotV7AtomicSettlementStoreIdentityV1,
    SpotV7CellOpeningV1,
    _hash_bytes,
)

SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V5 = 5

_V5_META_SCHEMA = _V4_EXPECTED_SCHEMA_SQL["spot_v7_store_meta"].replace(
    "schema_version = 4",
    "schema_version = 5",
)

_SELECTION_BLOCKER = SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5.codes[0].value
_REVOCATION_BLOCKER = SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5.codes[1].value
_ROLLBACK_BLOCKER = SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5.codes[2].value
_RELEASE_BLOCKER = SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5.codes[3].value
_RUNTIME_BLOCKER = SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5.codes[4].value
_ACTIVATION_BLOCKER_TEXT = ",".join(
    code.value for code in SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5.codes
)

_V5_AUTHORITY_PROVENANCE_SCHEMA = f"""
    CREATE TABLE spot_v7_authority_provenance_v5 (
        settlement_commitment BLOB NOT NULL PRIMARY KEY REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT,
        prerequisite_set_root BLOB NOT NULL UNIQUE CHECK (typeof(prerequisite_set_root) = 'blob' AND length(prerequisite_set_root) = 32),
        proof_receipt_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(proof_receipt_sha256) = 'blob' AND length(proof_receipt_sha256) = 32),
        proof_journal_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(proof_journal_sha256) = 'blob' AND length(proof_journal_sha256) = 32),
        verified_program_id BLOB NOT NULL CHECK (typeof(verified_program_id) = 'blob' AND length(verified_program_id) = 32),
        verified_profile_id BLOB NOT NULL CHECK (typeof(verified_profile_id) = 'blob' AND length(verified_profile_id) = 32),
        verified_program_manifest_root BLOB NOT NULL CHECK (typeof(verified_program_manifest_root) = 'blob' AND length(verified_program_manifest_root) = 32),
        proof_verifier_manifest_sha256 BLOB NOT NULL CHECK (typeof(proof_verifier_manifest_sha256) = 'blob' AND length(proof_verifier_manifest_sha256) = 32),
        runtime_execution_record_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(runtime_execution_record_sha256) = 'blob' AND length(runtime_execution_record_sha256) = 32),
        runtime_output_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(runtime_output_sha256) = 'blob' AND length(runtime_output_sha256) = 32),
        runtime_manifest_sha256 BLOB NOT NULL CHECK (typeof(runtime_manifest_sha256) = 'blob' AND length(runtime_manifest_sha256) = 32),
        release_manifest_sha256 BLOB NOT NULL CHECK (typeof(release_manifest_sha256) = 'blob' AND length(release_manifest_sha256) = 32),
        release_evidence_sha256 BLOB NOT NULL CHECK (typeof(release_evidence_sha256) = 'blob' AND length(release_evidence_sha256) = 32),
        authority_manifest_sha256 BLOB NOT NULL CHECK (typeof(authority_manifest_sha256) = 'blob' AND length(authority_manifest_sha256) = 32),
        da_certificate_root BLOB NOT NULL UNIQUE CHECK (typeof(da_certificate_root) = 'blob' AND length(da_certificate_root) = 32),
        finality_certificate_root BLOB NOT NULL UNIQUE CHECK (typeof(finality_certificate_root) = 'blob' AND length(finality_certificate_root) = 32),
        replay_material_root BLOB NOT NULL UNIQUE CHECK (typeof(replay_material_root) = 'blob' AND length(replay_material_root) = 32),
        exact_proof_verifier_manifest BLOB NOT NULL CHECK (typeof(exact_proof_verifier_manifest) = 'blob' AND length(exact_proof_verifier_manifest) BETWEEN 1 AND 4194304),
        exact_runtime_manifest BLOB NOT NULL CHECK (typeof(exact_runtime_manifest) = 'blob' AND length(exact_runtime_manifest) BETWEEN 1 AND 4194304),
        exact_release_manifest BLOB NOT NULL CHECK (typeof(exact_release_manifest) = 'blob' AND length(exact_release_manifest) BETWEEN 1 AND 4194304),
        exact_release_evidence BLOB NOT NULL CHECK (typeof(exact_release_evidence) = 'blob' AND length(exact_release_evidence) BETWEEN 1 AND 8388608),
        exact_authority_manifest BLOB NOT NULL CHECK (typeof(exact_authority_manifest) = 'blob' AND length(exact_authority_manifest) BETWEEN 1 AND 4194304),
        release_revision_be BLOB NOT NULL CHECK (typeof(release_revision_be) = 'blob' AND length(release_revision_be) = 8),
        release_activation_epoch_be BLOB NOT NULL CHECK (typeof(release_activation_epoch_be) = 'blob' AND length(release_activation_epoch_be) = 8),
        release_revocation_epoch_be BLOB CHECK (release_revocation_epoch_be IS NULL OR (typeof(release_revocation_epoch_be) = 'blob' AND length(release_revocation_epoch_be) = 8)),
        evaluation_epoch_be BLOB NOT NULL CHECK (typeof(evaluation_epoch_be) = 'blob' AND length(evaluation_epoch_be) = 8),
        current_release_evidence_verified INTEGER NOT NULL CHECK (current_release_evidence_verified = 0),
        proof_receipt_authority INTEGER NOT NULL CHECK (proof_receipt_authority = 0),
        runtime_authority INTEGER NOT NULL CHECK (runtime_authority = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0),
        activation_blocker TEXT NOT NULL CHECK (activation_blocker = '{_ACTIVATION_BLOCKER_TEXT}')
    ) STRICT, WITHOUT ROWID
"""

_V5_ACTIVATION_BLOCKER_SCHEMA = f"""
    CREATE TABLE spot_v7_activation_blocker_v5 (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        governed_release_selection_blocker_code TEXT NOT NULL CHECK (governed_release_selection_blocker_code = '{_SELECTION_BLOCKER}'),
        release_revocation_policy_blocker_code TEXT NOT NULL CHECK (release_revocation_policy_blocker_code = '{_REVOCATION_BLOCKER}'),
        release_rollback_protection_blocker_code TEXT NOT NULL CHECK (release_rollback_protection_blocker_code = '{_ROLLBACK_BLOCKER}'),
        fresh_release_blocker_code TEXT NOT NULL CHECK (fresh_release_blocker_code = '{_RELEASE_BLOCKER}'),
        fresh_runtime_blocker_code TEXT NOT NULL CHECK (fresh_runtime_blocker_code = '{_RUNTIME_BLOCKER}'),
        governed_release_selection_verified INTEGER NOT NULL CHECK (governed_release_selection_verified = 0),
        release_revocation_policy_verified INTEGER NOT NULL CHECK (release_revocation_policy_verified = 0),
        release_rollback_protection_verified INTEGER NOT NULL CHECK (release_rollback_protection_verified = 0),
        fresh_governed_release_evidence_verified INTEGER NOT NULL CHECK (fresh_governed_release_evidence_verified = 0),
        fresh_governed_runtime_evidence_verified INTEGER NOT NULL CHECK (fresh_governed_runtime_evidence_verified = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
"""

_V5_EXPECTED_SCHEMA_SQL = {
    **_V4_EXPECTED_SCHEMA_SQL,
    "spot_v7_store_meta": _V5_META_SCHEMA,
    "spot_v7_authority_provenance_v5": _V5_AUTHORITY_PROVENANCE_SCHEMA,
    "spot_v7_activation_blocker_v5": _V5_ACTIVATION_BLOCKER_SCHEMA,
}


def _initialize_or_validate_spot_v7_store_v5(
    connection: sqlite3.Connection,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
    policy: _GovernedSpotV7OperationalPolicyV3,
    allow_initialize: bool = False,
) -> None:
    if not connection.in_transaction:
        raise ValueError("Spot V7 V5 initialization requires a transaction")
    _require_canonical_genesis_cells(genesis_cells)
    governed = _require_governed_operational_policy_v3(policy)
    projection = governed._projection_for_governed_da_v2()
    if (
        projection.application_id != identity.application_id
        or projection.chain_or_domain_id != identity.chain_or_domain_id
    ):
        raise ValueError("Spot V7 V5 policy does not match the store scope")
    existing = connection.execute(
        "SELECT name FROM sqlite_master WHERE name NOT LIKE 'sqlite_%'"
    ).fetchall()
    if not existing:
        if not allow_initialize:
            raise ValueError("empty Spot V7 V5 database cannot be reinitialized")
        _create_schema_v5(connection, identity=identity, genesis_cells=genesis_cells)
        _insert_policy_v4(connection, governed)
        _insert_activation_blocker_v5(connection)
    _validate_spot_v7_schema_v5(connection)
    _validate_store_identity(connection, identity)
    _validate_genesis_cells(connection, genesis_cells)
    _validate_policy_v4(connection, governed)
    _validate_activation_blocker_v5(connection)


def _create_schema_v5(
    connection: sqlite3.Connection,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
) -> None:
    _require_frozen_v4_base_schema()
    if int(connection.execute("PRAGMA application_id").fetchone()[0]) != 0:
        raise ValueError("empty Spot V7 V5 database has an application_id")
    if int(connection.execute("PRAGMA user_version").fetchone()[0]) != 0:
        raise ValueError("empty Spot V7 V5 database has a user_version")
    connection.execute(f"PRAGMA application_id = {SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1}")
    connection.execute(f"PRAGMA user_version = {SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V5}")
    for statement in _V5_EXPECTED_SCHEMA_SQL.values():
        connection.execute(statement)
    connection.execute(
        """
        INSERT INTO spot_v7_store_meta (
            singleton, schema_version, application_id, chain_or_domain_id,
            verified_program_id, verified_profile_id, verified_program_manifest_root,
            genesis_state_root, state_root, revision, settlement_count, cell_count,
            last_epoch_id_be, settlement_authority, production_authority,
            authority_blocked_reason
        ) VALUES (1, 5, ?, ?, ?, ?, ?, ?, ?, 0, 0, ?, NULL, 0, 0, ?)
        """,
        (
            _hash_bytes(identity.application_id, name="V5 store application_id"),
            _hash_bytes(identity.chain_or_domain_id, name="V5 store chain_or_domain_id"),
            _hash_bytes(identity.verified_program_id, name="V5 store verified_program_id"),
            _hash_bytes(identity.verified_profile_id, name="V5 store verified_profile_id"),
            _hash_bytes(
                identity.verified_program_manifest_root,
                name="V5 store verified_program_manifest_root",
            ),
            _hash_bytes(identity.genesis_state_root, name="V5 store genesis_state_root"),
            _hash_bytes(identity.genesis_state_root, name="V5 store state_root"),
            len(genesis_cells),
            SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
        ),
    )
    rows = tuple(_opening_storage_row(cell) for cell in genesis_cells)
    connection.executemany(
        """
        INSERT INTO spot_v7_genesis_cells (
            cell_key, kind, subject_id, asset_id, atoms_be, value_hash
        ) VALUES (?, ?, ?, ?, ?, ?)
        """,
        rows,
    )
    connection.executemany(
        """
        INSERT INTO spot_v7_cells (
            cell_key, kind, subject_id, asset_id, atoms_be, value_hash, updated_revision
        ) VALUES (?, ?, ?, ?, ?, ?, 0)
        """,
        rows,
    )


def _insert_activation_blocker_v5(connection: sqlite3.Connection) -> None:
    connection.execute(
        """
        INSERT INTO spot_v7_activation_blocker_v5 (
            singleton, governed_release_selection_blocker_code,
            release_revocation_policy_blocker_code,
            release_rollback_protection_blocker_code,
            fresh_release_blocker_code, fresh_runtime_blocker_code,
            governed_release_selection_verified,
            release_revocation_policy_verified,
            release_rollback_protection_verified,
            fresh_governed_release_evidence_verified,
            fresh_governed_runtime_evidence_verified, release_authority,
            settlement_authority, production_authority
        ) VALUES (1, ?, ?, ?, ?, ?, 0, 0, 0, 0, 0, 0, 0, 0)
        """,
        (
            _SELECTION_BLOCKER,
            _REVOCATION_BLOCKER,
            _ROLLBACK_BLOCKER,
            _RELEASE_BLOCKER,
            _RUNTIME_BLOCKER,
        ),
    )


def _validate_spot_v7_schema_v5(connection: sqlite3.Connection) -> None:
    _require_frozen_v4_base_schema()
    application_id = int(connection.execute("PRAGMA application_id").fetchone()[0])
    if application_id != SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1:
        raise ValueError("Spot V7 V5 store application_id mismatch")
    version = int(connection.execute("PRAGMA user_version").fetchone()[0])
    if version != SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V5:
        raise ValueError("Spot V7 V5 store user_version mismatch")
    rows = connection.execute(
        """
        SELECT type, name, sql FROM sqlite_master
        WHERE name NOT LIKE 'sqlite_%'
        ORDER BY type, name
        """
    ).fetchall()
    observed = {(str(row["type"]), str(row["name"])) for row in rows}
    expected = {("table", name) for name in _V5_EXPECTED_SCHEMA_SQL}
    if observed != expected:
        raise ValueError("Spot V7 V5 schema object set mismatch")
    for row in rows:
        name = str(row["name"])
        if _normalize_sql(str(row["sql"])) != _normalize_sql(_V5_EXPECTED_SCHEMA_SQL[name]):
            raise ValueError(f"Spot V7 V5 schema SQL mismatch for {name}")
    meta = connection.execute(
        "SELECT schema_version FROM spot_v7_store_meta WHERE singleton = 1"
    ).fetchone()
    if meta is None or int(meta[0]) != SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V5:
        raise ValueError("Spot V7 V5 metadata schema version mismatch")


def _validate_activation_blocker_v5(connection: sqlite3.Connection) -> None:
    row = connection.execute(
        "SELECT * FROM spot_v7_activation_blocker_v5 WHERE singleton = 1"
    ).fetchone()
    if row is None:
        raise ValueError("Spot V7 V5 activation blocker is missing")
    if str(row["governed_release_selection_blocker_code"]) != _SELECTION_BLOCKER:
        raise ValueError("Spot V7 V5 release selection blocker mismatch")
    if str(row["release_revocation_policy_blocker_code"]) != _REVOCATION_BLOCKER:
        raise ValueError("Spot V7 V5 release revocation blocker mismatch")
    if str(row["release_rollback_protection_blocker_code"]) != _ROLLBACK_BLOCKER:
        raise ValueError("Spot V7 V5 release rollback blocker mismatch")
    if str(row["fresh_release_blocker_code"]) != _RELEASE_BLOCKER:
        raise ValueError("Spot V7 V5 release blocker mismatch")
    if str(row["fresh_runtime_blocker_code"]) != _RUNTIME_BLOCKER:
        raise ValueError("Spot V7 V5 runtime blocker mismatch")
    false_fields = (
        "governed_release_selection_verified",
        "release_revocation_policy_verified",
        "release_rollback_protection_verified",
        "fresh_governed_release_evidence_verified",
        "fresh_governed_runtime_evidence_verified",
        "release_authority",
        "settlement_authority",
        "production_authority",
    )
    if any(int(row[field]) != 0 for field in false_fields):
        raise ValueError("Spot V7 V5 activation nonclaim mismatch")


__all__ = ()
