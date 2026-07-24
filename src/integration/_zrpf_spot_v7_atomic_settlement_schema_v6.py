"""Exact SQLite schema V6 with retained finality-checker invocation bytes."""

from __future__ import annotations

import sqlite3

from src.integration._zrpf_spot_v7_atomic_settlement_schema import (
    SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1,
    _normalize_sql,
    _opening_storage_row,
    _require_canonical_genesis_cells,
    _validate_genesis_cells,
    _validate_store_identity,
)
from src.integration._zrpf_spot_v7_atomic_settlement_schema_v4 import (
    _insert_policy_v4,
    _require_frozen_v4_base_schema,
    _validate_policy_v4,
)
from src.integration._zrpf_spot_v7_atomic_settlement_schema_v5 import (
    _V5_EXPECTED_SCHEMA_SQL,
    _insert_activation_blocker_v5,
    _validate_activation_blocker_v5,
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

SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V6 = 6

_V6_META_SCHEMA = _V5_EXPECTED_SCHEMA_SQL["spot_v7_store_meta"].replace(
    "schema_version = 5",
    "schema_version = 6",
)

_V6_FINALITY_INVOCATION_SCHEMA = """
    CREATE TABLE spot_v7_checkpoint_finality_invocation_v6 (
        settlement_commitment BLOB NOT NULL PRIMARY KEY REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT,
        finality_certificate_root BLOB NOT NULL UNIQUE CHECK (typeof(finality_certificate_root) = 'blob' AND length(finality_certificate_root) = 32),
        exact_finality_certificate_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(exact_finality_certificate_sha256) = 'blob' AND length(exact_finality_certificate_sha256) = 32),
        authority_manifest_sha256 BLOB NOT NULL CHECK (typeof(authority_manifest_sha256) = 'blob' AND length(authority_manifest_sha256) = 32),
        checker_executable_sha256 BLOB NOT NULL CHECK (typeof(checker_executable_sha256) = 'blob' AND length(checker_executable_sha256) = 32),
        request_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(request_sha256) = 'blob' AND length(request_sha256) = 32),
        response_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(response_sha256) = 'blob' AND length(response_sha256) = 32),
        exact_authority_manifest BLOB NOT NULL CHECK (typeof(exact_authority_manifest) = 'blob' AND length(exact_authority_manifest) BETWEEN 1 AND 4096),
        exact_request BLOB NOT NULL CHECK (typeof(exact_request) = 'blob' AND length(exact_request) BETWEEN 886 AND 1461),
        exact_response BLOB NOT NULL CHECK (typeof(exact_response) = 'blob' AND length(exact_response) = 330),
        manifest_pinned_cross_check_executed INTEGER NOT NULL CHECK (manifest_pinned_cross_check_executed = 1),
        release_governed_checker_identity_verified INTEGER NOT NULL CHECK (release_governed_checker_identity_verified = 0),
        hostile_same_interpreter_resistance_established INTEGER NOT NULL CHECK (hostile_same_interpreter_resistance_established = 0),
        proof_receipt_authority INTEGER NOT NULL CHECK (proof_receipt_authority = 0),
        runtime_authority INTEGER NOT NULL CHECK (runtime_authority = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
"""

_V6_EXPECTED_SCHEMA_SQL = {
    **_V5_EXPECTED_SCHEMA_SQL,
    "spot_v7_store_meta": _V6_META_SCHEMA,
    "spot_v7_checkpoint_finality_invocation_v6": _V6_FINALITY_INVOCATION_SCHEMA,
}


def _initialize_or_validate_spot_v7_store_v6(
    connection: sqlite3.Connection,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
    policy: _GovernedSpotV7OperationalPolicyV3,
    allow_initialize: bool = False,
) -> None:
    if not connection.in_transaction:
        raise ValueError("Spot V7 V6 initialization requires a transaction")
    _require_canonical_genesis_cells(genesis_cells)
    governed = _require_governed_operational_policy_v3(policy)
    projection = governed._projection_for_governed_da_v2()
    if (
        projection.application_id != identity.application_id
        or projection.chain_or_domain_id != identity.chain_or_domain_id
    ):
        raise ValueError("Spot V7 V6 policy does not match the store scope")
    existing = connection.execute(
        "SELECT name FROM sqlite_master WHERE name NOT LIKE 'sqlite_%'"
    ).fetchall()
    if not existing:
        if not allow_initialize:
            raise ValueError("empty Spot V7 V6 database cannot be reinitialized")
        _create_schema_v6(connection, identity=identity, genesis_cells=genesis_cells)
        _insert_policy_v4(connection, governed)
        _insert_activation_blocker_v5(connection)
    _validate_spot_v7_schema_v6(connection)
    _validate_store_identity(connection, identity)
    _validate_genesis_cells(connection, genesis_cells)
    _validate_policy_v4(connection, governed)
    _validate_activation_blocker_v5(connection)


def _create_schema_v6(
    connection: sqlite3.Connection,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
) -> None:
    _require_frozen_v4_base_schema()
    if int(connection.execute("PRAGMA application_id").fetchone()[0]) != 0:
        raise ValueError("empty Spot V7 V6 database has an application_id")
    if int(connection.execute("PRAGMA user_version").fetchone()[0]) != 0:
        raise ValueError("empty Spot V7 V6 database has a user_version")
    connection.execute(f"PRAGMA application_id = {SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1}")
    connection.execute(f"PRAGMA user_version = {SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V6}")
    for statement in _V6_EXPECTED_SCHEMA_SQL.values():
        connection.execute(statement)
    connection.execute(
        """
        INSERT INTO spot_v7_store_meta (
            singleton, schema_version, application_id, chain_or_domain_id,
            verified_program_id, verified_profile_id, verified_program_manifest_root,
            genesis_state_root, state_root, revision, settlement_count, cell_count,
            last_epoch_id_be, settlement_authority, production_authority,
            authority_blocked_reason
        ) VALUES (1, 6, ?, ?, ?, ?, ?, ?, ?, 0, 0, ?, NULL, 0, 0, ?)
        """,
        (
            _hash_bytes(identity.application_id, name="V6 store application_id"),
            _hash_bytes(identity.chain_or_domain_id, name="V6 store chain_or_domain_id"),
            _hash_bytes(identity.verified_program_id, name="V6 store verified_program_id"),
            _hash_bytes(identity.verified_profile_id, name="V6 store verified_profile_id"),
            _hash_bytes(
                identity.verified_program_manifest_root,
                name="V6 store verified_program_manifest_root",
            ),
            _hash_bytes(identity.genesis_state_root, name="V6 store genesis_state_root"),
            _hash_bytes(identity.genesis_state_root, name="V6 store state_root"),
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


def _validate_spot_v7_schema_v6(connection: sqlite3.Connection) -> None:
    _require_frozen_v4_base_schema()
    application_id = int(connection.execute("PRAGMA application_id").fetchone()[0])
    if application_id != SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1:
        raise ValueError("Spot V7 V6 store application_id mismatch")
    version = int(connection.execute("PRAGMA user_version").fetchone()[0])
    if version != SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V6:
        raise ValueError("Spot V7 V6 store user_version mismatch")
    rows = connection.execute(
        """
        SELECT type, name, sql FROM sqlite_master
        WHERE name NOT LIKE 'sqlite_%'
        ORDER BY type, name
        """
    ).fetchall()
    observed = {(str(row["type"]), str(row["name"])) for row in rows}
    expected = {("table", name) for name in _V6_EXPECTED_SCHEMA_SQL}
    if observed != expected:
        raise ValueError("Spot V7 V6 schema object set mismatch")
    for row in rows:
        name = str(row["name"])
        if _normalize_sql(str(row["sql"])) != _normalize_sql(_V6_EXPECTED_SCHEMA_SQL[name]):
            raise ValueError(f"Spot V7 V6 schema SQL mismatch for {name}")
    meta = connection.execute(
        "SELECT schema_version FROM spot_v7_store_meta WHERE singleton = 1"
    ).fetchone()
    if meta is None or int(meta[0]) != SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V6:
        raise ValueError("Spot V7 V6 metadata schema version mismatch")


__all__ = ()
