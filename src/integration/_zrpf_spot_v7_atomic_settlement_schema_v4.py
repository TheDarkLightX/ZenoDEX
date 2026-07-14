"""Exact SQLite schema V4 for authority-neutral Spot V7 operational commits."""

from __future__ import annotations

import hashlib
import sqlite3

from src.integration._zrpf_spot_v7_atomic_settlement_schema import (
    _EXPECTED_SCHEMA_SQL,
    SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1,
    _normalize_sql,
    _opening_storage_row,
    _require_canonical_genesis_cells,
    _validate_genesis_cells,
    _validate_store_identity,
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
    _root_bytes_allow_zero,
)

SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V4 = 4
SPOT_V7_V4_BASE_ECONOMIC_SCHEMA_SHA256 = (
    "89209dcee199f09ce18970990075d91b4e589dae8e473b2472cd8c9cce5fae25"
)

_V4_BASE_ECONOMIC_TABLES = (
    "spot_v7_store_meta",
    "spot_v7_genesis_cells",
    "spot_v7_cells",
    "spot_v7_settlements",
    "spot_v7_cell_transitions",
    "spot_v7_asset_effects",
    "spot_v7_economic_actions",
    "spot_v7_authorization_nullifiers",
    "spot_v7_authorization_grant_spends",
    "spot_v7_consumed_objects",
)

_V4_META_SCHEMA = _EXPECTED_SCHEMA_SQL["spot_v7_store_meta"].replace(
    "schema_version = 3",
    "schema_version = 4",
)

_V4_BASE_ECONOMIC_SCHEMA_SQL = {
    name: _V4_META_SCHEMA if name == "spot_v7_store_meta" else _EXPECTED_SCHEMA_SQL[name]
    for name in _V4_BASE_ECONOMIC_TABLES
}

_V4_SCHEMA_STATEMENTS = (
    """
    CREATE TABLE spot_v7_operational_policy_v4 (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        application_id BLOB NOT NULL CHECK (typeof(application_id) = 'blob' AND length(application_id) = 32),
        chain_or_domain_id BLOB NOT NULL CHECK (typeof(chain_or_domain_id) = 'blob' AND length(chain_or_domain_id) = 32),
        zeno_ledger_chain_id TEXT NOT NULL CHECK (typeof(zeno_ledger_chain_id) = 'text' AND length(zeno_ledger_chain_id) BETWEEN 1 AND 128),
        full_blob_policy_root BLOB NOT NULL CHECK (typeof(full_blob_policy_root) = 'blob' AND length(full_blob_policy_root) = 32),
        sampled_policy_root BLOB NOT NULL CHECK (typeof(sampled_policy_root) = 'blob' AND length(sampled_policy_root) = 32),
        beacon_policy_root BLOB NOT NULL CHECK (typeof(beacon_policy_root) = 'blob' AND length(beacon_policy_root) = 32),
        checkpoint_finality_policy_root BLOB NOT NULL CHECK (typeof(checkpoint_finality_policy_root) = 'blob' AND length(checkpoint_finality_policy_root) = 32),
        beacon_source_finality_policy_root BLOB NOT NULL CHECK (typeof(beacon_source_finality_policy_root) = 'blob' AND length(beacon_source_finality_policy_root) = 32),
        policy_provenance_root BLOB NOT NULL CHECK (typeof(policy_provenance_root) = 'blob' AND length(policy_provenance_root) = 32),
        manifest_sha256 BLOB NOT NULL CHECK (typeof(manifest_sha256) = 'blob' AND length(manifest_sha256) = 32),
        exact_policy_evidence BLOB NOT NULL CHECK (typeof(exact_policy_evidence) = 'blob' AND length(exact_policy_evidence) BETWEEN 1 AND 4194304),
        current_checkpoint_sequence_be BLOB NOT NULL CHECK (typeof(current_checkpoint_sequence_be) = 'blob' AND length(current_checkpoint_sequence_be) = 8),
        current_checkpoint_hash BLOB NOT NULL CHECK (typeof(current_checkpoint_hash) = 'blob' AND length(current_checkpoint_hash) = 32),
        current_release_head_verified INTEGER NOT NULL CHECK (current_release_head_verified = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_operational_da_v4 (
        settlement_commitment BLOB NOT NULL PRIMARY KEY REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT,
        certificate_root BLOB NOT NULL UNIQUE CHECK (typeof(certificate_root) = 'blob' AND length(certificate_root) = 32),
        data_root BLOB NOT NULL CHECK (typeof(data_root) = 'blob' AND length(data_root) = 32),
        chunk_root BLOB NOT NULL CHECK (typeof(chunk_root) = 'blob' AND length(chunk_root) = 32),
        full_blob_policy_root BLOB NOT NULL CHECK (typeof(full_blob_policy_root) = 'blob' AND length(full_blob_policy_root) = 32),
        sampled_policy_root BLOB NOT NULL CHECK (typeof(sampled_policy_root) = 'blob' AND length(sampled_policy_root) = 32),
        checked_epoch_be BLOB NOT NULL CHECK (typeof(checked_epoch_be) = 'blob' AND length(checked_epoch_be) = 8),
        retention_through_epoch_be BLOB NOT NULL CHECK (typeof(retention_through_epoch_be) = 'blob' AND length(retention_through_epoch_be) = 8),
        exact_blob_sha256 BLOB NOT NULL CHECK (typeof(exact_blob_sha256) = 'blob' AND length(exact_blob_sha256) = 32),
        sampled_evidence_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(sampled_evidence_sha256) = 'blob' AND length(sampled_evidence_sha256) = 32),
        accepted_provider_set_root BLOB NOT NULL CHECK (typeof(accepted_provider_set_root) = 'blob' AND length(accepted_provider_set_root) = 32),
        beacon_commitment BLOB NOT NULL CHECK (typeof(beacon_commitment) = 'blob' AND length(beacon_commitment) = 32),
        source_network_id BLOB NOT NULL CHECK (typeof(source_network_id) = 'blob' AND length(source_network_id) = 32),
        source_protocol_id BLOB NOT NULL CHECK (typeof(source_protocol_id) = 'blob' AND length(source_protocol_id) = 32),
        source_epoch_lag_be BLOB NOT NULL CHECK (typeof(source_epoch_lag_be) = 'blob' AND length(source_epoch_lag_be) = 8),
        source_checkpoint_sequence_be BLOB NOT NULL CHECK (typeof(source_checkpoint_sequence_be) = 'blob' AND length(source_checkpoint_sequence_be) = 8),
        source_checkpoint_hash BLOB NOT NULL CHECK (typeof(source_checkpoint_hash) = 'blob' AND length(source_checkpoint_hash) = 32),
        source_finality_policy_root BLOB NOT NULL CHECK (typeof(source_finality_policy_root) = 'blob' AND length(source_finality_policy_root) = 32),
        source_finality_certificate_root BLOB NOT NULL CHECK (typeof(source_finality_certificate_root) = 'blob' AND length(source_finality_certificate_root) = 32),
        source_finality_evidence_root BLOB NOT NULL CHECK (typeof(source_finality_evidence_root) = 'blob' AND length(source_finality_evidence_root) = 32),
        exact_full_blob BLOB NOT NULL CHECK (typeof(exact_full_blob) = 'blob' AND length(exact_full_blob) BETWEEN 1 AND 8388608),
        exact_full_blob_certificate BLOB NOT NULL CHECK (typeof(exact_full_blob_certificate) = 'blob' AND length(exact_full_blob_certificate) BETWEEN 1 AND 512),
        exact_sampled_evidence BLOB NOT NULL CHECK (typeof(exact_sampled_evidence) = 'blob' AND length(exact_sampled_evidence) BETWEEN 1 AND 20971520),
        exact_source_finality_certificate BLOB NOT NULL CHECK (typeof(exact_source_finality_certificate) = 'blob' AND length(exact_source_finality_certificate) BETWEEN 1 AND 576),
        exact_source_finality_evidence BLOB NOT NULL CHECK (typeof(exact_source_finality_evidence) = 'blob' AND length(exact_source_finality_evidence) BETWEEN 1 AND 1048576),
        exact_content_verified INTEGER NOT NULL CHECK (exact_content_verified = 1),
        sampled_policy_governance_verified INTEGER NOT NULL CHECK (sampled_policy_governance_verified = 1),
        governed_beacon_provenance_verified INTEGER NOT NULL CHECK (governed_beacon_provenance_verified = 1),
        public_future_availability_verified INTEGER NOT NULL CHECK (public_future_availability_verified = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_operational_finality_v4 (
        settlement_commitment BLOB NOT NULL PRIMARY KEY REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT,
        certificate_root BLOB NOT NULL UNIQUE CHECK (typeof(certificate_root) = 'blob' AND length(certificate_root) = 32),
        policy_root BLOB NOT NULL CHECK (typeof(policy_root) = 'blob' AND length(policy_root) = 32),
        proof_journal_hash BLOB NOT NULL UNIQUE CHECK (typeof(proof_journal_hash) = 'blob' AND length(proof_journal_hash) = 32),
        post_state_root BLOB NOT NULL UNIQUE CHECK (typeof(post_state_root) = 'blob' AND length(post_state_root) = 32),
        finality_evidence_root BLOB NOT NULL UNIQUE CHECK (typeof(finality_evidence_root) = 'blob' AND length(finality_evidence_root) = 32),
        prior_checkpoint_sequence_be BLOB NOT NULL CHECK (typeof(prior_checkpoint_sequence_be) = 'blob' AND length(prior_checkpoint_sequence_be) = 8),
        prior_checkpoint_hash BLOB NOT NULL CHECK (typeof(prior_checkpoint_hash) = 'blob' AND length(prior_checkpoint_hash) = 32),
        next_checkpoint_sequence_be BLOB NOT NULL UNIQUE CHECK (typeof(next_checkpoint_sequence_be) = 'blob' AND length(next_checkpoint_sequence_be) = 8),
        next_checkpoint_hash BLOB NOT NULL UNIQUE CHECK (typeof(next_checkpoint_hash) = 'blob' AND length(next_checkpoint_hash) = 32),
        exact_certificate BLOB NOT NULL CHECK (typeof(exact_certificate) = 'blob' AND length(exact_certificate) BETWEEN 1 AND 576),
        exact_finality_evidence BLOB NOT NULL CHECK (typeof(exact_finality_evidence) = 'blob' AND length(exact_finality_evidence) BETWEEN 1 AND 1048576),
        cryptographic_checkpoint_quorum_authenticated INTEGER NOT NULL CHECK (cryptographic_checkpoint_quorum_authenticated = 1),
        proof_receipt_authentication_established INTEGER NOT NULL CHECK (proof_receipt_authentication_established = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_settlement_replay_v4 (
        settlement_commitment BLOB NOT NULL PRIMARY KEY REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT,
        replay_material_root BLOB NOT NULL UNIQUE CHECK (typeof(replay_material_root) = 'blob' AND length(replay_material_root) = 32),
        exact_projection BLOB NOT NULL CHECK (typeof(exact_projection) = 'blob' AND length(exact_projection) BETWEEN 1 AND 65536),
        exact_header BLOB NOT NULL CHECK (typeof(exact_header) = 'blob' AND length(exact_header) BETWEEN 1 AND 262144),
        exact_body BLOB NOT NULL CHECK (typeof(exact_body) = 'blob' AND length(exact_body) BETWEEN 1 AND 1048576),
        exact_envelope BLOB NOT NULL CHECK (typeof(exact_envelope) = 'blob' AND length(exact_envelope) BETWEEN 1 AND 262144),
        exact_receipt BLOB NOT NULL CHECK (typeof(exact_receipt) = 'blob' AND length(exact_receipt) BETWEEN 1 AND 262144),
        exact_evidence BLOB NOT NULL CHECK (typeof(exact_evidence) = 'blob' AND length(exact_evidence) BETWEEN 1 AND 524288),
        exact_config_document BLOB NOT NULL CHECK (typeof(exact_config_document) = 'blob' AND length(exact_config_document) BETWEEN 1 AND 262144),
        exact_pre_state_snapshot BLOB NOT NULL CHECK (typeof(exact_pre_state_snapshot) = 'blob' AND length(exact_pre_state_snapshot) BETWEEN 1 AND 25165824),
        exact_parent_header BLOB CHECK (exact_parent_header IS NULL OR (typeof(exact_parent_header) = 'blob' AND length(exact_parent_header) BETWEEN 1 AND 262144)),
        replay_reverified_before_commit INTEGER NOT NULL CHECK (replay_reverified_before_commit = 1),
        proof_receipt_authentication_established INTEGER NOT NULL CHECK (proof_receipt_authentication_established = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
    """,
)

_V4_EXPECTED_SCHEMA_SQL = {
    **_V4_BASE_ECONOMIC_SCHEMA_SQL,
    "spot_v7_operational_policy_v4": _V4_SCHEMA_STATEMENTS[0],
    "spot_v7_operational_da_v4": _V4_SCHEMA_STATEMENTS[1],
    "spot_v7_operational_finality_v4": _V4_SCHEMA_STATEMENTS[2],
    "spot_v7_settlement_replay_v4": _V4_SCHEMA_STATEMENTS[3],
}


def _initialize_or_validate_spot_v7_store_v4(
    connection: sqlite3.Connection,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
    policy: _GovernedSpotV7OperationalPolicyV3,
    allow_initialize: bool = False,
) -> None:
    if not connection.in_transaction:
        raise ValueError("Spot V7 V4 initialization requires a transaction")
    _require_canonical_genesis_cells(genesis_cells)
    governed = _require_governed_operational_policy_v3(policy)
    projection = governed._projection_for_governed_da_v2()
    if (
        projection.application_id != identity.application_id
        or projection.chain_or_domain_id != identity.chain_or_domain_id
    ):
        raise ValueError("Spot V7 V4 policy does not match the store scope")
    existing = connection.execute(
        "SELECT name FROM sqlite_master WHERE name NOT LIKE 'sqlite_%'"
    ).fetchall()
    if not existing:
        if not allow_initialize:
            raise ValueError("empty Spot V7 V4 database cannot be reinitialized")
        _create_schema_v4(connection, identity=identity, genesis_cells=genesis_cells)
        _insert_policy_v4(connection, governed)
    _validate_spot_v7_schema_v4(connection)
    _validate_store_identity(connection, identity)
    _validate_genesis_cells(connection, genesis_cells)
    _validate_policy_v4(connection, governed)


def _create_schema_v4(
    connection: sqlite3.Connection,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
) -> None:
    _require_frozen_v4_base_schema()
    if int(connection.execute("PRAGMA application_id").fetchone()[0]) != 0:
        raise ValueError("empty Spot V7 V4 database has an application_id")
    if int(connection.execute("PRAGMA user_version").fetchone()[0]) != 0:
        raise ValueError("empty Spot V7 V4 database has a user_version")
    connection.execute(f"PRAGMA application_id = {SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1}")
    connection.execute(f"PRAGMA user_version = {SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V4}")
    for statement in _V4_EXPECTED_SCHEMA_SQL.values():
        connection.execute(statement)
    connection.execute(
        """
        INSERT INTO spot_v7_store_meta (
            singleton, schema_version, application_id, chain_or_domain_id,
            verified_program_id, verified_profile_id, verified_program_manifest_root,
            genesis_state_root, state_root, revision, settlement_count, cell_count,
            last_epoch_id_be, settlement_authority, production_authority,
            authority_blocked_reason
        ) VALUES (1, 4, ?, ?, ?, ?, ?, ?, ?, 0, 0, ?, NULL, 0, 0, ?)
        """,
        (
            _hash_bytes(identity.application_id, name="V4 store application_id"),
            _hash_bytes(identity.chain_or_domain_id, name="V4 store chain_or_domain_id"),
            _hash_bytes(identity.verified_program_id, name="V4 store verified_program_id"),
            _hash_bytes(identity.verified_profile_id, name="V4 store verified_profile_id"),
            _hash_bytes(
                identity.verified_program_manifest_root,
                name="V4 store verified_program_manifest_root",
            ),
            _hash_bytes(identity.genesis_state_root, name="V4 store genesis_state_root"),
            _hash_bytes(identity.genesis_state_root, name="V4 store state_root"),
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


def _validate_spot_v7_schema_v4(connection: sqlite3.Connection) -> None:
    _require_frozen_v4_base_schema()
    application_id = int(connection.execute("PRAGMA application_id").fetchone()[0])
    if application_id != SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1:
        raise ValueError("Spot V7 V4 store application_id mismatch")
    version = int(connection.execute("PRAGMA user_version").fetchone()[0])
    if version != SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V4:
        raise ValueError("Spot V7 V4 store user_version mismatch")
    rows = connection.execute(
        """
        SELECT type, name, sql FROM sqlite_master
        WHERE name NOT LIKE 'sqlite_%'
        ORDER BY type, name
        """
    ).fetchall()
    observed = {(str(row["type"]), str(row["name"])) for row in rows}
    expected = {("table", name) for name in _V4_EXPECTED_SCHEMA_SQL}
    if observed != expected:
        raise ValueError("Spot V7 V4 schema object set mismatch")
    for row in rows:
        name = str(row["name"])
        if _normalize_sql(str(row["sql"])) != _normalize_sql(_V4_EXPECTED_SCHEMA_SQL[name]):
            raise ValueError(f"Spot V7 V4 schema SQL mismatch for {name}")
    meta = connection.execute(
        "SELECT schema_version FROM spot_v7_store_meta WHERE singleton = 1"
    ).fetchone()
    if meta is None or int(meta[0]) != SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V4:
        raise ValueError("Spot V7 V4 metadata schema version mismatch")


def _require_frozen_v4_base_schema() -> None:
    payload = "\n".join(
        f"{name}\0{_normalize_sql(statement)}"
        for name, statement in _V4_BASE_ECONOMIC_SCHEMA_SQL.items()
    ).encode("utf-8")
    if hashlib.sha256(payload).hexdigest() != SPOT_V7_V4_BASE_ECONOMIC_SCHEMA_SHA256:
        raise ValueError("Spot V7 V4 frozen economic-base schema digest mismatch")


def _insert_policy_v4(
    connection: sqlite3.Connection,
    policy: _GovernedSpotV7OperationalPolicyV3,
) -> None:
    projection = policy._projection_for_governed_da_v2()
    provenance = policy._provenance_for_governed_da_v2()
    store_policy = policy._base_store_policy_for_finality_v3()
    connection.execute(
        """
        INSERT INTO spot_v7_operational_policy_v4 (
            singleton, application_id, chain_or_domain_id, zeno_ledger_chain_id,
            full_blob_policy_root, sampled_policy_root, beacon_policy_root,
            checkpoint_finality_policy_root, beacon_source_finality_policy_root,
            policy_provenance_root,
            manifest_sha256, exact_policy_evidence,
            current_checkpoint_sequence_be, current_checkpoint_hash,
            current_release_head_verified, release_authority,
            settlement_authority, production_authority
        ) VALUES (1, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0, 0)
        """,
        (
            _hash_bytes(projection.application_id, name="V4 policy application"),
            _hash_bytes(projection.chain_or_domain_id, name="V4 policy domain"),
            projection.zeno_ledger_chain_id,
            _hash_bytes(projection.full_blob_da_policy_root, name="V4 full blob policy"),
            _hash_bytes(projection.sampled_policy_root, name="V4 sampled policy"),
            _hash_bytes(projection.beacon_policy_root, name="V4 beacon policy"),
            _hash_bytes(
                projection.checkpoint_finality_policy_root,
                name="V4 finality policy",
            ),
            _hash_bytes(
                projection.beacon_source_finality_policy_root,
                name="V4 beacon source finality policy",
            ),
            _hash_bytes(provenance.evidence_root, name="V4 policy provenance"),
            bytes.fromhex(provenance.manifest_sha256),
            provenance.exact_evidence_bytes,
            store_policy.genesis_application_checkpoint_sequence.to_bytes(8, "big"),
            _root_bytes_allow_zero(
                store_policy.genesis_application_checkpoint_hash,
                name="V4 genesis checkpoint",
            ),
        ),
    )


def _validate_policy_v4(
    connection: sqlite3.Connection,
    policy: _GovernedSpotV7OperationalPolicyV3,
) -> None:
    row = connection.execute(
        "SELECT * FROM spot_v7_operational_policy_v4 WHERE singleton = 1"
    ).fetchone()
    if row is None:
        raise ValueError("Spot V7 V4 policy row is missing")
    projection = policy._projection_for_governed_da_v2()
    provenance = policy._provenance_for_governed_da_v2()
    expected = {
        "application_id": _hash_bytes(projection.application_id, name="policy application"),
        "chain_or_domain_id": _hash_bytes(projection.chain_or_domain_id, name="policy domain"),
        "full_blob_policy_root": _hash_bytes(
            projection.full_blob_da_policy_root,
            name="full blob policy",
        ),
        "sampled_policy_root": _hash_bytes(projection.sampled_policy_root, name="sampled policy"),
        "beacon_policy_root": _hash_bytes(projection.beacon_policy_root, name="beacon policy"),
        "checkpoint_finality_policy_root": _hash_bytes(
            projection.checkpoint_finality_policy_root,
            name="finality policy",
        ),
        "beacon_source_finality_policy_root": _hash_bytes(
            projection.beacon_source_finality_policy_root,
            name="beacon source finality policy",
        ),
        "policy_provenance_root": _hash_bytes(
            provenance.evidence_root,
            name="policy provenance",
        ),
        "manifest_sha256": bytes.fromhex(provenance.manifest_sha256),
        "exact_policy_evidence": provenance.exact_evidence_bytes,
    }
    for field, value in expected.items():
        if bytes(row[field]) != value:
            raise ValueError(f"Spot V7 V4 policy mismatch: {field}")
    if str(row["zeno_ledger_chain_id"]) != projection.zeno_ledger_chain_id:
        raise ValueError("Spot V7 V4 policy chain ID mismatch")
    meta = connection.execute(
        "SELECT revision FROM spot_v7_store_meta WHERE singleton = 1"
    ).fetchone()
    if meta is None:
        raise ValueError("Spot V7 V4 metadata row is missing")
    if int(meta["revision"]) == 0:
        store_policy = policy._base_store_policy_for_finality_v3()
        if int.from_bytes(bytes(row["current_checkpoint_sequence_be"]), "big") != (
            store_policy.genesis_application_checkpoint_sequence
        ):
            raise ValueError("Spot V7 V4 empty-store checkpoint sequence mismatch")
        if bytes(row["current_checkpoint_hash"]) != _root_bytes_allow_zero(
            store_policy.genesis_application_checkpoint_hash,
            name="V4 genesis checkpoint",
        ):
            raise ValueError("Spot V7 V4 empty-store checkpoint hash mismatch")
    for field in (
        "current_release_head_verified",
        "release_authority",
        "settlement_authority",
        "production_authority",
    ):
        if int(row[field]) != 0:
            raise ValueError(f"Spot V7 V4 policy nonclaim mismatch: {field}")


__all__ = ()
