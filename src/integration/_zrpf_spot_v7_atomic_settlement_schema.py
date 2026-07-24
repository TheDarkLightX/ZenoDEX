"""Strict SQLite schema for authority-false Spot V7 atomic settlement mechanics."""

from __future__ import annotations

import sqlite3

from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    SpotV7AtomicSettlementCursorV1,
    SpotV7AtomicSettlementStoreIdentityV1,
    SpotV7CellKindV1,
    SpotV7CellOpeningV1,
    _hash_bytes,
    _hex_hash,
)

SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V2 = 2
SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1 = 0x5A535637

_SCHEMA_STATEMENTS = (
    """
    CREATE TABLE spot_v7_store_meta (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        schema_version INTEGER NOT NULL CHECK (schema_version = 2),
        application_id BLOB NOT NULL CHECK (typeof(application_id) = 'blob' AND length(application_id) = 32),
        chain_or_domain_id BLOB NOT NULL CHECK (typeof(chain_or_domain_id) = 'blob' AND length(chain_or_domain_id) = 32),
        verified_program_id BLOB NOT NULL CHECK (typeof(verified_program_id) = 'blob' AND length(verified_program_id) = 32),
        verified_profile_id BLOB NOT NULL CHECK (typeof(verified_profile_id) = 'blob' AND length(verified_profile_id) = 32),
        verified_program_manifest_root BLOB NOT NULL CHECK (typeof(verified_program_manifest_root) = 'blob' AND length(verified_program_manifest_root) = 32),
        genesis_state_root BLOB NOT NULL CHECK (typeof(genesis_state_root) = 'blob' AND length(genesis_state_root) = 32),
        state_root BLOB NOT NULL CHECK (typeof(state_root) = 'blob' AND length(state_root) = 32),
        revision INTEGER NOT NULL CHECK (revision BETWEEN 0 AND 1048576),
        settlement_count INTEGER NOT NULL CHECK (settlement_count BETWEEN 0 AND 1048576),
        cell_count INTEGER NOT NULL CHECK (cell_count BETWEEN 1 AND 1048576),
        last_epoch_id_be BLOB CHECK (last_epoch_id_be IS NULL OR (typeof(last_epoch_id_be) = 'blob' AND length(last_epoch_id_be) = 8)),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0),
        authority_blocked_reason TEXT NOT NULL,
        CHECK (revision = settlement_count),
        CHECK ((revision = 0 AND last_epoch_id_be IS NULL) OR (revision > 0 AND last_epoch_id_be IS NOT NULL))
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_genesis_cells (
        cell_key BLOB NOT NULL PRIMARY KEY CHECK (typeof(cell_key) = 'blob' AND length(cell_key) = 32),
        kind INTEGER NOT NULL CHECK (kind IN (1, 2)),
        subject_id BLOB NOT NULL CHECK ((kind = 1 AND length(subject_id) = 48) OR (kind = 2 AND length(subject_id) = 32)),
        asset_id BLOB NOT NULL CHECK (typeof(asset_id) = 'blob' AND length(asset_id) = 32),
        atoms_be BLOB NOT NULL CHECK (typeof(atoms_be) = 'blob' AND length(atoms_be) = 16),
        value_hash BLOB NOT NULL CHECK (typeof(value_hash) = 'blob' AND length(value_hash) = 32),
        UNIQUE (kind, subject_id, asset_id)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_cells (
        cell_key BLOB NOT NULL PRIMARY KEY CHECK (typeof(cell_key) = 'blob' AND length(cell_key) = 32),
        kind INTEGER NOT NULL CHECK (kind IN (1, 2)),
        subject_id BLOB NOT NULL CHECK ((kind = 1 AND length(subject_id) = 48) OR (kind = 2 AND length(subject_id) = 32)),
        asset_id BLOB NOT NULL CHECK (typeof(asset_id) = 'blob' AND length(asset_id) = 32),
        atoms_be BLOB NOT NULL CHECK (typeof(atoms_be) = 'blob' AND length(atoms_be) = 16),
        value_hash BLOB NOT NULL CHECK (typeof(value_hash) = 'blob' AND length(value_hash) = 32),
        updated_revision INTEGER NOT NULL CHECK (updated_revision BETWEEN 0 AND 1048576),
        UNIQUE (kind, subject_id, asset_id)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_settlements (
        settlement_commitment BLOB NOT NULL PRIMARY KEY CHECK (typeof(settlement_commitment) = 'blob' AND length(settlement_commitment) = 32),
        revision INTEGER NOT NULL UNIQUE CHECK (revision BETWEEN 1 AND 1048576),
        epoch_id_be BLOB NOT NULL UNIQUE CHECK (typeof(epoch_id_be) = 'blob' AND length(epoch_id_be) = 8),
        previous_state_root BLOB NOT NULL CHECK (typeof(previous_state_root) = 'blob' AND length(previous_state_root) = 32),
        result_state_root BLOB NOT NULL UNIQUE CHECK (typeof(result_state_root) = 'blob' AND length(result_state_root) = 32),
        receipt_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(receipt_sha256) = 'blob' AND length(receipt_sha256) = 32),
        journal_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(journal_sha256) = 'blob' AND length(journal_sha256) = 32),
        firecracker_execution_record_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(firecracker_execution_record_sha256) = 'blob' AND length(firecracker_execution_record_sha256) = 32),
        firecracker_output_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(firecracker_output_sha256) = 'blob' AND length(firecracker_output_sha256) = 32),
        plan_b_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(plan_b_sha256) = 'blob' AND length(plan_b_sha256) = 32),
        verified_program_id BLOB NOT NULL CHECK (typeof(verified_program_id) = 'blob' AND length(verified_program_id) = 32),
        verified_profile_id BLOB NOT NULL CHECK (typeof(verified_profile_id) = 'blob' AND length(verified_profile_id) = 32),
        verified_program_manifest_root BLOB NOT NULL CHECK (typeof(verified_program_manifest_root) = 'blob' AND length(verified_program_manifest_root) = 32),
        source_child_claim_binding BLOB NOT NULL UNIQUE CHECK (typeof(source_child_claim_binding) = 'blob' AND length(source_child_claim_binding) = 32),
        source_child_journal_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(source_child_journal_sha256) = 'blob' AND length(source_child_journal_sha256) = 32),
        data_availability_certificate_root BLOB NOT NULL CHECK (typeof(data_availability_certificate_root) = 'blob' AND length(data_availability_certificate_root) = 32),
        data_root BLOB NOT NULL CHECK (typeof(data_root) = 'blob' AND length(data_root) = 32),
        settlement_effect_plan_commitment BLOB NOT NULL UNIQUE CHECK (typeof(settlement_effect_plan_commitment) = 'blob' AND length(settlement_effect_plan_commitment) = 32),
        cell_transitions_root BLOB NOT NULL CHECK (typeof(cell_transitions_root) = 'blob' AND length(cell_transitions_root) = 32),
        exact_v7_receipt BLOB NOT NULL CHECK (typeof(exact_v7_receipt) = 'blob' AND length(exact_v7_receipt) BETWEEN 1 AND 16777216),
        exact_v7_journal BLOB NOT NULL CHECK (typeof(exact_v7_journal) = 'blob' AND length(exact_v7_journal) BETWEEN 1 AND 65536),
        exact_plan_b BLOB NOT NULL CHECK (typeof(exact_plan_b) = 'blob' AND length(exact_plan_b) BETWEEN 1 AND 524288),
        exact_firecracker_execution_record BLOB NOT NULL CHECK (typeof(exact_firecracker_execution_record) = 'blob' AND length(exact_firecracker_execution_record) BETWEEN 1 AND 1048576),
        exact_firecracker_output BLOB NOT NULL CHECK (typeof(exact_firecracker_output) = 'blob' AND length(exact_firecracker_output) BETWEEN 1 AND 65536),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0),
        firecracker_execution_verified INTEGER NOT NULL CHECK (firecracker_execution_verified = 0),
        authority_blocked_reason TEXT NOT NULL
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_cell_transitions (
        settlement_commitment BLOB NOT NULL REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 3),
        cell_key BLOB NOT NULL CHECK (typeof(cell_key) = 'blob' AND length(cell_key) = 32),
        kind INTEGER NOT NULL CHECK (kind IN (1, 2)),
        role INTEGER NOT NULL CHECK (role IN (1, 2)),
        subject_id BLOB NOT NULL CHECK ((kind = 1 AND length(subject_id) = 48) OR (kind = 2 AND length(subject_id) = 32)),
        asset_id BLOB NOT NULL CHECK (typeof(asset_id) = 'blob' AND length(asset_id) = 32),
        pre_atoms_be BLOB NOT NULL CHECK (typeof(pre_atoms_be) = 'blob' AND length(pre_atoms_be) = 16),
        post_atoms_be BLOB NOT NULL CHECK (typeof(post_atoms_be) = 'blob' AND length(post_atoms_be) = 16),
        pre_value_hash BLOB NOT NULL CHECK (typeof(pre_value_hash) = 'blob' AND length(pre_value_hash) = 32),
        post_value_hash BLOB NOT NULL CHECK (typeof(post_value_hash) = 'blob' AND length(post_value_hash) = 32),
        amount_atoms_be BLOB NOT NULL CHECK (typeof(amount_atoms_be) = 'blob' AND length(amount_atoms_be) = 16),
        transition_commitment BLOB NOT NULL CHECK (typeof(transition_commitment) = 'blob' AND length(transition_commitment) = 32),
        PRIMARY KEY (settlement_commitment, ordinal),
        UNIQUE (settlement_commitment, cell_key)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_asset_effects (
        effect_id BLOB NOT NULL PRIMARY KEY CHECK (typeof(effect_id) = 'blob' AND length(effect_id) = 32),
        settlement_commitment BLOB NOT NULL REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 1),
        economic_action_id BLOB NOT NULL CHECK (typeof(economic_action_id) = 'blob' AND length(economic_action_id) = 32),
        asset_id BLOB NOT NULL CHECK (typeof(asset_id) = 'blob' AND length(asset_id) = 32),
        amount_atoms_be BLOB NOT NULL CHECK (typeof(amount_atoms_be) = 'blob' AND length(amount_atoms_be) = 16),
        UNIQUE (settlement_commitment, ordinal),
        UNIQUE (settlement_commitment, asset_id)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_economic_actions (
        economic_action_id BLOB NOT NULL PRIMARY KEY CHECK (typeof(economic_action_id) = 'blob' AND length(economic_action_id) = 32),
        settlement_commitment BLOB NOT NULL UNIQUE REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_authorization_nullifiers (
        authorization_nullifier BLOB NOT NULL PRIMARY KEY CHECK (typeof(authorization_nullifier) = 'blob' AND length(authorization_nullifier) = 32),
        settlement_commitment BLOB NOT NULL UNIQUE REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_authorization_grant_spends (
        authorization_grant_spend_nullifier BLOB NOT NULL PRIMARY KEY CHECK (typeof(authorization_grant_spend_nullifier) = 'blob' AND length(authorization_grant_spend_nullifier) = 32),
        settlement_commitment BLOB NOT NULL UNIQUE REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_consumed_objects (
        consumed_object_id BLOB NOT NULL PRIMARY KEY CHECK (typeof(consumed_object_id) = 'blob' AND length(consumed_object_id) = 32),
        settlement_commitment BLOB NOT NULL REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 63),
        UNIQUE (settlement_commitment, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_operational_policy (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        application_id BLOB NOT NULL CHECK (typeof(application_id) = 'blob' AND length(application_id) = 32),
        chain_or_domain_id BLOB NOT NULL CHECK (typeof(chain_or_domain_id) = 'blob' AND length(chain_or_domain_id) = 32),
        data_schema_id BLOB NOT NULL CHECK (typeof(data_schema_id) = 'blob' AND length(data_schema_id) = 32),
        storage_policy_hash BLOB NOT NULL CHECK (typeof(storage_policy_hash) = 'blob' AND length(storage_policy_hash) = 32),
        minimum_retention_epochs_be BLOB NOT NULL CHECK (typeof(minimum_retention_epochs_be) = 'blob' AND length(minimum_retention_epochs_be) = 8),
        minimum_remaining_epochs_be BLOB NOT NULL CHECK (typeof(minimum_remaining_epochs_be) = 'blob' AND length(minimum_remaining_epochs_be) = 8),
        maximum_blob_bytes INTEGER NOT NULL CHECK (maximum_blob_bytes BETWEEN 1 AND 8388608),
        full_blob_policy_root BLOB NOT NULL UNIQUE CHECK (typeof(full_blob_policy_root) = 'blob' AND length(full_blob_policy_root) = 32),
        finality_network_id BLOB NOT NULL CHECK (typeof(finality_network_id) = 'blob' AND length(finality_network_id) = 32),
        finality_protocol_id BLOB NOT NULL CHECK (typeof(finality_protocol_id) = 'blob' AND length(finality_protocol_id) = 32),
        external_finality_policy_hash BLOB NOT NULL CHECK (typeof(external_finality_policy_hash) = 'blob' AND length(external_finality_policy_hash) = 32),
        finality_verifier_set_root BLOB NOT NULL CHECK (typeof(finality_verifier_set_root) = 'blob' AND length(finality_verifier_set_root) = 32),
        checkpoint_finality_policy_root BLOB NOT NULL UNIQUE CHECK (typeof(checkpoint_finality_policy_root) = 'blob' AND length(checkpoint_finality_policy_root) = 32),
        genesis_checkpoint_sequence_be BLOB NOT NULL CHECK (typeof(genesis_checkpoint_sequence_be) = 'blob' AND length(genesis_checkpoint_sequence_be) = 8),
        genesis_checkpoint_hash BLOB NOT NULL CHECK (typeof(genesis_checkpoint_hash) = 'blob' AND length(genesis_checkpoint_hash) = 32),
        current_checkpoint_sequence_be BLOB NOT NULL CHECK (typeof(current_checkpoint_sequence_be) = 'blob' AND length(current_checkpoint_sequence_be) = 8),
        current_checkpoint_hash BLOB NOT NULL CHECK (typeof(current_checkpoint_hash) = 'blob' AND length(current_checkpoint_hash) = 32),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_operational_da (
        settlement_commitment BLOB NOT NULL PRIMARY KEY REFERENCES spot_v7_settlements(settlement_commitment) ON DELETE RESTRICT,
        certificate_root BLOB NOT NULL UNIQUE CHECK (typeof(certificate_root) = 'blob' AND length(certificate_root) = 32),
        data_root BLOB NOT NULL CHECK (typeof(data_root) = 'blob' AND length(data_root) = 32),
        policy_root BLOB NOT NULL CHECK (typeof(policy_root) = 'blob' AND length(policy_root) = 32),
        checked_epoch_be BLOB NOT NULL CHECK (typeof(checked_epoch_be) = 'blob' AND length(checked_epoch_be) = 8),
        retention_through_epoch_be BLOB NOT NULL CHECK (typeof(retention_through_epoch_be) = 'blob' AND length(retention_through_epoch_be) = 8),
        blob_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(blob_sha256) = 'blob' AND length(blob_sha256) = 32),
        certificate_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(certificate_sha256) = 'blob' AND length(certificate_sha256) = 32),
        exact_blob BLOB NOT NULL CHECK (typeof(exact_blob) = 'blob' AND length(exact_blob) BETWEEN 1 AND 8388608),
        exact_certificate BLOB NOT NULL CHECK (typeof(exact_certificate) = 'blob' AND length(exact_certificate) BETWEEN 1 AND 512),
        provider_retrievability_verified INTEGER NOT NULL CHECK (provider_retrievability_verified = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_operational_finality (
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
        certificate_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(certificate_sha256) = 'blob' AND length(certificate_sha256) = 32),
        evidence_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(evidence_sha256) = 'blob' AND length(evidence_sha256) = 32),
        exact_certificate BLOB NOT NULL CHECK (typeof(exact_certificate) = 'blob' AND length(exact_certificate) BETWEEN 1 AND 576),
        exact_finality_evidence BLOB NOT NULL CHECK (typeof(exact_finality_evidence) = 'blob' AND length(exact_finality_evidence) BETWEEN 1 AND 1048576),
        external_finality_authenticated INTEGER NOT NULL CHECK (external_finality_authenticated = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
    """,
)

_EXPECTED_SCHEMA_SQL = {
    "spot_v7_store_meta": _SCHEMA_STATEMENTS[0],
    "spot_v7_genesis_cells": _SCHEMA_STATEMENTS[1],
    "spot_v7_cells": _SCHEMA_STATEMENTS[2],
    "spot_v7_settlements": _SCHEMA_STATEMENTS[3],
    "spot_v7_cell_transitions": _SCHEMA_STATEMENTS[4],
    "spot_v7_asset_effects": _SCHEMA_STATEMENTS[5],
    "spot_v7_economic_actions": _SCHEMA_STATEMENTS[6],
    "spot_v7_authorization_nullifiers": _SCHEMA_STATEMENTS[7],
    "spot_v7_authorization_grant_spends": _SCHEMA_STATEMENTS[8],
    "spot_v7_consumed_objects": _SCHEMA_STATEMENTS[9],
    "spot_v7_operational_policy": _SCHEMA_STATEMENTS[10],
    "spot_v7_operational_da": _SCHEMA_STATEMENTS[11],
    "spot_v7_operational_finality": _SCHEMA_STATEMENTS[12],
}


def _initialize_or_validate_spot_v7_store(
    connection: sqlite3.Connection,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
) -> None:
    if not connection.in_transaction:
        raise ValueError("Spot V7 store initialization requires an existing transaction")
    _require_canonical_genesis_cells(genesis_cells)
    existing = connection.execute(
        "SELECT name FROM sqlite_master WHERE name NOT LIKE 'sqlite_%'"
    ).fetchall()
    if not existing:
        _create_schema(connection, identity=identity, genesis_cells=genesis_cells)
    _validate_spot_v7_schema(connection)
    _validate_store_identity(connection, identity)
    _validate_genesis_cells(connection, genesis_cells)


def _create_schema(
    connection: sqlite3.Connection,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    genesis_cells: tuple[SpotV7CellOpeningV1, ...],
) -> None:
    if connection.execute("PRAGMA application_id").fetchone()[0] != 0:
        raise ValueError("empty Spot V7 database has an application_id")
    if connection.execute("PRAGMA user_version").fetchone()[0] != 0:
        raise ValueError("empty Spot V7 database has a user_version")
    connection.execute(f"PRAGMA application_id = {SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1}")
    connection.execute(f"PRAGMA user_version = {SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V2}")
    for statement in _SCHEMA_STATEMENTS:
        connection.execute(statement)
    connection.execute(
        """
        INSERT INTO spot_v7_store_meta (
            singleton, schema_version, application_id, chain_or_domain_id,
            verified_program_id, verified_profile_id, verified_program_manifest_root,
            genesis_state_root, state_root, revision, settlement_count, cell_count,
            last_epoch_id_be, settlement_authority, production_authority,
            authority_blocked_reason
        ) VALUES (1, 2, ?, ?, ?, ?, ?, ?, ?, 0, 0, ?, NULL, 0, 0, ?)
        """,
        (
            _hash_bytes(identity.application_id, name="store application_id"),
            _hash_bytes(identity.chain_or_domain_id, name="store chain_or_domain_id"),
            _hash_bytes(identity.verified_program_id, name="store verified_program_id"),
            _hash_bytes(identity.verified_profile_id, name="store verified_profile_id"),
            _hash_bytes(
                identity.verified_program_manifest_root,
                name="store verified_program_manifest_root",
            ),
            _hash_bytes(identity.genesis_state_root, name="store genesis_state_root"),
            _hash_bytes(identity.genesis_state_root, name="store state_root"),
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


def _validate_spot_v7_schema(connection: sqlite3.Connection) -> None:
    if (
        connection.execute("PRAGMA application_id").fetchone()[0]
        != SPOT_V7_ATOMIC_SETTLEMENT_APPLICATION_ID_V1
    ):
        raise ValueError("Spot V7 store application_id mismatch")
    if (
        connection.execute("PRAGMA user_version").fetchone()[0]
        != SPOT_V7_ATOMIC_SETTLEMENT_SCHEMA_VERSION_V2
    ):
        raise ValueError("Spot V7 store user_version mismatch")
    rows = connection.execute(
        """
        SELECT type, name, sql FROM sqlite_master
        WHERE name NOT LIKE 'sqlite_%'
        ORDER BY type, name
        """
    ).fetchall()
    observed = {(str(row["type"]), str(row["name"])) for row in rows}
    expected = {("table", name) for name in _EXPECTED_SCHEMA_SQL}
    if observed != expected:
        raise ValueError("Spot V7 store schema object set mismatch")
    for row in rows:
        name = str(row["name"])
        if _normalize_sql(str(row["sql"])) != _normalize_sql(_EXPECTED_SCHEMA_SQL[name]):
            raise ValueError(f"Spot V7 store schema SQL mismatch for {name}")


def _validate_store_identity(
    connection: sqlite3.Connection,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
) -> None:
    row = connection.execute("SELECT * FROM spot_v7_store_meta WHERE singleton = 1").fetchone()
    if row is None:
        raise ValueError("Spot V7 store metadata row is missing")
    expected = {
        "application_id": identity.application_id,
        "chain_or_domain_id": identity.chain_or_domain_id,
        "verified_program_id": identity.verified_program_id,
        "verified_profile_id": identity.verified_profile_id,
        "verified_program_manifest_root": identity.verified_program_manifest_root,
        "genesis_state_root": identity.genesis_state_root,
    }
    for name, value in expected.items():
        if bytes(row[name]) != _hash_bytes(value, name=f"expected store {name}"):
            raise ValueError(f"Spot V7 store identity mismatch: {name}")
    if (
        int(row["settlement_authority"]) != 0
        or int(row["production_authority"]) != 0
        or str(row["authority_blocked_reason"])
        != SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1
    ):
        raise ValueError("Spot V7 store authority non-claim mismatch")


def _validate_genesis_cells(
    connection: sqlite3.Connection,
    expected: tuple[SpotV7CellOpeningV1, ...],
) -> None:
    rows = connection.execute("SELECT * FROM spot_v7_genesis_cells ORDER BY cell_key").fetchall()
    observed = tuple(_opening_from_row(row) for row in rows)
    if observed != expected:
        raise ValueError("Spot V7 store genesis cells mismatch")


def _read_spot_v7_cursor(connection: sqlite3.Connection) -> SpotV7AtomicSettlementCursorV1:
    row = connection.execute(
        """
        SELECT revision, state_root, settlement_count, cell_count, last_epoch_id_be
        FROM spot_v7_store_meta WHERE singleton = 1
        """
    ).fetchone()
    if row is None:
        raise ValueError("Spot V7 store metadata row is missing")
    encoded_epoch = row["last_epoch_id_be"]
    return SpotV7AtomicSettlementCursorV1(
        revision=int(row["revision"]),
        state_root=_hex_hash(bytes(row["state_root"])),
        settlement_count=int(row["settlement_count"]),
        cell_count=int(row["cell_count"]),
        last_epoch_id=(
            None if encoded_epoch is None else int.from_bytes(bytes(encoded_epoch), "big")
        ),
    )


def _read_current_cells(connection: sqlite3.Connection) -> tuple[SpotV7CellOpeningV1, ...]:
    rows = connection.execute("SELECT * FROM spot_v7_cells ORDER BY cell_key").fetchall()
    return tuple(_opening_from_row(row) for row in rows)


def _require_canonical_genesis_cells(cells: tuple[SpotV7CellOpeningV1, ...]) -> None:
    if type(cells) is not tuple or not cells:
        raise ValueError("Spot V7 genesis cells must be a nonempty tuple")
    if any(type(cell) is not SpotV7CellOpeningV1 for cell in cells):
        raise TypeError("Spot V7 genesis cells must be exact SpotV7CellOpeningV1 values")
    keys = tuple(cell.cell_key for cell in cells)
    if keys != tuple(sorted(keys)) or len(set(keys)) != len(keys):
        raise ValueError("Spot V7 genesis cells must be sorted by unique cell key")


def _opening_storage_row(cell: SpotV7CellOpeningV1) -> tuple[object, ...]:
    subject = bytes.fromhex(cell.subject_id[2:])
    return (
        _hash_bytes(cell.cell_key, name="stored cell key"),
        cell.kind.value,
        subject,
        _hash_bytes(cell.asset_id, name="stored cell asset"),
        cell.atoms.to_bytes(16, "big"),
        _hash_bytes(cell.value_hash, name="stored cell value hash"),
    )


def _opening_from_row(row: sqlite3.Row) -> SpotV7CellOpeningV1:
    if not isinstance(row, sqlite3.Row):
        raise TypeError("stored Spot V7 cell row must be sqlite3.Row")
    kind = SpotV7CellKindV1(int(row["kind"]))
    opening = SpotV7CellOpeningV1(
        kind=kind,
        subject_id="0x" + bytes(row["subject_id"]).hex(),
        asset_id=_hex_hash(bytes(row["asset_id"])),
        atoms=int.from_bytes(bytes(row["atoms_be"]), "big"),
    )
    if opening.cell_key != _hex_hash(bytes(row["cell_key"])):
        raise ValueError("stored Spot V7 cell key mismatch")
    if opening.value_hash != _hex_hash(bytes(row["value_hash"])):
        raise ValueError("stored Spot V7 cell value hash mismatch")
    return opening


def _normalize_sql(value: str) -> str:
    return " ".join(value.strip().removesuffix(";").split())
