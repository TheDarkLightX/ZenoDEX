"""Exact embeddable SQLite schema for unified Spot V7 release history.

The tables in this module are designed to live in the same SQLite database as
the future Spot V7 economic store.  They deliberately retain every authority
flag as zero.  A canonical imported watermark is an observation until a
protocol adapter authenticates an externally monotonic anchor.
"""

from __future__ import annotations

import sqlite3
from typing import Final

SPOT_V7_RELEASE_STATE_SCHEMA_VERSION_V7: Final = 7
SPOT_V7_RETIRED_SOURCE_USER_VERSION_V7: Final = 307

_RELEASE_STATE_SCHEMA_V7: Final = """
    CREATE TABLE spot_v7_release_state_v7 (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        schema_version INTEGER NOT NULL CHECK (schema_version = 7),
        store_identity_bytes BLOB NOT NULL CHECK (typeof(store_identity_bytes) = 'blob' AND length(store_identity_bytes) BETWEEN 1 AND 32768),
        store_identity_sha256 BLOB NOT NULL CHECK (typeof(store_identity_sha256) = 'blob' AND length(store_identity_sha256) = 32),
        database_revision_be BLOB NOT NULL CHECK (typeof(database_revision_be) = 'blob' AND length(database_revision_be) = 8),
        release_state_root BLOB NOT NULL CHECK (typeof(release_state_root) = 'blob' AND length(release_state_root) = 32),
        event_count INTEGER NOT NULL CHECK (event_count BETWEEN 0 AND 4096),
        last_evaluation_epoch_be BLOB CHECK (last_evaluation_epoch_be IS NULL OR (typeof(last_evaluation_epoch_be) = 'blob' AND length(last_evaluation_epoch_be) = 8)),
        current_candidate_id BLOB CHECK (current_candidate_id IS NULL OR (typeof(current_candidate_id) = 'blob' AND length(current_candidate_id) = 32)),
        current_candidate_sha256 BLOB CHECK (current_candidate_sha256 IS NULL OR (typeof(current_candidate_sha256) = 'blob' AND length(current_candidate_sha256) = 32)),
        current_release_revision_be BLOB CHECK (current_release_revision_be IS NULL OR (typeof(current_release_revision_be) = 'blob' AND length(current_release_revision_be) = 8)),
        current_select_input_id BLOB CHECK (current_select_input_id IS NULL OR (typeof(current_select_input_id) = 'blob' AND length(current_select_input_id) = 32)),
        current_revocation_record_id BLOB CHECK (current_revocation_record_id IS NULL OR (typeof(current_revocation_record_id) = 'blob' AND length(current_revocation_record_id) = 32)),
        imported_final_revision_be BLOB NOT NULL CHECK (typeof(imported_final_revision_be) = 'blob' AND length(imported_final_revision_be) = 8),
        cutover_id BLOB NOT NULL UNIQUE CHECK (typeof(cutover_id) = 'blob' AND length(cutover_id) = 32),
        external_backend_id TEXT NOT NULL CHECK (typeof(external_backend_id) = 'text' AND length(external_backend_id) BETWEEN 1 AND 128),
        external_anchor_position_be BLOB NOT NULL CHECK (typeof(external_anchor_position_be) = 'blob' AND length(external_anchor_position_be) = 8),
        external_anchor_commitment BLOB NOT NULL CHECK (typeof(external_anchor_commitment) = 'blob' AND length(external_anchor_commitment) = 32),
        external_anchor_parent_commitment BLOB NOT NULL CHECK (typeof(external_anchor_parent_commitment) = 'blob' AND length(external_anchor_parent_commitment) = 32),
        external_anchor_watermark_hash BLOB NOT NULL CHECK (typeof(external_anchor_watermark_hash) = 'blob' AND length(external_anchor_watermark_hash) = 32),
        cutover_complete INTEGER NOT NULL CHECK (cutover_complete = 1),
        old_store_retired INTEGER NOT NULL CHECK (old_store_retired = 1),
        release_event_writer_active INTEGER NOT NULL CHECK (release_event_writer_active = 1),
        release_governed_trust_roots_authenticated INTEGER NOT NULL CHECK (release_governed_trust_roots_authenticated = 0),
        external_monotonic_anchor_authenticated INTEGER NOT NULL CHECK (external_monotonic_anchor_authenticated = 0),
        currentness_at_settlement_verified INTEGER NOT NULL CHECK (currentness_at_settlement_verified = 0),
        proof_receipt_authority INTEGER NOT NULL CHECK (proof_receipt_authority = 0),
        runtime_authority INTEGER NOT NULL CHECK (runtime_authority = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0),
        CHECK (
            (event_count = 0 AND last_evaluation_epoch_be IS NULL AND current_candidate_id IS NULL AND current_candidate_sha256 IS NULL AND current_release_revision_be IS NULL AND current_select_input_id IS NULL AND current_revocation_record_id IS NULL)
            OR
            (event_count > 0 AND last_evaluation_epoch_be IS NOT NULL AND current_candidate_id IS NOT NULL AND current_candidate_sha256 IS NOT NULL AND current_release_revision_be IS NOT NULL AND current_select_input_id IS NOT NULL)
        ),
        CHECK (database_revision_be >= imported_final_revision_be)
    ) STRICT, WITHOUT ROWID
"""

_RELEASE_EVENTS_SCHEMA_V7: Final = """
    CREATE TABLE spot_v7_release_events_v7 (
        event_revision_be BLOB NOT NULL PRIMARY KEY CHECK (typeof(event_revision_be) = 'blob' AND length(event_revision_be) = 8),
        event_origin TEXT NOT NULL CHECK (event_origin IN ('IMPORTED_V3', 'NATIVE_V7')),
        imported_cutover_id BLOB CHECK (imported_cutover_id IS NULL OR (typeof(imported_cutover_id) = 'blob' AND length(imported_cutover_id) = 32)),
        event_kind TEXT NOT NULL CHECK (event_kind IN ('SELECT', 'REVOKE')),
        selector_input_id BLOB NOT NULL UNIQUE CHECK (typeof(selector_input_id) = 'blob' AND length(selector_input_id) = 32),
        selector_input_bytes BLOB NOT NULL CHECK (typeof(selector_input_bytes) = 'blob' AND length(selector_input_bytes) = 320),
        candidate_id BLOB NOT NULL CHECK (typeof(candidate_id) = 'blob' AND length(candidate_id) = 32),
        candidate_sha256 BLOB NOT NULL CHECK (typeof(candidate_sha256) = 'blob' AND length(candidate_sha256) = 32),
        candidate_bytes BLOB NOT NULL CHECK (typeof(candidate_bytes) = 'blob' AND length(candidate_bytes) BETWEEN 1 AND 262144),
        release_revision_be BLOB NOT NULL CHECK (typeof(release_revision_be) = 'blob' AND length(release_revision_be) = 8),
        evaluation_epoch_be BLOB NOT NULL CHECK (typeof(evaluation_epoch_be) = 'blob' AND length(evaluation_epoch_be) = 8),
        envelope_bytes BLOB NOT NULL CHECK (typeof(envelope_bytes) = 'blob' AND length(envelope_bytes) BETWEEN 1 AND 32768),
        revocation_record_bytes BLOB CHECK (revocation_record_bytes IS NULL OR (typeof(revocation_record_bytes) = 'blob' AND length(revocation_record_bytes) = 216)),
        revocation_record_id BLOB UNIQUE CHECK (revocation_record_id IS NULL OR (typeof(revocation_record_id) = 'blob' AND length(revocation_record_id) = 32)),
        signer_registry_bytes BLOB NOT NULL CHECK (typeof(signer_registry_bytes) = 'blob' AND length(signer_registry_bytes) BETWEEN 1 AND 262144),
        signature_envelopes_bytes BLOB NOT NULL CHECK (typeof(signature_envelopes_bytes) = 'blob' AND length(signature_envelopes_bytes) BETWEEN 1 AND 1048576),
        quorum_report_bytes BLOB NOT NULL CHECK (typeof(quorum_report_bytes) = 'blob' AND length(quorum_report_bytes) BETWEEN 1 AND 262144),
        external_trust_pins_bytes BLOB NOT NULL CHECK (typeof(external_trust_pins_bytes) = 'blob' AND length(external_trust_pins_bytes) BETWEEN 1 AND 32768),
        derived_static_trust_pin_identity BLOB NOT NULL CHECK (typeof(derived_static_trust_pin_identity) = 'blob' AND length(derived_static_trust_pin_identity) = 32),
        authentication_evidence_bytes BLOB NOT NULL CHECK (typeof(authentication_evidence_bytes) = 'blob' AND length(authentication_evidence_bytes) BETWEEN 1 AND 2097152),
        authentication_evidence_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(authentication_evidence_sha256) = 'blob' AND length(authentication_evidence_sha256) = 32),
        select_candidate_id BLOB UNIQUE CHECK (select_candidate_id IS NULL OR (typeof(select_candidate_id) = 'blob' AND length(select_candidate_id) = 32)),
        select_release_revision_be BLOB UNIQUE CHECK (select_release_revision_be IS NULL OR (typeof(select_release_revision_be) = 'blob' AND length(select_release_revision_be) = 8)),
        revoke_candidate_id BLOB UNIQUE CHECK (revoke_candidate_id IS NULL OR (typeof(revoke_candidate_id) = 'blob' AND length(revoke_candidate_id) = 32)),
        revoke_release_revision_be BLOB UNIQUE CHECK (revoke_release_revision_be IS NULL OR (typeof(revoke_release_revision_be) = 'blob' AND length(revoke_release_revision_be) = 8)),
        previous_state_root BLOB NOT NULL CHECK (typeof(previous_state_root) = 'blob' AND length(previous_state_root) = 32),
        result_state_root BLOB NOT NULL UNIQUE CHECK (typeof(result_state_root) = 'blob' AND length(result_state_root) = 32),
        durable_authenticated_release_state_recorded INTEGER NOT NULL CHECK (durable_authenticated_release_state_recorded = 1),
        release_governed_trust_roots_authenticated INTEGER NOT NULL CHECK (release_governed_trust_roots_authenticated = 0),
        external_monotonic_anchor_authenticated INTEGER NOT NULL CHECK (external_monotonic_anchor_authenticated = 0),
        proof_receipt_authority INTEGER NOT NULL CHECK (proof_receipt_authority = 0),
        runtime_authority INTEGER NOT NULL CHECK (runtime_authority = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0),
        CHECK ((event_origin = 'IMPORTED_V3') = (imported_cutover_id IS NOT NULL)),
        CHECK (
            (event_kind = 'SELECT' AND revocation_record_bytes IS NULL AND revocation_record_id IS NULL AND select_candidate_id = candidate_id AND select_release_revision_be = release_revision_be AND revoke_candidate_id IS NULL AND revoke_release_revision_be IS NULL)
            OR
            (event_kind = 'REVOKE' AND revocation_record_bytes IS NOT NULL AND revocation_record_id IS NOT NULL AND select_candidate_id IS NULL AND select_release_revision_be IS NULL AND revoke_candidate_id = candidate_id AND revoke_release_revision_be = release_revision_be)
        )
    ) STRICT, WITHOUT ROWID
"""

_RELEASE_CUTOVER_SCHEMA_V7: Final = """
    CREATE TABLE spot_v7_release_cutover_v7 (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        cutover_id BLOB NOT NULL UNIQUE CHECK (typeof(cutover_id) = 'blob' AND length(cutover_id) = 32),
        source_schema_version INTEGER NOT NULL CHECK (source_schema_version = 3),
        retired_source_user_version INTEGER NOT NULL CHECK (retired_source_user_version = 307),
        source_store_identity_sha256 BLOB NOT NULL CHECK (typeof(source_store_identity_sha256) = 'blob' AND length(source_store_identity_sha256) = 32),
        imported_final_revision_be BLOB NOT NULL CHECK (typeof(imported_final_revision_be) = 'blob' AND length(imported_final_revision_be) = 8),
        imported_release_state_root BLOB NOT NULL CHECK (typeof(imported_release_state_root) = 'blob' AND length(imported_release_state_root) = 32),
        imported_checkpoint_hash BLOB NOT NULL CHECK (typeof(imported_checkpoint_hash) = 'blob' AND length(imported_checkpoint_hash) = 32),
        exact_imported_checkpoint_bytes BLOB NOT NULL CHECK (typeof(exact_imported_checkpoint_bytes) = 'blob' AND length(exact_imported_checkpoint_bytes) BETWEEN 1 AND 16384),
        exact_watermark_bytes BLOB NOT NULL CHECK (typeof(exact_watermark_bytes) = 'blob' AND length(exact_watermark_bytes) BETWEEN 1 AND 16384),
        watermark_sha256 BLOB NOT NULL CHECK (typeof(watermark_sha256) = 'blob' AND length(watermark_sha256) = 32),
        watermark_hash BLOB NOT NULL CHECK (typeof(watermark_hash) = 'blob' AND length(watermark_hash) = 32),
        currentness_assessment_sha256 BLOB NOT NULL CHECK (typeof(currentness_assessment_sha256) = 'blob' AND length(currentness_assessment_sha256) = 32),
        external_backend_id TEXT NOT NULL CHECK (typeof(external_backend_id) = 'text' AND length(external_backend_id) BETWEEN 1 AND 128),
        external_anchor_position_be BLOB NOT NULL CHECK (typeof(external_anchor_position_be) = 'blob' AND length(external_anchor_position_be) = 8),
        external_anchor_commitment BLOB NOT NULL CHECK (typeof(external_anchor_commitment) = 'blob' AND length(external_anchor_commitment) = 32),
        external_anchor_parent_commitment BLOB NOT NULL CHECK (typeof(external_anchor_parent_commitment) = 'blob' AND length(external_anchor_parent_commitment) = 32),
        old_store_retired INTEGER NOT NULL CHECK (old_store_retired = 1),
        new_release_writer_active INTEGER NOT NULL CHECK (new_release_writer_active = 1),
        external_monotonic_anchor_authenticated INTEGER NOT NULL CHECK (external_monotonic_anchor_authenticated = 0),
        currentness_at_settlement_verified INTEGER NOT NULL CHECK (currentness_at_settlement_verified = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
"""

_RELEASE_OBSERVATIONS_SCHEMA_V7: Final = """
    CREATE TABLE spot_v7_release_observations_v7 (
        external_anchor_position_be BLOB NOT NULL PRIMARY KEY CHECK (typeof(external_anchor_position_be) = 'blob' AND length(external_anchor_position_be) = 8),
        external_backend_id TEXT NOT NULL CHECK (typeof(external_backend_id) = 'text' AND length(external_backend_id) BETWEEN 1 AND 128),
        external_anchor_commitment BLOB NOT NULL UNIQUE CHECK (typeof(external_anchor_commitment) = 'blob' AND length(external_anchor_commitment) = 32),
        external_anchor_parent_commitment BLOB NOT NULL CHECK (typeof(external_anchor_parent_commitment) = 'blob' AND length(external_anchor_parent_commitment) = 32),
        watermark_hash BLOB NOT NULL UNIQUE CHECK (typeof(watermark_hash) = 'blob' AND length(watermark_hash) = 32),
        watermark_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(watermark_sha256) = 'blob' AND length(watermark_sha256) = 32),
        exact_watermark_bytes BLOB NOT NULL CHECK (typeof(exact_watermark_bytes) = 'blob' AND length(exact_watermark_bytes) BETWEEN 1 AND 16384),
        local_checkpoint_hash BLOB NOT NULL CHECK (typeof(local_checkpoint_hash) = 'blob' AND length(local_checkpoint_hash) = 32),
        local_checkpoint_sha256 BLOB NOT NULL CHECK (typeof(local_checkpoint_sha256) = 'blob' AND length(local_checkpoint_sha256) = 32),
        exact_local_checkpoint_bytes BLOB NOT NULL CHECK (typeof(exact_local_checkpoint_bytes) = 'blob' AND length(exact_local_checkpoint_bytes) BETWEEN 1 AND 16384),
        assessment_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(assessment_sha256) = 'blob' AND length(assessment_sha256) = 32),
        exact_assessment_bytes BLOB NOT NULL CHECK (typeof(exact_assessment_bytes) = 'blob' AND length(exact_assessment_bytes) BETWEEN 1 AND 65536),
        observed_database_revision_be BLOB NOT NULL CHECK (typeof(observed_database_revision_be) = 'blob' AND length(observed_database_revision_be) = 8),
        observed_release_state_root BLOB NOT NULL CHECK (typeof(observed_release_state_root) = 'blob' AND length(observed_release_state_root) = 32),
        observation_relation TEXT NOT NULL CHECK (typeof(observation_relation) = 'text' AND length(observation_relation) BETWEEN 1 AND 128),
        blocker_code TEXT NOT NULL CHECK (typeof(blocker_code) = 'text' AND length(blocker_code) BETWEEN 1 AND 128),
        external_finality_authenticated INTEGER NOT NULL CHECK (external_finality_authenticated = 0),
        external_monotonicity_authenticated INTEGER NOT NULL CHECK (external_monotonicity_authenticated = 0),
        rollback_safe_currentness_established INTEGER NOT NULL CHECK (rollback_safe_currentness_established = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
"""

_RELEASE_SCHEMA_SQL_V7: Final = {
    "spot_v7_release_state_v7": _RELEASE_STATE_SCHEMA_V7,
    "spot_v7_release_events_v7": _RELEASE_EVENTS_SCHEMA_V7,
    "spot_v7_release_cutover_v7": _RELEASE_CUTOVER_SCHEMA_V7,
    "spot_v7_release_observations_v7": _RELEASE_OBSERVATIONS_SCHEMA_V7,
}


def _install_spot_v7_release_schema_v7(connection: sqlite3.Connection) -> None:
    """Install the release tables inside an already-open write transaction."""

    if type(connection) is not sqlite3.Connection:
        raise TypeError("V7 release schema requires an exact SQLite connection")
    if not connection.in_transaction:
        raise ValueError("V7 release schema installation requires a transaction")
    existing = {
        str(row[0])
        for row in connection.execute(
            "SELECT name FROM sqlite_master WHERE name LIKE 'spot_v7_release_%_v7'"
        ).fetchall()
    }
    if existing:
        raise ValueError("V7 release schema already exists or is incomplete")
    for statement in _RELEASE_SCHEMA_SQL_V7.values():
        connection.execute(statement)
    _validate_spot_v7_release_schema_v7(connection)


def _validate_spot_v7_release_schema_v7(connection: sqlite3.Connection) -> None:
    """Require the exact release-table subset while allowing economic tables."""

    if type(connection) is not sqlite3.Connection:
        raise TypeError("V7 release schema requires an exact SQLite connection")
    rows = connection.execute(
        "SELECT name, sql FROM sqlite_master WHERE name LIKE 'spot_v7_release_%_v7' ORDER BY name"
    ).fetchall()
    observed = {str(row[0]): str(row[1]) for row in rows}
    if frozenset(observed) != frozenset(_RELEASE_SCHEMA_SQL_V7):
        raise ValueError("V7 release schema object set mismatch")
    for name, expected in _RELEASE_SCHEMA_SQL_V7.items():
        if _normalize_sql(observed[name]) != _normalize_sql(expected):
            raise ValueError(f"V7 release schema SQL mismatch for {name}")
    placeholders = ",".join("?" for _name in _RELEASE_SCHEMA_SQL_V7)
    attached_objects = connection.execute(
        f"SELECT type, name FROM sqlite_master "
        f"WHERE tbl_name IN ({placeholders}) "
        "AND (type = 'trigger' OR (type = 'index' AND sql IS NOT NULL))",
        tuple(_RELEASE_SCHEMA_SQL_V7),
    ).fetchall()
    if attached_objects:
        raise ValueError("V7 release tables have unexpected triggers or explicit indexes")


def _normalize_sql(value: str) -> str:
    return " ".join(value.strip().removesuffix(";").split())


__all__ = ()
