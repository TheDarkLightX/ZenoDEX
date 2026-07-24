"""Locked duplicate checks and persistence for Spot V7 settlement mechanics."""

from __future__ import annotations

import sqlite3

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _TestOnlySealedSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_atomic_settlement_schema import _opening_from_row
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    SpotV7AtomicSettlementCursorV1,
    SpotV7AtomicSettlementRejectReasonV1,
    SpotV7CellTransitionV1,
    _hash_bytes,
)


def _candidate_reject_reason_locked(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> SpotV7AtomicSettlementRejectReasonV1 | None:
    duplicate = _duplicate_settlement_reason(connection, candidate)
    if duplicate is not None:
        return duplicate
    duplicate = _duplicate_identity_reason(connection, candidate)
    if duplicate is not None:
        return duplicate
    for object_id in candidate.consumed_object_ids:
        row = connection.execute(
            "SELECT 1 FROM spot_v7_consumed_objects WHERE consumed_object_id = ?",
            (_hash_bytes(object_id, name="candidate consumed object"),),
        ).fetchone()
        if row is not None:
            return SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_CONSUMED_OBJECT
    return None


def _duplicate_settlement_reason(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> SpotV7AtomicSettlementRejectReasonV1 | None:
    duplicate = _first_duplicate_reason(
        connection,
        _artifact_duplicate_checks(candidate),
    )
    if duplicate is not None:
        return duplicate
    return _first_duplicate_reason(connection, _binding_duplicate_checks(candidate))


def _artifact_duplicate_checks(
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> tuple[tuple[str, str, str, SpotV7AtomicSettlementRejectReasonV1], ...]:
    return (
        (
            "SELECT 1 FROM spot_v7_settlements WHERE receipt_sha256 = ?",
            "receipt_sha256",
            candidate.receipt_sha256,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_RECEIPT,
        ),
        (
            "SELECT 1 FROM spot_v7_settlements WHERE journal_sha256 = ?",
            "journal_sha256",
            candidate.journal_sha256,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_JOURNAL,
        ),
        (
            "SELECT 1 FROM spot_v7_settlements "
            "WHERE firecracker_execution_record_sha256 = ?",
            "firecracker_execution_record_sha256",
            candidate.firecracker_execution_record_sha256,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_FIRECRACKER_EXECUTION,
        ),
        (
            "SELECT 1 FROM spot_v7_settlements WHERE firecracker_output_sha256 = ?",
            "firecracker_output_sha256",
            candidate.firecracker_output_sha256,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_FIRECRACKER_OUTPUT,
        ),
    )


def _binding_duplicate_checks(
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> tuple[tuple[str, str, str, SpotV7AtomicSettlementRejectReasonV1], ...]:
    return (
        (
            "SELECT 1 FROM spot_v7_settlements "
            "WHERE settlement_effect_plan_commitment = ?",
            "settlement_effect_plan_commitment",
            candidate.settlement_effect_plan_commitment,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SETTLEMENT_PLAN,
        ),
        (
            "SELECT 1 FROM spot_v7_settlements WHERE plan_b_sha256 = ?",
            "plan_b_sha256",
            candidate.plan_b_sha256,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SETTLEMENT_PLAN,
        ),
        (
            "SELECT 1 FROM spot_v7_settlements WHERE source_child_claim_binding = ?",
            "source_child_claim_binding",
            candidate.source_child_claim_binding,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SOURCE_CHILD,
        ),
        (
            "SELECT 1 FROM spot_v7_settlements WHERE source_child_journal_sha256 = ?",
            "source_child_journal_sha256",
            candidate.source_child_journal_sha256,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SOURCE_CHILD,
        ),
        (
            "SELECT 1 FROM spot_v7_settlements WHERE result_state_root = ?",
            "result_state_root",
            candidate.post_state_root,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_POST_STATE_ROOT,
        ),
    )


def _duplicate_identity_reason(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> SpotV7AtomicSettlementRejectReasonV1 | None:
    checks = (
        (
            "SELECT 1 FROM spot_v7_economic_actions WHERE economic_action_id = ?",
            "economic_action_id",
            candidate.economic_action_id,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_ECONOMIC_ACTION,
        ),
        (
            "SELECT 1 FROM spot_v7_authorization_nullifiers "
            "WHERE authorization_nullifier = ?",
            "authorization_nullifier",
            candidate.authorization_nullifier,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_AUTHORIZATION_NULLIFIER,
        ),
        (
            "SELECT 1 FROM spot_v7_authorization_grant_spends "
            "WHERE authorization_grant_spend_nullifier = ?",
            "authorization_grant_spend_nullifier",
            candidate.authorization_grant_spend_nullifier,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_AUTHORIZATION_GRANT_SPEND,
        ),
    )
    return _first_duplicate_reason(connection, checks)


def _first_duplicate_reason(
    connection: sqlite3.Connection,
    checks: tuple[tuple[str, str, str, SpotV7AtomicSettlementRejectReasonV1], ...],
) -> SpotV7AtomicSettlementRejectReasonV1 | None:
    for statement, name, value, reason in checks:
        encoded = _hash_bytes(value, name=f"candidate duplicate {name}")
        if connection.execute(statement, (encoded,)).fetchone() is not None:
            return reason
    return None


def _candidate_cells_match_locked(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> bool:
    for transition in candidate.cell_transitions:
        row = connection.execute(
            "SELECT * FROM spot_v7_cells WHERE cell_key = ?",
            (_hash_bytes(transition.cell_key, name="candidate cell key"),),
        ).fetchone()
        if row is None or _opening_from_row(row) != transition.pre:
            return False
    return True


def _persist_candidate(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
    next_cursor: SpotV7AtomicSettlementCursorV1,
) -> None:
    _persist_settlement_header(connection, candidate, next_cursor)
    _persist_unique_identities(connection, candidate)
    _persist_cell_transitions(connection, candidate, next_cursor.revision)
    _persist_asset_effects(connection, candidate)
    _persist_consumed_objects(connection, candidate)


def _persist_settlement_header(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
    next_cursor: SpotV7AtomicSettlementCursorV1,
) -> None:
    connection.execute(
        """
        INSERT INTO spot_v7_settlements (
            settlement_commitment, revision, epoch_id_be, previous_state_root,
            result_state_root, receipt_sha256, journal_sha256,
            firecracker_execution_record_sha256, firecracker_output_sha256,
            plan_b_sha256, verified_program_id, verified_profile_id,
            verified_program_manifest_root, source_child_claim_binding,
            source_child_journal_sha256, data_availability_certificate_root,
            data_root, settlement_effect_plan_commitment, cell_transitions_root,
            exact_v7_receipt, exact_v7_journal, exact_plan_b,
            exact_firecracker_execution_record, exact_firecracker_output,
            settlement_authority, production_authority,
            firecracker_execution_verified, authority_blocked_reason
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0, ?)
        """,
        _settlement_header_values(candidate, next_cursor),
    )


def _settlement_header_values(
    candidate: _TestOnlySealedSpotV7SettlementV1,
    next_cursor: SpotV7AtomicSettlementCursorV1,
) -> tuple[object, ...]:
    return (
        _hash_bytes(candidate.settlement_commitment, name="candidate commitment"),
        next_cursor.revision,
        candidate.epoch_id.to_bytes(8, "big"),
        _hash_bytes(candidate.pre_state_root, name="candidate pre state"),
        _hash_bytes(candidate.post_state_root, name="candidate post state"),
        _hash_bytes(candidate.receipt_sha256, name="candidate receipt SHA-256"),
        _hash_bytes(candidate.journal_sha256, name="candidate journal SHA-256"),
        _hash_bytes(
            candidate.firecracker_execution_record_sha256,
            name="candidate Firecracker execution SHA-256",
        ),
        _hash_bytes(candidate.firecracker_output_sha256, name="candidate output SHA-256"),
        _hash_bytes(candidate.plan_b_sha256, name="candidate Plan B SHA-256"),
        _hash_bytes(candidate.verified_program_id, name="candidate program ID"),
        _hash_bytes(candidate.verified_profile_id, name="candidate profile ID"),
        _hash_bytes(candidate.verified_program_manifest_root, name="candidate manifest"),
        _hash_bytes(candidate.source_child_claim_binding, name="candidate child claim"),
        _hash_bytes(candidate.source_child_journal_sha256, name="candidate child journal"),
        _hash_bytes(
            candidate.data_availability_certificate_root,
            name="candidate DA certificate root",
        ),
        _hash_bytes(candidate.data_root, name="candidate data root"),
        _hash_bytes(candidate.settlement_effect_plan_commitment, name="candidate plan"),
        _hash_bytes(candidate.cell_transitions_root, name="candidate transition root"),
        candidate.exact_v7_receipt_bytes,
        candidate.exact_v7_journal_bytes,
        candidate.exact_plan_b_bytes,
        candidate.exact_firecracker_execution_record_bytes,
        candidate.exact_firecracker_output_bytes,
        SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    )


def _persist_unique_identities(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> None:
    commitment = _hash_bytes(candidate.settlement_commitment, name="candidate commitment")
    statements = (
        (
            "INSERT INTO spot_v7_economic_actions "
            "(economic_action_id, settlement_commitment) VALUES (?, ?)",
            "economic_action_id",
            candidate.economic_action_id,
        ),
        (
            "INSERT INTO spot_v7_authorization_nullifiers "
            "(authorization_nullifier, settlement_commitment) VALUES (?, ?)",
            "authorization_nullifier",
            candidate.authorization_nullifier,
        ),
        (
            "INSERT INTO spot_v7_authorization_grant_spends "
            "(authorization_grant_spend_nullifier, settlement_commitment) VALUES (?, ?)",
            "authorization_grant_spend_nullifier",
            candidate.authorization_grant_spend_nullifier,
        ),
    )
    for statement, name, value in statements:
        connection.execute(
            statement,
            (_hash_bytes(value, name=f"candidate {name}"), commitment),
        )


def _persist_cell_transitions(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
    revision: int,
) -> None:
    commitment = _hash_bytes(candidate.settlement_commitment, name="candidate commitment")
    for ordinal, transition in enumerate(candidate.cell_transitions):
        _insert_cell_transition(connection, commitment, ordinal, transition)
        cursor = connection.execute(
            """
            UPDATE spot_v7_cells
            SET atoms_be = ?, value_hash = ?, updated_revision = ?
            WHERE cell_key = ? AND atoms_be = ? AND value_hash = ?
            """,
            (
                transition.post.atoms.to_bytes(16, "big"),
                _hash_bytes(transition.post.value_hash, name="transition post value"),
                revision,
                _hash_bytes(transition.cell_key, name="transition cell key"),
                transition.pre.atoms.to_bytes(16, "big"),
                _hash_bytes(transition.pre.value_hash, name="transition pre value"),
            ),
        )
        if cursor.rowcount != 1:
            raise ValueError("Spot V7 cell compare-and-swap failed during persistence")


def _insert_cell_transition(
    connection: sqlite3.Connection,
    settlement_commitment: bytes,
    ordinal: int,
    transition: SpotV7CellTransitionV1,
) -> None:
    if type(transition) is not SpotV7CellTransitionV1:
        raise TypeError("transition must be exact SpotV7CellTransitionV1")
    connection.execute(
        """
        INSERT INTO spot_v7_cell_transitions (
            settlement_commitment, ordinal, cell_key, kind, role, subject_id,
            asset_id, pre_atoms_be, post_atoms_be, pre_value_hash,
            post_value_hash, amount_atoms_be, transition_commitment
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            settlement_commitment,
            ordinal,
            _hash_bytes(transition.cell_key, name="transition cell key"),
            transition.pre.kind.value,
            transition.role.value,
            bytes.fromhex(transition.pre.subject_id[2:]),
            _hash_bytes(transition.pre.asset_id, name="transition asset"),
            transition.pre.atoms.to_bytes(16, "big"),
            transition.post.atoms.to_bytes(16, "big"),
            _hash_bytes(transition.pre.value_hash, name="transition pre value"),
            _hash_bytes(transition.post.value_hash, name="transition post value"),
            transition.amount_atoms.to_bytes(16, "big"),
            _hash_bytes(transition.commitment, name="transition commitment"),
        ),
    )


def _persist_asset_effects(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> None:
    commitment = _hash_bytes(candidate.settlement_commitment, name="candidate commitment")
    connection.executemany(
        """
        INSERT INTO spot_v7_asset_effects (
            effect_id, settlement_commitment, ordinal, economic_action_id,
            asset_id, amount_atoms_be
        ) VALUES (?, ?, ?, ?, ?, ?)
        """,
        (
            (
                _hash_bytes(effect.effect_id, name="candidate effect ID"),
                commitment,
                ordinal,
                _hash_bytes(effect.economic_action_id, name="candidate effect action"),
                _hash_bytes(effect.asset_id, name="candidate effect asset"),
                effect.amount_atoms.to_bytes(16, "big"),
            )
            for ordinal, effect in enumerate(candidate.asset_effects)
        ),
    )


def _persist_consumed_objects(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> None:
    commitment = _hash_bytes(candidate.settlement_commitment, name="candidate commitment")
    connection.executemany(
        """
        INSERT INTO spot_v7_consumed_objects (
            consumed_object_id, settlement_commitment, ordinal
        ) VALUES (?, ?, ?)
        """,
        (
            (
                _hash_bytes(object_id, name="candidate consumed object"),
                commitment,
                ordinal,
            )
            for ordinal, object_id in enumerate(candidate.consumed_object_ids)
        ),
    )


def _cas_spot_v7_meta(
    connection: sqlite3.Connection,
    previous: SpotV7AtomicSettlementCursorV1,
    next_cursor: SpotV7AtomicSettlementCursorV1,
) -> None:
    result = connection.execute(
        """
        UPDATE spot_v7_store_meta
        SET revision = ?, settlement_count = ?, state_root = ?, last_epoch_id_be = ?
        WHERE singleton = 1 AND revision = ? AND settlement_count = ? AND state_root = ?
        """,
        (
            next_cursor.revision,
            next_cursor.settlement_count,
            _hash_bytes(next_cursor.state_root, name="next cursor state root"),
            next_cursor.last_epoch_id.to_bytes(8, "big")
            if next_cursor.last_epoch_id is not None
            else None,
            previous.revision,
            previous.settlement_count,
            _hash_bytes(previous.state_root, name="previous cursor state root"),
        ),
    )
    if result.rowcount != 1:
        raise ValueError("Spot V7 metadata compare-and-swap failed")
