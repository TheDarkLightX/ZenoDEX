"""Restart replay and exact row reconstruction for Spot V7 settlement mechanics."""

from __future__ import annotations

import hashlib
import sqlite3
from dataclasses import dataclass

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _seal_test_only_spot_v7_settlement_v1,
    _SpotV7SettlementCandidateInputV1,
    _TestOnlySealedSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_atomic_settlement_records import _single_identifier
from src.integration._zrpf_spot_v7_atomic_settlement_schema import (
    _opening_from_row,
    _read_current_cells,
    _read_spot_v7_cursor,
)
from src.integration._zrpf_spot_v7_operational_store import (
    _validate_complete_test_only_operational_history,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    SpotV7AssetEffectV1,
    SpotV7CellKindV1,
    SpotV7CellOpeningV1,
    SpotV7CellRoleV1,
    SpotV7CellTransitionV1,
    _hash_bytes,
    _hex_hash,
)


@dataclass(frozen=True, slots=True)
class _StoredCandidatePartsV1:
    action: str
    authorization: str
    grant_spend: str
    transitions: tuple[SpotV7CellTransitionV1, ...]
    effects: tuple[SpotV7AssetEffectV1, ...]
    consumed: tuple[str, ...]


@dataclass(slots=True)
class _ReplayStateV1:
    cells: dict[str, SpotV7CellOpeningV1]
    updated_revisions: dict[str, int]
    state_root: str
    epoch_id: int | None


def _validate_complete_spot_v7_history(connection: sqlite3.Connection) -> None:
    """Replay economic rows plus the legacy operational evidence surface."""

    _validate_complete_spot_v7_economic_history(connection)
    _validate_complete_test_only_operational_history(connection)


def _validate_complete_spot_v7_economic_history(
    connection: sqlite3.Connection,
) -> None:
    """Replay every committed economic row and compare current cells."""

    _validate_database_pragmas_and_counts(connection)
    meta = _read_meta_row(connection)
    state = _read_genesis_replay_state(connection, meta)
    settlements = connection.execute(
        "SELECT * FROM spot_v7_settlements ORDER BY revision"
    ).fetchall()
    for expected_revision, row in enumerate(settlements, start=1):
        state = _replay_one_settlement(connection, row, expected_revision, state)
    current_cells = {cell.cell_key: cell for cell in _read_current_cells(connection)}
    if state.cells != current_cells:
        raise ValueError("Spot V7 current cells disagree with replayed history")
    current_revisions = {
        _hex_hash(bytes(row["cell_key"])): int(row["updated_revision"])
        for row in connection.execute(
            "SELECT cell_key, updated_revision FROM spot_v7_cells ORDER BY cell_key"
        ).fetchall()
    }
    if state.updated_revisions != current_revisions:
        raise ValueError("Spot V7 cell revisions disagree with replayed history")
    head = _read_spot_v7_cursor(connection)
    if head.state_root != state.state_root:
        raise ValueError("Spot V7 metadata state root disagrees with replayed history")
    if head.last_epoch_id != state.epoch_id:
        raise ValueError("Spot V7 metadata epoch disagrees with replayed history")


def _read_meta_row(connection: sqlite3.Connection) -> sqlite3.Row:
    row = connection.execute("SELECT * FROM spot_v7_store_meta WHERE singleton = 1").fetchone()
    if row is None:
        raise ValueError("Spot V7 metadata row is missing")
    return row


def _read_genesis_replay_state(
    connection: sqlite3.Connection,
    meta: sqlite3.Row,
) -> _ReplayStateV1:
    rows = connection.execute("SELECT * FROM spot_v7_genesis_cells ORDER BY cell_key").fetchall()
    cells = tuple(_opening_from_row(row) for row in rows)
    return _ReplayStateV1(
        cells={cell.cell_key: cell for cell in cells},
        updated_revisions={cell.cell_key: 0 for cell in cells},
        state_root=_hex_hash(bytes(meta["genesis_state_root"])),
        epoch_id=None,
    )


def _replay_one_settlement(
    connection: sqlite3.Connection,
    row: sqlite3.Row,
    expected_revision: int,
    state: _ReplayStateV1,
) -> _ReplayStateV1:
    if int(row["revision"]) != expected_revision:
        raise ValueError("Spot V7 settlement revisions are not dense")
    epoch = int.from_bytes(bytes(row["epoch_id_be"]), "big")
    if state.epoch_id is not None and epoch <= state.epoch_id:
        raise ValueError("Spot V7 settlement epochs are not strictly increasing")
    if _hex_hash(bytes(row["previous_state_root"])) != state.state_root:
        raise ValueError("Spot V7 settlement state-root continuity mismatch")
    candidate = _reconstruct_candidate(connection, row)
    if candidate.settlement_commitment != _hex_hash(bytes(row["settlement_commitment"])):
        raise ValueError("Spot V7 stored capability commitment mismatch")
    _apply_replayed_transitions(
        state.cells,
        state.updated_revisions,
        candidate.cell_transitions,
        revision=expected_revision,
    )
    return _ReplayStateV1(
        state.cells,
        state.updated_revisions,
        candidate.post_state_root,
        epoch,
    )


def _validate_database_pragmas_and_counts(connection: sqlite3.Connection) -> None:
    quick_check = connection.execute("PRAGMA quick_check").fetchall()
    if len(quick_check) != 1 or quick_check[0][0] != "ok":
        raise ValueError("Spot V7 store quick_check failed")
    if connection.execute("PRAGMA foreign_key_check").fetchone() is not None:
        raise ValueError("Spot V7 store foreign_key_check failed")
    meta = _read_meta_row(connection)
    revision = int(meta["revision"])
    expected_counts = {
        "spot_v7_settlements": revision,
        "spot_v7_economic_actions": revision,
        "spot_v7_authorization_nullifiers": revision,
        "spot_v7_authorization_grant_spends": revision,
        "spot_v7_cell_transitions": revision * 4,
        "spot_v7_asset_effects": revision * 2,
        "spot_v7_cells": int(meta["cell_count"]),
        "spot_v7_genesis_cells": int(meta["cell_count"]),
    }
    for table, expected in expected_counts.items():
        actual = _table_count(connection, table)
        if actual != expected:
            raise ValueError(f"Spot V7 store count mismatch for {table}")
    if revision and _table_count(connection, "spot_v7_consumed_objects") < revision:
        raise ValueError("Spot V7 consumed-object count is incomplete")
    _validate_meta_authority_nonclaim(meta)


def _table_count(connection: sqlite3.Connection, table: str) -> int:
    statements = {
        "spot_v7_settlements": "SELECT count(*) FROM spot_v7_settlements",
        "spot_v7_economic_actions": "SELECT count(*) FROM spot_v7_economic_actions",
        "spot_v7_authorization_nullifiers": (
            "SELECT count(*) FROM spot_v7_authorization_nullifiers"
        ),
        "spot_v7_authorization_grant_spends": (
            "SELECT count(*) FROM spot_v7_authorization_grant_spends"
        ),
        "spot_v7_cell_transitions": "SELECT count(*) FROM spot_v7_cell_transitions",
        "spot_v7_asset_effects": "SELECT count(*) FROM spot_v7_asset_effects",
        "spot_v7_cells": "SELECT count(*) FROM spot_v7_cells",
        "spot_v7_genesis_cells": "SELECT count(*) FROM spot_v7_genesis_cells",
        "spot_v7_consumed_objects": "SELECT count(*) FROM spot_v7_consumed_objects",
    }
    try:
        statement = statements[table]
    except KeyError as exc:
        raise ValueError("unsupported Spot V7 count table") from exc
    return int(connection.execute(statement).fetchone()[0])


def _validate_meta_authority_nonclaim(meta: sqlite3.Row) -> None:
    if (
        int(meta["settlement_authority"]) != 0
        or int(meta["production_authority"]) != 0
        or str(meta["authority_blocked_reason"])
        != SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1
    ):
        raise ValueError("Spot V7 metadata authority non-claim mismatch")


def _reconstruct_candidate(
    connection: sqlite3.Connection,
    settlement_row: sqlite3.Row,
) -> _TestOnlySealedSpotV7SettlementV1:
    commitment = bytes(settlement_row["settlement_commitment"])
    meta = _read_meta_row(connection)
    parts = _load_candidate_parts(connection, commitment)
    _validate_stored_artifact_hashes(settlement_row)
    candidate_input = _candidate_input_from_rows(meta, settlement_row, parts)
    candidate = _seal_test_only_spot_v7_settlement_v1(candidate_input)
    _validate_candidate_roots_and_identity(meta, settlement_row, candidate)
    return candidate


def _load_candidate_parts(
    connection: sqlite3.Connection,
    commitment: bytes,
) -> _StoredCandidatePartsV1:
    return _StoredCandidatePartsV1(
        action=_single_identifier(
            connection, "spot_v7_economic_actions", "economic_action_id", commitment
        ),
        authorization=_single_identifier(
            connection,
            "spot_v7_authorization_nullifiers",
            "authorization_nullifier",
            commitment,
        ),
        grant_spend=_single_identifier(
            connection,
            "spot_v7_authorization_grant_spends",
            "authorization_grant_spend_nullifier",
            commitment,
        ),
        transitions=_load_transitions(connection, commitment),
        effects=_load_effects(connection, commitment),
        consumed=_load_consumed_objects(connection, commitment),
    )


def _load_transitions(
    connection: sqlite3.Connection,
    commitment: bytes,
) -> tuple[SpotV7CellTransitionV1, ...]:
    rows = connection.execute(
        "SELECT * FROM spot_v7_cell_transitions WHERE settlement_commitment = ? ORDER BY ordinal",
        (commitment,),
    ).fetchall()
    if len(rows) != 4 or [int(row["ordinal"]) for row in rows] != list(range(4)):
        raise ValueError("Spot V7 stored transition ordinals are invalid")
    return tuple(_transition_from_row(row) for row in rows)


def _load_effects(
    connection: sqlite3.Connection,
    commitment: bytes,
) -> tuple[SpotV7AssetEffectV1, ...]:
    rows = connection.execute(
        "SELECT * FROM spot_v7_asset_effects WHERE settlement_commitment = ? ORDER BY ordinal",
        (commitment,),
    ).fetchall()
    if len(rows) != 2 or [int(row["ordinal"]) for row in rows] != [0, 1]:
        raise ValueError("Spot V7 stored effect ordinals are invalid")
    return tuple(_effect_from_row(row) for row in rows)


def _load_consumed_objects(
    connection: sqlite3.Connection,
    commitment: bytes,
) -> tuple[str, ...]:
    rows = connection.execute(
        "SELECT * FROM spot_v7_consumed_objects WHERE settlement_commitment = ? ORDER BY ordinal",
        (commitment,),
    ).fetchall()
    ordinals = [int(row["ordinal"]) for row in rows]
    if not rows or ordinals != list(range(len(rows))):
        raise ValueError("Spot V7 stored consumed-object ordinals are invalid")
    return tuple(_hex_hash(bytes(row["consumed_object_id"])) for row in rows)


def _candidate_input_from_rows(
    meta: sqlite3.Row,
    row: sqlite3.Row,
    parts: _StoredCandidatePartsV1,
) -> _SpotV7SettlementCandidateInputV1:
    return _SpotV7SettlementCandidateInputV1(
        application_id=_hex_hash(bytes(meta["application_id"])),
        chain_or_domain_id=_hex_hash(bytes(meta["chain_or_domain_id"])),
        epoch_id=int.from_bytes(bytes(row["epoch_id_be"]), "big"),
        verified_program_id=_hex_hash(bytes(row["verified_program_id"])),
        verified_profile_id=_hex_hash(bytes(row["verified_profile_id"])),
        verified_program_manifest_root=_hex_hash(bytes(row["verified_program_manifest_root"])),
        source_child_claim_binding=_hex_hash(bytes(row["source_child_claim_binding"])),
        source_child_journal_sha256=_hex_hash(bytes(row["source_child_journal_sha256"])),
        data_availability_certificate_root=_hex_hash(
            bytes(row["data_availability_certificate_root"])
        ),
        data_root=_hex_hash(bytes(row["data_root"])),
        settlement_effect_plan_commitment=_hex_hash(
            bytes(row["settlement_effect_plan_commitment"])
        ),
        pre_state_root=_hex_hash(bytes(row["previous_state_root"])),
        post_state_root=_hex_hash(bytes(row["result_state_root"])),
        economic_action_id=parts.action,
        authorization_nullifier=parts.authorization,
        authorization_grant_spend_nullifier=parts.grant_spend,
        consumed_object_ids=parts.consumed,
        cell_transitions=parts.transitions,
        cell_transitions_root=_hex_hash(bytes(row["cell_transitions_root"])),
        asset_effects=parts.effects,
        exact_v7_receipt_bytes=bytes(row["exact_v7_receipt"]),
        exact_v7_journal_bytes=bytes(row["exact_v7_journal"]),
        exact_plan_b_bytes=bytes(row["exact_plan_b"]),
        exact_firecracker_execution_record_bytes=bytes(row["exact_firecracker_execution_record"]),
        exact_firecracker_output_bytes=bytes(row["exact_firecracker_output"]),
    )


def _validate_stored_artifact_hashes(row: sqlite3.Row) -> None:
    pairs = (
        ("receipt_sha256", "exact_v7_receipt"),
        ("journal_sha256", "exact_v7_journal"),
        ("plan_b_sha256", "exact_plan_b"),
        ("firecracker_execution_record_sha256", "exact_firecracker_execution_record"),
        ("firecracker_output_sha256", "exact_firecracker_output"),
    )
    for hash_name, bytes_name in pairs:
        observed = hashlib.sha256(bytes(row[bytes_name])).digest()
        if observed != bytes(row[hash_name]):
            raise ValueError(f"Spot V7 stored artifact hash mismatch: {bytes_name}")


def _validate_candidate_roots_and_identity(
    meta: sqlite3.Row,
    row: sqlite3.Row,
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> None:
    if any(
        bytes(row[name]) != bytes(meta[name])
        for name in (
            "verified_program_id",
            "verified_profile_id",
            "verified_program_manifest_root",
        )
    ):
        raise ValueError("Spot V7 settlement program identity drift")
    authority_fields = (
        "settlement_authority",
        "production_authority",
        "firecracker_execution_verified",
    )
    if any(int(row[name]) != 0 for name in authority_fields):
        raise ValueError("Spot V7 settlement authority flag drift")
    if str(row["authority_blocked_reason"]) != (
        SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1
    ):
        raise ValueError("Spot V7 settlement blocked reason drift")
    if candidate.cell_transitions_root != _hex_hash(bytes(row["cell_transitions_root"])):
        raise ValueError("Spot V7 stored cell transition root mismatch")


def _transition_from_row(row: sqlite3.Row) -> SpotV7CellTransitionV1:
    kind = SpotV7CellKindV1(int(row["kind"]))
    subject_id = "0x" + bytes(row["subject_id"]).hex()
    asset_id = _hex_hash(bytes(row["asset_id"]))
    pre = SpotV7CellOpeningV1(
        kind,
        subject_id,
        asset_id,
        int.from_bytes(bytes(row["pre_atoms_be"]), "big"),
    )
    post = SpotV7CellOpeningV1(
        kind,
        subject_id,
        asset_id,
        int.from_bytes(bytes(row["post_atoms_be"]), "big"),
    )
    transition = SpotV7CellTransitionV1(SpotV7CellRoleV1(int(row["role"])), pre, post)
    expected = {
        "cell_key": transition.cell_key,
        "pre_value_hash": transition.pre.value_hash,
        "post_value_hash": transition.post.value_hash,
        "transition_commitment": transition.commitment,
    }
    for name, value in expected.items():
        if bytes(row[name]) != _hash_bytes(value, name=f"stored transition {name}"):
            raise ValueError(f"Spot V7 stored transition mismatch: {name}")
    if int.from_bytes(bytes(row["amount_atoms_be"]), "big") != transition.amount_atoms:
        raise ValueError("Spot V7 stored transition amount mismatch")
    return transition


def _effect_from_row(row: sqlite3.Row) -> SpotV7AssetEffectV1:
    effect = SpotV7AssetEffectV1(
        economic_action_id=_hex_hash(bytes(row["economic_action_id"])),
        asset_id=_hex_hash(bytes(row["asset_id"])),
        amount_atoms=int.from_bytes(bytes(row["amount_atoms_be"]), "big"),
    )
    if bytes(row["effect_id"]) != _hash_bytes(effect.effect_id, name="stored effect ID"):
        raise ValueError("Spot V7 stored effect ID mismatch")
    return effect


def _apply_replayed_transitions(
    cells: dict[str, SpotV7CellOpeningV1],
    updated_revisions: dict[str, int],
    transitions: tuple[SpotV7CellTransitionV1, ...],
    *,
    revision: int,
) -> None:
    for transition in transitions:
        if cells.get(transition.cell_key) != transition.pre:
            raise ValueError("Spot V7 replayed cell pre-state mismatch")
        cells[transition.cell_key] = transition.post
        updated_revisions[transition.cell_key] = revision


def _stored_candidate_matches(
    connection: sqlite3.Connection,
    candidate: _TestOnlySealedSpotV7SettlementV1,
) -> bool:
    row = connection.execute(
        "SELECT * FROM spot_v7_settlements WHERE settlement_commitment = ?",
        (_hash_bytes(candidate.settlement_commitment, name="candidate commitment"),),
    ).fetchone()
    if row is None:
        return False
    reconstructed = _reconstruct_candidate(connection, row)
    artifact_pairs = (
        (reconstructed.exact_v7_receipt_bytes, candidate.exact_v7_receipt_bytes),
        (reconstructed.exact_v7_journal_bytes, candidate.exact_v7_journal_bytes),
        (reconstructed.exact_plan_b_bytes, candidate.exact_plan_b_bytes),
        (
            reconstructed.exact_firecracker_execution_record_bytes,
            candidate.exact_firecracker_execution_record_bytes,
        ),
        (reconstructed.exact_firecracker_output_bytes, candidate.exact_firecracker_output_bytes),
    )
    return reconstructed.settlement_commitment == candidate.settlement_commitment and all(
        left == right for left, right in artifact_pairs
    )
