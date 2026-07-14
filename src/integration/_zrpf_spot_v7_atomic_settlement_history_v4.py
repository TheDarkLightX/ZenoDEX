"""Restart replay for authority-neutral Spot V7 operational schema V4."""

from __future__ import annotations

import sqlite3
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any, cast

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
    _seal_test_only_spot_v7_settlement_v1,
)
from src.integration._zrpf_spot_v7_atomic_settlement_evidence_v4 import (
    _validate_da_row,
    _validate_finality_row,
)
from src.integration._zrpf_spot_v7_atomic_settlement_history import (
    _stored_candidate_matches,
    _validate_complete_spot_v7_economic_history,
)
from src.integration._zrpf_spot_v7_atomic_settlement_schema import (
    _read_spot_v7_cursor,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _GovernedFirecrackerSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _require_settlement_capability,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
)
from src.integration._zrpf_spot_v7_settlement_durable_replay import (
    _reverify_persisted_spot_v7_settlement_replay_v2,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    _decode_exact_json_object,
)
from src.integration._zrpf_spot_v7_settlement_replay_packet import (
    _UntrustedPersistedSpotV7SettlementReplayInputsV2,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AtomicSettlementCursorV1,
    _hash_bytes,
    _hex_hash,
)

SettlementResolverV4 = Callable[[str], object]
MAX_SPOT_V7_V4_HISTORY_ENTRIES = 1_024
MAX_SPOT_V7_V4_DATABASE_BYTES = 512 * 1_024 * 1_024


class _SpotV7SettlementResolverErrorV4(ValueError):
    """Typed fail-closed wrapper for the explicitly external resolver port."""


class _SpotV7OperationalHistoryChangedV4(ValueError):
    """The database changed after the resolver-safe history snapshot closed."""


@dataclass(frozen=True, slots=True)
class _SpotV7OperationalHistoryAnchorV4:
    economic_cursor: SpotV7AtomicSettlementCursorV1
    policy_checkpoint_sequence: int
    policy_checkpoint_hash: str
    ordered_settlement_commitments: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class _ResolvedSpotV7SettlementEntryV4:
    commitment: str
    settlement: _GovernedFirecrackerSpotV7SettlementV1


@dataclass(frozen=True, slots=True)
class _ResolvedSpotV7OperationalHistoryV4:
    anchor: _SpotV7OperationalHistoryAnchorV4
    entries: tuple[_ResolvedSpotV7SettlementEntryV4, ...]


def _capture_operational_history_anchor_locked_v4(
    connection: sqlite3.Connection,
) -> _SpotV7OperationalHistoryAnchorV4:
    cursor = _read_spot_v7_cursor(connection)
    page_count = int(connection.execute("PRAGMA page_count").fetchone()[0])
    page_size = int(connection.execute("PRAGMA page_size").fetchone()[0])
    if cursor.revision > MAX_SPOT_V7_V4_HISTORY_ENTRIES:
        raise ValueError("Spot V7 V4 history exceeds the governed entry bound")
    if (
        page_count <= 0
        or page_size <= 0
        or (page_count * page_size > MAX_SPOT_V7_V4_DATABASE_BYTES)
    ):
        raise ValueError("Spot V7 V4 database exceeds the governed byte bound")
    commitments = tuple(
        _hex_hash(bytes(row[0]))
        for row in connection.execute(
            "SELECT settlement_commitment FROM spot_v7_settlements ORDER BY revision"
        ).fetchall()
    )
    if len(commitments) != cursor.revision:
        raise ValueError("Spot V7 V4 settlement history count mismatch")
    for table in (
        "spot_v7_operational_da_v4",
        "spot_v7_operational_finality_v4",
        "spot_v7_settlement_replay_v4",
    ):
        count = int(connection.execute(f"SELECT count(*) FROM {table}").fetchone()[0])
        if count != cursor.revision:
            raise ValueError(f"Spot V7 V4 history count mismatch for {table}")
    policy_row = connection.execute(
        "SELECT current_checkpoint_sequence_be, current_checkpoint_hash "
        "FROM spot_v7_operational_policy_v4 WHERE singleton = 1"
    ).fetchone()
    if policy_row is None:
        raise ValueError("Spot V7 V4 policy cursor is missing")
    return _SpotV7OperationalHistoryAnchorV4(
        cursor,
        int.from_bytes(bytes(policy_row[0]), "big"),
        _hex_hash(bytes(policy_row[1])),
        commitments,
    )


def _resolve_operational_history_outside_transaction_v4(
    anchor: _SpotV7OperationalHistoryAnchorV4,
    settlement_resolver: SettlementResolverV4,
) -> _ResolvedSpotV7OperationalHistoryV4:
    entries = tuple(
        _resolve_settlement_entry(commitment, settlement_resolver)
        for commitment in anchor.ordered_settlement_commitments
    )
    return _ResolvedSpotV7OperationalHistoryV4(anchor, entries)


def _empty_resolved_operational_history_locked_v4(
    connection: sqlite3.Connection,
) -> _ResolvedSpotV7OperationalHistoryV4:
    anchor = _capture_operational_history_anchor_locked_v4(connection)
    if anchor.economic_cursor.revision != 0 or anchor.ordered_settlement_commitments:
        raise ValueError("Spot V7 V4 initialization history is not empty")
    return _ResolvedSpotV7OperationalHistoryV4(anchor, ())


def _append_resolved_operational_history_v4(
    resolved: _ResolvedSpotV7OperationalHistoryV4,
    *,
    expected_anchor: _SpotV7OperationalHistoryAnchorV4,
    commitment: str,
    settlement: _GovernedFirecrackerSpotV7SettlementV1,
) -> _ResolvedSpotV7OperationalHistoryV4:
    if expected_anchor.ordered_settlement_commitments != (
        resolved.anchor.ordered_settlement_commitments + (commitment,)
    ):
        raise ValueError("Spot V7 V4 successor history commitment order mismatch")
    entry = _resolved_settlement_entry(commitment, settlement)
    return _ResolvedSpotV7OperationalHistoryV4(
        expected_anchor,
        resolved.entries + (entry,),
    )


def _validate_complete_spot_v7_operational_history_v4(
    connection: sqlite3.Connection,
    *,
    policy: _GovernedSpotV7OperationalPolicyV3,
    resolved_history: _ResolvedSpotV7OperationalHistoryV4,
) -> None:
    _validate_complete_spot_v7_economic_history(connection)
    actual_anchor = _capture_operational_history_anchor_locked_v4(connection)
    if actual_anchor != resolved_history.anchor:
        raise _SpotV7OperationalHistoryChangedV4(
            "Spot V7 V4 operational history changed during external resolution"
        )
    if len(resolved_history.entries) != len(actual_anchor.ordered_settlement_commitments):
        raise ValueError("Spot V7 V4 resolved history entry count mismatch")
    store_policy = policy._base_store_policy_for_finality_v3()
    prior_sequence = store_policy.genesis_application_checkpoint_sequence
    prior_hash = store_policy.genesis_application_checkpoint_hash
    settlements = connection.execute(
        "SELECT * FROM spot_v7_settlements ORDER BY revision"
    ).fetchall()
    for settlement_row, resolved_entry in zip(
        settlements,
        resolved_history.entries,
        strict=True,
    ):
        commitment = _hex_hash(bytes(settlement_row["settlement_commitment"]))
        if resolved_entry.commitment != commitment:
            raise ValueError("Spot V7 V4 resolved history order mismatch")
        settlement = resolved_entry.settlement
        candidate = settlement._candidate_for_atomic_store()
        if _derive_capability_commitment(candidate) != commitment:
            raise ValueError("Spot V7 V4 resolver returned the wrong settlement")
        sealed = _seal_test_only_spot_v7_settlement_v1(candidate)
        if not _stored_candidate_matches(connection, sealed):
            raise ValueError("Spot V7 V4 resolved settlement differs from stored economics")
        da_row, finality_row, replay_row = _operational_rows(connection, commitment)
        replay_projection = _validate_replay_row(
            settlement,
            replay_row,
            expected_commitment=commitment,
        )
        _validate_da_row(
            policy,
            candidate_epoch=candidate.epoch_id,
            settlement_row=settlement_row,
            row=da_row,
        )
        prior_sequence, prior_hash = _validate_finality_row(
            policy,
            candidate=candidate,
            settlement_row=settlement_row,
            replay_projection=replay_projection,
            row=finality_row,
            prior_sequence=prior_sequence,
            prior_hash=prior_hash,
        )
    _require_policy_cursor(connection, prior_sequence, prior_hash)


def _resolve_settlement_entry(
    commitment: str,
    settlement_resolver: SettlementResolverV4,
) -> _ResolvedSpotV7SettlementEntryV4:
    try:
        value = settlement_resolver(commitment)
    except Exception as exc:
        raise _SpotV7SettlementResolverErrorV4("Spot V7 V4 settlement resolver failed") from exc
    return _resolved_settlement_entry(commitment, value)


def _resolved_settlement_entry(
    commitment: str,
    value: object,
) -> _ResolvedSpotV7SettlementEntryV4:
    settlement = _require_settlement_capability(value)
    if _derive_capability_commitment(settlement._candidate_for_atomic_store()) != commitment:
        raise ValueError("Spot V7 V4 resolver returned the wrong settlement")
    return _ResolvedSpotV7SettlementEntryV4(commitment, settlement)


def _operational_rows(
    connection: sqlite3.Connection,
    commitment: str,
) -> tuple[sqlite3.Row, sqlite3.Row, sqlite3.Row]:
    encoded = _hash_bytes(commitment, name="V4 history commitment")
    rows = tuple(
        connection.execute(
            f"SELECT * FROM {table} WHERE settlement_commitment = ?",
            (encoded,),
        ).fetchone()
        for table in (
            "spot_v7_operational_da_v4",
            "spot_v7_operational_finality_v4",
            "spot_v7_settlement_replay_v4",
        )
    )
    if any(row is None for row in rows):
        raise ValueError("Spot V7 V4 operational rows are incomplete")
    return (
        cast(sqlite3.Row, rows[0]),
        cast(sqlite3.Row, rows[1]),
        cast(sqlite3.Row, rows[2]),
    )


def _validate_replay_row(
    settlement: object,
    row: sqlite3.Row,
    *,
    expected_commitment: str,
) -> dict[str, Any]:
    persisted = _UntrustedPersistedSpotV7SettlementReplayInputsV2(
        exact_projection_bytes=bytes(row["exact_projection"]),
        exact_header_bytes=bytes(row["exact_header"]),
        exact_body_bytes=bytes(row["exact_body"]),
        exact_envelope_bytes=bytes(row["exact_envelope"]),
        exact_receipt_bytes=bytes(row["exact_receipt"]),
        exact_evidence_bytes=bytes(row["exact_evidence"]),
        exact_config_document_bytes=bytes(row["exact_config_document"]),
        exact_pre_state_snapshot_bytes=bytes(row["exact_pre_state_snapshot"]),
    )
    parent = None if row["exact_parent_header"] is None else bytes(row["exact_parent_header"])
    replayed = _reverify_persisted_spot_v7_settlement_replay_v2(
        settlement=settlement,
        persisted=persisted,
        exact_parent_header_bytes=parent,
    )
    packet = replayed._durable_replay_packet_for_history_commit()
    projection = packet._projection_for_history_reverification()
    if packet._persisted_inputs_for_storage() != persisted:
        raise ValueError("Spot V7 V4 replay packet differs after restart replay")
    if projection.candidate_settlement_commitment != expected_commitment:
        raise ValueError("Spot V7 V4 replay settlement commitment mismatch")
    if bytes(row["replay_material_root"]) != _hash_bytes(
        projection.replay_material_root,
        name="V4 replay material root",
    ):
        raise ValueError("Spot V7 V4 replay material root mismatch")
    _require_binary_flags(
        row,
        true_fields=("replay_reverified_before_commit",),
        false_fields=(
            "proof_receipt_authentication_established",
            "release_authority",
            "settlement_authority",
            "production_authority",
        ),
    )
    return _decode_exact_json_object(
        persisted.exact_projection_bytes,
        name="V4 replay projection",
    )


def _require_policy_cursor(
    connection: sqlite3.Connection,
    sequence: int,
    checkpoint_hash: str,
) -> None:
    row = connection.execute(
        "SELECT current_checkpoint_sequence_be, current_checkpoint_hash "
        "FROM spot_v7_operational_policy_v4 WHERE singleton = 1"
    ).fetchone()
    if row is None or (
        int.from_bytes(bytes(row["current_checkpoint_sequence_be"]), "big") != sequence
        or _hex_hash(bytes(row["current_checkpoint_hash"])) != checkpoint_hash
    ):
        raise ValueError("Spot V7 V4 policy cursor disagrees with history")


def _require_binary_flags(
    row: sqlite3.Row,
    *,
    true_fields: tuple[str, ...],
    false_fields: tuple[str, ...],
) -> None:
    if any(int(row[field]) != 1 for field in true_fields) or any(
        int(row[field]) != 0 for field in false_fields
    ):
        raise ValueError("Spot V7 V4 scoped claim flag mismatch")


__all__ = ()
