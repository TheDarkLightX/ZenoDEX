"""Deterministic row mechanics for the atomicity-only ZRPF settlement store."""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass

from src.core._zrpf_settlement_commit_authority import (
    SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    _AuthenticatedSettlementCommitV1,
)
from src.core.zrpf_settlement_effect_plan import SettlementEffectPlanV1
from src.integration.recursive_stark_admission_store_types import _hash_bytes, _hex_hash
from src.integration.zrpf_atomic_settlement_store_types import (
    MAX_SETTLEMENT_REVISION_V1,
    DurableZrpfSettlementCursorV1,
    DurableZrpfSettlementReceiptV1,
    ZrpfAtomicSettlementRejectReasonV1,
    ZrpfAtomicSettlementStoreErrorV1,
)
from src.state.canonical import canonical_json_bytes

_OVERLAP_SPECS = (
    (
        1,
        "zrpf_settlement_economic_actions",
        "economic_action_id",
        ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_ECONOMIC_ACTION,
    ),
    (
        2,
        "zrpf_settlement_authorization_consumptions",
        "authorization_nullifier",
        ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_AUTHORIZATION_NULLIFIER,
    ),
    (
        3,
        "zrpf_settlement_authorization_consumptions",
        "authorization_grant_spend_nullifier",
        ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_AUTHORIZATION_GRANT_SPEND,
    ),
    (
        4,
        "zrpf_settlement_asset_effects",
        "effect_id",
        ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_ASSET_EFFECT,
    ),
    (
        5,
        "zrpf_settlement_message_effects",
        "message_id",
        ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_MESSAGE_EFFECT,
    ),
    (
        6,
        "zrpf_settlement_carry_effects",
        "carry_id",
        ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_CARRY_EFFECT,
    ),
    (
        7,
        "zrpf_settlement_reward_effects",
        "reward_id",
        ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_REWARD_EFFECT,
    ),
)

_ALLOWED_RECORD_TABLES = {
    "zrpf_settlement_cell_writes",
    "zrpf_settlement_asset_effects",
    "zrpf_settlement_authorization_consumptions",
    "zrpf_settlement_message_effects",
    "zrpf_settlement_carry_effects",
    "zrpf_settlement_reward_effects",
}


@dataclass(frozen=True, slots=True)
class _SettlementRecordBatchV1:
    table: str
    id_columns: tuple[str, ...]
    id_values: tuple[tuple[str, ...], ...]
    action_ids: tuple[str, ...]
    records: tuple[dict[str, object], ...]
    extra_columns: tuple[str, ...] = ()
    extra_values: tuple[tuple[str, ...], ...] = ()


def _read_settlement_cursor(connection: sqlite3.Connection) -> DurableZrpfSettlementCursorV1:
    row = connection.execute(
        "SELECT revision, state_root, plan_count FROM zrpf_settlement_meta WHERE singleton = 1"
    ).fetchone()
    if row is None:
        raise ValueError("atomic settlement metadata row is missing")
    return DurableZrpfSettlementCursorV1(
        revision=int(row["revision"]),
        state_root=_hex_hash(bytes(row["state_root"])),
        plan_count=int(row["plan_count"]),
    )


def _next_settlement_cursor(
    previous: DurableZrpfSettlementCursorV1,
    plan: SettlementEffectPlanV1,
) -> DurableZrpfSettlementCursorV1:
    revision = previous.revision + 1
    if revision > MAX_SETTLEMENT_REVISION_V1:
        raise ValueError("atomic settlement revision capacity exceeded")
    return DurableZrpfSettlementCursorV1(
        revision=revision,
        state_root=plan.post_state_root,
        plan_count=revision,
    )


def _settlement_overlap_reason(
    connection: sqlite3.Connection,
    plan: SettlementEffectPlanV1,
) -> ZrpfAtomicSettlementRejectReasonV1 | None:
    _stage_incoming_settlement_ids(connection, plan)
    for kind, table, column, reason in _OVERLAP_SPECS:
        found = connection.execute(
            f"""
            SELECT 1 FROM temp.zrpf_settlement_incoming_ids AS incoming
            JOIN {table} AS stored ON stored.{column} = incoming.identifier
            WHERE incoming.kind = ? LIMIT 1
            """,
            (kind,),
        ).fetchone()
        if found is not None:
            return reason
    return None


def _stage_incoming_settlement_ids(
    connection: sqlite3.Connection,
    plan: SettlementEffectPlanV1,
) -> None:
    connection.execute(
        "CREATE TEMP TABLE IF NOT EXISTS zrpf_settlement_incoming_ids "
        "(kind INTEGER NOT NULL, identifier BLOB NOT NULL, PRIMARY KEY (kind, identifier)) "
        "WITHOUT ROWID"
    )
    connection.execute("DELETE FROM temp.zrpf_settlement_incoming_ids")
    rows: list[tuple[int, bytes]] = []
    rows.extend(
        (1, _hash_bytes(value, name="economic action")) for value in plan.economic_action_ids
    )
    rows.extend(
        (2, _hash_bytes(row.authorization_nullifier, name="authorization nullifier"))
        for row in plan.authorization_consumptions
    )
    rows.extend(
        (
            3,
            _hash_bytes(
                row.authorization_grant_spend_nullifier,
                name="authorization grant spend nullifier",
            ),
        )
        for row in plan.authorization_consumptions
    )
    rows.extend((4, _hash_bytes(row.effect_id, name="asset effect")) for row in plan.asset_effects)
    rows.extend(
        (5, _hash_bytes(row.message_id, name="message effect")) for row in plan.message_effects
    )
    rows.extend((6, _hash_bytes(row.carry_id, name="carry effect")) for row in plan.carry_effects)
    rows.extend(
        (7, _hash_bytes(row.reward_id, name="reward effect")) for row in plan.reward_effects
    )
    connection.executemany(
        "INSERT INTO temp.zrpf_settlement_incoming_ids (kind, identifier) VALUES (?, ?)",
        rows,
    )


def _persist_settlement_header(
    connection: sqlite3.Connection,
    authenticated: _AuthenticatedSettlementCommitV1,
    next_cursor: DurableZrpfSettlementCursorV1,
) -> None:
    plan = authenticated.plan
    connection.execute(
        """
        INSERT INTO zrpf_settlement_plans (
            plan_commitment, root_journal_hash, admission_revision, settlement_revision,
            application_id, chain_or_domain_id, epoch_id_be, public_policy_hash,
            previous_state_root, result_state_root, economic_action_ids_root,
            ledger_cell_writes_root, asset_effects_root,
            authorization_consumptions_root, authorization_nullifiers_root,
            authorization_grant_spend_nullifiers_root, message_effects_root,
            carry_effects_root, reward_effects_root, canonical_plan,
            settlement_authority, authority_blocked_reason
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, ?)
        """,
        (
            _hash_bytes(plan.commitment, name="plan commitment"),
            _hash_bytes(plan.source_root_journal_hash, name="source root journal hash"),
            next_cursor.revision,
            next_cursor.revision,
            _hash_bytes(plan.application_id, name="application_id"),
            _hash_bytes(plan.chain_or_domain_id, name="chain_or_domain_id"),
            plan.epoch_id.to_bytes(8, "big"),
            _hash_bytes(plan.public_policy_hash, name="public_policy_hash"),
            _hash_bytes(plan.pre_state_root, name="pre_state_root"),
            _hash_bytes(plan.post_state_root, name="post_state_root"),
            _hash_bytes(plan.economic_action_ids_root, name="economic action IDs root"),
            _hash_bytes(plan.ledger_cell_writes_root, name="cell writes root"),
            _hash_bytes(plan.asset_effects_root, name="asset effects root"),
            _hash_bytes(
                plan.authorization_consumptions_root,
                name="authorization consumptions root",
            ),
            _hash_bytes(plan.authorization_nullifiers_root, name="authorization root"),
            _hash_bytes(
                plan.authorization_grant_spend_nullifiers_root,
                name="grant spend root",
            ),
            _hash_bytes(plan.message_effects_root, name="message effects root"),
            _hash_bytes(plan.carry_effects_root, name="carry effects root"),
            _hash_bytes(plan.reward_effects_root, name="reward effects root"),
            plan.canonical_bytes(),
            SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
        ),
    )


def _persist_settlement_actions(
    connection: sqlite3.Connection,
    plan: SettlementEffectPlanV1,
) -> None:
    commitment = _hash_bytes(plan.commitment, name="plan commitment")
    connection.executemany(
        """
        INSERT INTO zrpf_settlement_economic_actions (
            economic_action_id, plan_commitment, ordinal
        ) VALUES (?, ?, ?)
        """,
        (
            (_hash_bytes(action_id, name="economic action"), commitment, ordinal)
            for ordinal, action_id in enumerate(plan.economic_action_ids)
        ),
    )


def _persist_settlement_rows(
    connection: sqlite3.Connection,
    plan: SettlementEffectPlanV1,
) -> None:
    commitment = _hash_bytes(plan.commitment, name="plan commitment")
    for batch in _record_batches(plan):
        _insert_record_rows(connection, batch, commitment)


def _record_batches(plan: SettlementEffectPlanV1) -> tuple[_SettlementRecordBatchV1, ...]:
    return (
        _cell_write_batch(plan),
        _asset_effect_batch(plan),
        _authorization_batch(plan),
        _message_batch(plan),
        _carry_batch(plan),
        _reward_batch(plan),
    )


def _cell_write_batch(plan: SettlementEffectPlanV1) -> _SettlementRecordBatchV1:
    rows = plan.ledger_cell_writes
    return _SettlementRecordBatchV1(
        table="zrpf_settlement_cell_writes",
        id_columns=(),
        id_values=((),) * len(rows),
        action_ids=tuple(row.economic_action_id for row in rows),
        records=tuple(row.to_commitment_obj() for row in rows),
        extra_columns=("cell_key",),
        extra_values=tuple((row.cell_key,) for row in rows),
    )


def _asset_effect_batch(plan: SettlementEffectPlanV1) -> _SettlementRecordBatchV1:
    rows = plan.asset_effects
    return _SettlementRecordBatchV1(
        table="zrpf_settlement_asset_effects",
        id_columns=("effect_id",),
        id_values=tuple((row.effect_id,) for row in rows),
        action_ids=tuple(row.economic_action_id for row in rows),
        records=tuple(row.to_commitment_obj() for row in rows),
    )


def _authorization_batch(plan: SettlementEffectPlanV1) -> _SettlementRecordBatchV1:
    rows = plan.authorization_consumptions
    return _SettlementRecordBatchV1(
        table="zrpf_settlement_authorization_consumptions",
        id_columns=("authorization_nullifier", "authorization_grant_spend_nullifier"),
        id_values=tuple(
            (row.authorization_nullifier, row.authorization_grant_spend_nullifier) for row in rows
        ),
        action_ids=tuple(row.economic_action_id for row in rows),
        records=tuple(row.to_commitment_obj() for row in rows),
    )


def _message_batch(plan: SettlementEffectPlanV1) -> _SettlementRecordBatchV1:
    rows = plan.message_effects
    return _SettlementRecordBatchV1(
        table="zrpf_settlement_message_effects",
        id_columns=("message_id",),
        id_values=tuple((row.message_id,) for row in rows),
        action_ids=tuple(row.economic_action_id for row in rows),
        records=tuple(row.to_commitment_obj() for row in rows),
    )


def _carry_batch(plan: SettlementEffectPlanV1) -> _SettlementRecordBatchV1:
    rows = plan.carry_effects
    return _SettlementRecordBatchV1(
        table="zrpf_settlement_carry_effects",
        id_columns=("carry_id",),
        id_values=tuple((row.carry_id,) for row in rows),
        action_ids=tuple(row.economic_action_id for row in rows),
        records=tuple(row.to_commitment_obj() for row in rows),
    )


def _reward_batch(plan: SettlementEffectPlanV1) -> _SettlementRecordBatchV1:
    rows = plan.reward_effects
    return _SettlementRecordBatchV1(
        table="zrpf_settlement_reward_effects",
        id_columns=("reward_id",),
        id_values=tuple((row.reward_id,) for row in rows),
        action_ids=tuple(row.economic_action_id for row in rows),
        records=tuple(row.to_commitment_obj() for row in rows),
    )


def _insert_record_rows(
    connection: sqlite3.Connection,
    batch: _SettlementRecordBatchV1,
    commitment: bytes,
) -> None:
    if batch.table not in _ALLOWED_RECORD_TABLES:
        raise ValueError("unsupported settlement record table")
    if batch.extra_columns:
        extra_rows = batch.extra_values
    else:
        extra_rows = ((),) * len(batch.records)
    lengths = (len(batch.id_values), len(batch.action_ids), len(batch.records), len(extra_rows))
    if len(set(lengths)) != 1:
        raise ValueError("settlement record columns have inconsistent lengths")
    columns = (
        batch.id_columns
        + ("plan_commitment", "ordinal", "economic_action_id")
        + batch.extra_columns
        + ("canonical_record",)
    )
    placeholders = ", ".join("?" for _ in columns)
    sql = f"INSERT INTO {batch.table} ({', '.join(columns)}) VALUES ({placeholders})"
    values = []
    for ordinal, (ids, action_id, record, extras) in enumerate(
        zip(batch.id_values, batch.action_ids, batch.records, extra_rows, strict=True)
    ):
        values.append(
            (
                *(_hash_bytes(value, name=f"{batch.table} identifier") for value in ids),
                commitment,
                ordinal,
                _hash_bytes(action_id, name=f"{batch.table} economic action"),
                *(_hash_bytes(value, name=f"{batch.table} extra identifier") for value in extras),
                canonical_json_bytes(record),
            )
        )
    connection.executemany(sql, values)


def _cas_settlement_meta(
    connection: sqlite3.Connection,
    previous: DurableZrpfSettlementCursorV1,
    result: DurableZrpfSettlementCursorV1,
) -> None:
    cursor = connection.execute(
        """
        UPDATE zrpf_settlement_meta
        SET revision = ?, plan_count = ?, state_root = ?
        WHERE singleton = 1 AND revision = ? AND state_root = ?
          AND settlement_authority = 0 AND authority_blocked_reason = ?
        """,
        (
            result.revision,
            result.plan_count,
            _hash_bytes(result.state_root, name="result settlement state root"),
            previous.revision,
            _hash_bytes(previous.state_root, name="previous settlement state root"),
            SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
        ),
    )
    if cursor.rowcount != 1:
        raise ZrpfAtomicSettlementStoreErrorV1(
            "ATOMIC_SETTLEMENT_INTERNAL_CAS_FAILED",
            "serialized settlement metadata compare-and-swap changed no row",
        )


def _read_settlement_plan_row(
    connection: sqlite3.Connection,
    *,
    root_journal_hash: str,
) -> sqlite3.Row | None:
    return connection.execute(
        "SELECT * FROM zrpf_settlement_plans WHERE root_journal_hash = ?",
        (_hash_bytes(root_journal_hash, name="root journal hash"),),
    ).fetchone()


def _settlement_receipt_from_row(row: sqlite3.Row) -> DurableZrpfSettlementReceiptV1:
    return DurableZrpfSettlementReceiptV1(
        plan_commitment=_hex_hash(bytes(row["plan_commitment"])),
        root_journal_hash=_hex_hash(bytes(row["root_journal_hash"])),
        settlement_revision=int(row["settlement_revision"]),
        previous_state_root=_hex_hash(bytes(row["previous_state_root"])),
        result_state_root=_hex_hash(bytes(row["result_state_root"])),
        economic_action_ids_root=_hex_hash(bytes(row["economic_action_ids_root"])),
        authorization_nullifiers_root=_hex_hash(bytes(row["authorization_nullifiers_root"])),
        authorization_grant_spend_nullifiers_root=_hex_hash(
            bytes(row["authorization_grant_spend_nullifiers_root"])
        ),
        settlement_authority=bool(row["settlement_authority"]),
        authority_blocked_reason=str(row["authority_blocked_reason"]),
    )
