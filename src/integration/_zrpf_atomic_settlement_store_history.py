"""Restart validation for atomicity-only ZRPF settlement-plan history."""

from __future__ import annotations

import sqlite3
from typing import Any

from src.core._zrpf_settlement_commit_authority import (
    SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
)
from src.core.zrpf_settlement_effect_plan import SettlementEffectPlanV1
from src.integration._zrpf_atomic_settlement_plan_codec import (
    _decode_canonical_settlement_plan_v1,
)
from src.integration.recursive_stark_admission_store_types import _hash_bytes, _hex_hash
from src.state.canonical import canonical_json_bytes


def _validate_complete_settlement_history(
    connection: sqlite3.Connection,
    *,
    genesis_state_root: bytes,
) -> None:
    if not connection.in_transaction:
        raise ValueError("settlement history validation requires an existing transaction")
    previous_state_root = genesis_state_root
    rows = connection.execute("SELECT * FROM zrpf_settlement_plans ORDER BY settlement_revision")
    observed_count = 0
    for expected_revision, row in enumerate(rows, start=1):
        observed_count = expected_revision
        if int(row["settlement_revision"]) != expected_revision:
            raise ValueError("settlement revisions must be dense")
        if int(row["admission_revision"]) != expected_revision:
            raise ValueError("settlement admission revision link mismatch")
        if bytes(row["previous_state_root"]) != previous_state_root:
            raise ValueError("settlement previous-state history link mismatch")
        plan = _decode_canonical_settlement_plan_v1(bytes(row["canonical_plan"]))
        if _hash_bytes(plan.commitment, name="recomputed plan commitment") != bytes(
            row["plan_commitment"]
        ):
            raise ValueError("settlement plan commitment mismatch")
        _validate_header_against_plan(row, plan)
        _validate_plan_sequences(connection, bytes(row["plan_commitment"]), plan)
        previous_state_root = bytes(row["result_state_root"])

    meta = connection.execute("SELECT * FROM zrpf_settlement_meta WHERE singleton = 1").fetchone()
    if meta is None:
        raise ValueError("settlement metadata row is missing")
    if int(meta["revision"]) != observed_count or int(meta["plan_count"]) != observed_count:
        raise ValueError("settlement metadata head count mismatch")
    expected_state_root = previous_state_root if observed_count else genesis_state_root
    if bytes(meta["state_root"]) != expected_state_root:
        raise ValueError("settlement metadata state root does not match history")
    if int(meta["settlement_authority"]) != 0:
        raise ValueError("settlement history authority must remain false")
    if str(meta["authority_blocked_reason"]) != SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1:
        raise ValueError("settlement history blocked reason mismatch")


def _validate_coupled_admission_settlement_history(connection: sqlite3.Connection) -> None:
    """Require one settlement plan at the same revision as every admission."""

    replay_meta = connection.execute(
        "SELECT revision, root_count FROM zrpf_store_meta WHERE singleton = 1"
    ).fetchone()
    settlement_meta = connection.execute(
        "SELECT revision, plan_count FROM zrpf_settlement_meta WHERE singleton = 1"
    ).fetchone()
    if replay_meta is None or settlement_meta is None:
        raise ValueError("coupled settlement metadata is missing")
    replay_revision = int(replay_meta["revision"])
    settlement_revision = int(settlement_meta["revision"])
    if replay_revision != settlement_revision:
        raise ValueError("admission and settlement history revisions diverge")
    if int(replay_meta["root_count"]) != int(settlement_meta["plan_count"]):
        raise ValueError("admission and settlement history counts diverge")
    mismatched = connection.execute(
        """
        SELECT 1
        FROM zrpf_admissions AS admission
        LEFT JOIN zrpf_settlement_plans AS plan
          ON plan.root_journal_hash = admission.root_journal_hash
         AND plan.admission_revision = admission.revision
         AND plan.settlement_revision = admission.revision
        WHERE plan.plan_commitment IS NULL
        LIMIT 1
        """
    ).fetchone()
    if mismatched is not None:
        raise ValueError("admission and settlement plan linkage mismatch")


def _validate_header_against_plan(row: sqlite3.Row, plan: SettlementEffectPlanV1) -> None:
    scalar_hash_fields = {
        "application_id": "application_id",
        "chain_or_domain_id": "chain_or_domain_id",
        "source_root_journal_hash": "root_journal_hash",
        "public_policy_hash": "public_policy_hash",
        "pre_state_root": "previous_state_root",
        "post_state_root": "result_state_root",
        "economic_action_ids_root": "economic_action_ids_root",
        "ledger_cell_writes_root": "ledger_cell_writes_root",
        "asset_effects_root": "asset_effects_root",
        "authorization_consumptions_root": "authorization_consumptions_root",
        "authorization_nullifiers_root": "authorization_nullifiers_root",
        "authorization_grant_spend_nullifiers_root": ("authorization_grant_spend_nullifiers_root"),
        "message_effects_root": "message_effects_root",
        "carry_effects_root": "carry_effects_root",
        "reward_effects_root": "reward_effects_root",
    }
    for plan_name, row_name in scalar_hash_fields.items():
        value = getattr(plan, plan_name)
        if _hash_bytes(value, name=f"stored plan {plan_name}") != bytes(row[row_name]):
            raise ValueError(f"stored settlement header {plan_name} mismatch")
    if plan.epoch_id.to_bytes(8, "big") != bytes(row["epoch_id_be"]):
        raise ValueError("stored settlement epoch mismatch")
    if int(row["settlement_authority"]) != 0:
        raise ValueError("stored settlement plan authority must remain false")
    if str(row["authority_blocked_reason"]) != SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1:
        raise ValueError("stored settlement plan blocked reason mismatch")


def _validate_plan_sequences(
    connection: sqlite3.Connection,
    plan_commitment: bytes,
    plan: SettlementEffectPlanV1,
) -> None:
    plan_obj = plan.to_commitment_obj()
    action_ids = _require_list(plan_obj, "economic_action_ids")
    action_rows = connection.execute(
        """
        SELECT ordinal, economic_action_id FROM zrpf_settlement_economic_actions
        WHERE plan_commitment = ? ORDER BY ordinal
        """,
        (plan_commitment,),
    ).fetchall()
    _require_dense_ordinals(action_rows, len(action_ids), "economic actions")
    observed_actions = [_hex_hash(bytes(row["economic_action_id"])) for row in action_rows]
    if observed_actions != action_ids:
        raise ValueError("stored settlement economic actions mismatch canonical plan")

    record_specs = (
        ("ledger_cell_writes", "zrpf_settlement_cell_writes", (), ("cell_key",)),
        ("asset_effects", "zrpf_settlement_asset_effects", ("effect_id",), ()),
        (
            "authorization_consumptions",
            "zrpf_settlement_authorization_consumptions",
            ("authorization_nullifier", "authorization_grant_spend_nullifier"),
            (),
        ),
        ("message_effects", "zrpf_settlement_message_effects", ("message_id",), ()),
        ("carry_effects", "zrpf_settlement_carry_effects", ("carry_id",), ()),
        ("reward_effects", "zrpf_settlement_reward_effects", ("reward_id",), ()),
    )
    for plan_name, table, id_columns, extra_columns in record_specs:
        records = _require_list(plan_obj, plan_name)
        columns = (
            ("ordinal", "economic_action_id") + id_columns + extra_columns + ("canonical_record",)
        )
        rows = connection.execute(
            f"SELECT {', '.join(columns)} FROM {table} WHERE plan_commitment = ? ORDER BY ordinal",
            (plan_commitment,),
        ).fetchall()
        _require_dense_ordinals(rows, len(records), plan_name)
        for ordinal, (record, stored) in enumerate(zip(records, rows, strict=True)):
            if type(record) is not dict:
                raise ValueError(f"stored settlement {plan_name}[{ordinal}] is not an object")
            if bytes(stored["canonical_record"]) != canonical_json_bytes(record):
                raise ValueError(f"stored settlement {plan_name} record mismatch")
            _require_record_identifier(stored, record, "economic_action_id", plan_name)
            for column in id_columns + extra_columns:
                _require_record_identifier(stored, record, column, plan_name)


def _require_record_identifier(
    row: sqlite3.Row,
    record: dict[str, Any],
    column: str,
    plan_name: str,
) -> None:
    value = record.get(column)
    if type(value) is not str:
        raise ValueError(f"stored settlement {plan_name} {column} is not a hash")
    if _hash_bytes(value, name=f"stored {plan_name} {column}") != bytes(row[column]):
        raise ValueError(f"stored settlement {plan_name} {column} mismatch")


def _require_list(plan: dict[str, Any], name: str) -> list[Any]:
    value = plan.get(name)
    if type(value) is not list:
        raise ValueError(f"stored settlement plan {name} must be a list")
    return value


def _require_dense_ordinals(
    rows: list[sqlite3.Row],
    expected_count: int,
    name: str,
) -> None:
    if len(rows) != expected_count:
        raise ValueError(f"stored settlement {name} count mismatch")
    if [int(row["ordinal"]) for row in rows] != list(range(expected_count)):
        raise ValueError(f"stored settlement {name} ordinals must be dense")
