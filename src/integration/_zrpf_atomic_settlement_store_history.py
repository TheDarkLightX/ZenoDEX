"""Restart validation for atomicity-only ZRPF settlement-plan history."""

from __future__ import annotations

import hashlib
import sqlite3
from typing import Any

from src.core._zrpf_settlement_certificate_authority import (
    SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1,
)
from src.core._zrpf_settlement_commit_authority import (
    SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
)
from src.core.zrpf_settlement_effect_plan import SettlementEffectPlanV1
from src.integration._zrpf_atomic_settlement_plan_codec import (
    _decode_canonical_settlement_plan_v1,
)
from src.integration._zrpf_authenticated_certificate_store_engine import (
    _ACTION_LIST_DOMAIN,
    _CONSUMED_LIST_DOMAIN,
    _GRANT_LIST_DOMAIN,
    _identifier_list_digest,
    _read_identifier_sequence,
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


def _validate_authenticated_certificate_history(connection: sqlite3.Connection) -> None:
    """Replay certificate bindings and corruption checks during every restart."""

    if not connection.in_transaction:
        raise ValueError("certificate history validation requires an existing transaction")
    rows = connection.execute(
        """
        SELECT certificate.*, plan.epoch_id_be AS plan_epoch_id_be,
               plan.root_journal_hash AS plan_root_journal_hash,
               plan.application_id AS plan_application_id,
               plan.chain_or_domain_id AS plan_chain_or_domain_id,
               plan.public_policy_hash AS plan_public_policy_hash,
               plan.previous_state_root AS plan_previous_state_root,
               plan.result_state_root AS plan_result_state_root,
               plan.economic_action_ids_root AS plan_economic_action_ids_root,
               plan.ledger_cell_writes_root AS plan_ledger_cell_writes_root,
               plan.asset_effects_root AS plan_asset_effects_root,
               plan.message_effects_root AS plan_message_effects_root,
               plan.carry_effects_root AS plan_carry_effects_root,
               plan.reward_effects_root AS plan_reward_effects_root,
               admission.authority_manifest_sha256 AS admission_authority_manifest_sha256,
               admission.verifier_executable_sha256 AS admission_verifier_executable_sha256,
               admission.verification_request_sha256 AS admission_verification_request_sha256,
               admission.release_binding_config_digest AS admission_release_binding_digest,
               admission.replay_manifest_sha256 AS admission_replay_manifest_sha256
        FROM zrpf_settlement_certificates AS certificate
        JOIN zrpf_settlement_plans AS plan
          ON plan.plan_commitment = certificate.plan_commitment
         AND plan.settlement_revision = certificate.settlement_revision
        JOIN zrpf_admissions AS admission
          ON admission.root_journal_hash = certificate.semantic_root_journal_hash
        ORDER BY certificate.settlement_revision
        """
    ).fetchall()
    for row in rows:
        _validate_certificate_history_row(connection, row)


def _validate_certificate_history_row(
    connection: sqlite3.Connection,
    row: sqlite3.Row,
) -> None:
    _validate_certificate_epoch_link(connection, row)
    _validate_certificate_scalar_links(row)
    _validate_certificate_bytes_and_authority(row)
    _validate_certificate_identifier_lists(connection, row)
    _validate_certificate_root_identities(connection, row)


def _validate_certificate_epoch_link(
    connection: sqlite3.Connection,
    row: sqlite3.Row,
) -> None:
    revision = int(row["settlement_revision"])
    epoch = int.from_bytes(bytes(row["epoch_id_be"]), "big")
    if bytes(row["epoch_id_be"]) != bytes(row["plan_epoch_id_be"]):
        raise ValueError("certificate epoch does not match normalized plan")
    prior = connection.execute(
        "SELECT epoch_id_be FROM zrpf_settlement_plans WHERE settlement_revision = ?",
        (revision - 1,),
    ).fetchone()
    if prior is not None and epoch <= int.from_bytes(bytes(prior["epoch_id_be"]), "big"):
        raise ValueError("certificate epoch history is not strictly monotonic")


def _validate_certificate_scalar_links(row: sqlite3.Row) -> None:
    linked_columns = (
        ("semantic_root_journal_hash", "plan_root_journal_hash"),
        ("application_id", "plan_application_id"),
        ("chain_or_domain_id", "plan_chain_or_domain_id"),
        ("public_policy_hash", "plan_public_policy_hash"),
        ("pre_state_root", "plan_previous_state_root"),
        ("post_state_root", "plan_result_state_root"),
        ("economic_action_ids_root", "plan_economic_action_ids_root"),
        ("ledger_cell_writes_root", "plan_ledger_cell_writes_root"),
        ("asset_effects_root", "plan_asset_effects_root"),
        ("message_effects_root", "plan_message_effects_root"),
        ("carry_effects_root", "plan_carry_effects_root"),
        ("reward_effects_root", "plan_reward_effects_root"),
        ("authority_manifest_sha256", "admission_authority_manifest_sha256"),
        ("verifier_executable_sha256", "admission_verifier_executable_sha256"),
        ("verification_request_sha256", "admission_verification_request_sha256"),
        ("admission_policy_binding_sha256", "admission_release_binding_digest"),
        ("settlement_manifest_sha256", "admission_replay_manifest_sha256"),
    )
    for certificate_column, linked_column in linked_columns:
        if bytes(row[certificate_column]) != bytes(row[linked_column]):
            raise ValueError(f"certificate {certificate_column} linkage mismatch")


def _validate_certificate_bytes_and_authority(row: sqlite3.Row) -> None:
    if hashlib.sha256(bytes(row["canonical_certificate"])).digest() != bytes(
        row["canonical_certificate_sha256"]
    ):
        raise ValueError("canonical settlement certificate sha256 mismatch")
    if hashlib.sha256(bytes(row["exact_effect_plan"])).digest() != bytes(
        row["exact_effect_plan_sha256"]
    ):
        raise ValueError("exact settlement effect plan sha256 mismatch")
    if int(row["settlement_authority"]) != 0:
        raise ValueError("authenticated certificate authority must remain false")
    if (
        str(row["authority_blocked_reason"])
        != SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1
    ):
        raise ValueError("authenticated certificate blocked reason mismatch")


def _validate_certificate_identifier_lists(
    connection: sqlite3.Connection,
    row: sqlite3.Row,
) -> None:
    certificate_journal_hash = _hex_hash(bytes(row["certificate_journal_hash"]))
    action_nullifiers = _read_identifier_sequence(
        connection,
        table="zrpf_settlement_action_nullifiers",
        column="action_nullifier",
        certificate_journal_hash=certificate_journal_hash,
    )
    consumed_objects = _read_identifier_sequence(
        connection,
        table="zrpf_settlement_consumed_objects",
        column="consumed_object_id",
        certificate_journal_hash=certificate_journal_hash,
    )
    if _identifier_list_digest(_ACTION_LIST_DOMAIN, action_nullifiers) != bytes(
        row["action_nullifier_list_sha256"]
    ):
        raise ValueError("stored action nullifier list digest mismatch")
    if _identifier_list_digest(_CONSUMED_LIST_DOMAIN, consumed_objects) != bytes(
        row["consumed_object_id_list_sha256"]
    ):
        raise ValueError("stored consumed object list digest mismatch")

    grant_rows = connection.execute(
        """
        SELECT authorization_grant_spend_nullifier
        FROM zrpf_settlement_authorization_consumptions
        WHERE plan_commitment = ? ORDER BY ordinal
        """,
        (bytes(row["plan_commitment"]),),
    ).fetchall()
    grant_spends = tuple(
        _hex_hash(bytes(grant["authorization_grant_spend_nullifier"]))
        for grant in grant_rows
    )
    if _identifier_list_digest(_GRANT_LIST_DOMAIN, grant_spends) != bytes(
        row["authorization_grant_spend_list_sha256"]
    ):
        raise ValueError("stored authorization grant spend list digest mismatch")


def _validate_certificate_root_identities(
    connection: sqlite3.Connection,
    row: sqlite3.Row,
) -> None:
    root = bytes(row["semantic_root_journal_hash"])
    for column, table in (
        ("semantic_claim_hash", "zrpf_child_claims"),
        ("settlement_claim_hash", "zrpf_child_claims"),
        ("settlement_receipt_id", "zrpf_accepted_receipts"),
    ):
        found = connection.execute(
            f"SELECT 1 FROM {table} WHERE identifier = ? AND root_journal_hash = ?",
            (bytes(row[column]), root),
        ).fetchone()
        if found is None:
            raise ValueError(f"certificate {column} identity linkage missing")

    admission_messages = connection.execute(
        "SELECT identifier FROM zrpf_cross_shard_messages "
        "WHERE root_journal_hash = ? ORDER BY ordinal",
        (root,),
    ).fetchall()
    plan_messages = connection.execute(
        "SELECT message_id FROM zrpf_settlement_message_effects "
        "WHERE plan_commitment = ? ORDER BY ordinal",
        (bytes(row["plan_commitment"]),),
    ).fetchall()
    if [bytes(value[0]) for value in admission_messages] != [
        bytes(value[0]) for value in plan_messages
    ]:
        raise ValueError("certificate message identity linkage mismatch")


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
