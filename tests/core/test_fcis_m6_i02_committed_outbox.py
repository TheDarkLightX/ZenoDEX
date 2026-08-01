"""I02 committed-outbox schema and operational-field tests."""

from __future__ import annotations

import json
import sqlite3
from pathlib import Path
from typing import Final

import pytest

from experiments.fcis_m6_h02_sqlite_publication import (
    ANFPublicationRowV1,
    H02Error,
    H02OutboxDeliveryRowV1,
    H02OutboxStatusV1,
    H02StorageError,
    create_database,
    read_outbox_delivery_rows,
    read_state,
)
from src.core.fcis_durable_retraction import (
    AuthorizedHistoryV1,
    DurableSnapshotV1,
    OutboxEffectV1,
    PublicationAtomV1,
    derive_effect_id,
    encode_history,
    initial_authority_state,
    tagged_digest,
)

_SCHEMA_PATH: Final[Path] = (
    Path(__file__).resolve().parents[2] / "docs/research/m6_tasks/TASK_I02_OUTBOX_SCHEMA_V1.json"
)


def test_i02_schema_matrix_matches_the_closed_operational_contract() -> None:
    payload = json.loads(_SCHEMA_PATH.read_text(encoding="utf-8"))
    assert payload["schema_version"] == "zenodex.fcis.m6.i02.outbox-schema.v1"
    assert payload["task_id"] == "I02"
    assert payload["operational_fields"] == [
        "status",
        "lease_owner",
        "lease_expiry",
        "attempt_count",
        "last_error",
        "ack_receipt_root",
    ]
    assert payload["transaction_rule"].startswith("semantic and operational")


def _snapshot_with_effect() -> tuple[
    DurableSnapshotV1,
    OutboxEffectV1,
    ANFPublicationRowV1,
]:
    authority = initial_authority_state(
        tagged_digest("i02/legacy-writer"),
        tagged_digest("i02/target-writer"),
    )
    genesis_root = tagged_digest("i02/genesis")
    commit_id = tagged_digest("i02/commit")
    payload_root = tagged_digest("i02/payload")
    effect = OutboxEffectV1(
        effect_id=derive_effect_id(
            commit_id=commit_id,
            ordinal=0,
            destination="i02-destination",
            payload_root=payload_root,
            writer_profile_root=authority.active_profile_root,
        ),
        ordinal=0,
        destination="i02-destination",
        payload_root=payload_root,
        adapter_profile_root=tagged_digest("i02/adapter"),
    )
    atom = PublicationAtomV1(
        sequence=1,
        commit_id=commit_id,
        command_root=tagged_digest("i02/command"),
        expected_pre_root=genesis_root,
        post_state_root=tagged_digest("i02/post-state"),
        writer_profile_root=authority.active_profile_root,
        authority_epoch_index=authority.epoch_index,
        authority_state_root=authority.root,
        nullifier_root=tagged_digest("i02/nullifier"),
        response_root=tagged_digest("i02/response"),
        receipt_root=tagged_digest("i02/receipt"),
        decision_root=tagged_digest("i02/decision"),
        bundle_root=tagged_digest("i02/bundle"),
        replay_root=tagged_digest("i02/replay"),
        outbox=(effect,),
    )
    history = AuthorizedHistoryV1(
        genesis_state_root=genesis_root,
        authority_epochs=(authority,),
        atoms=(atom,),
        acks=(),
    )
    snapshot = encode_history(history)
    anf_row = ANFPublicationRowV1(
        commit_id=commit_id,
        atom_root=atom.atom_root,
        anf_root=tagged_digest("i02/anf"),
    )
    return snapshot, effect, anf_row


def test_i02_committed_effect_gets_pending_operational_row() -> None:
    snapshot, effect, anf_row = _snapshot_with_effect()
    connection = create_database(snapshot, (anf_row,))
    try:
        rows = read_outbox_delivery_rows(connection, snapshot)
        assert rows == (
            H02OutboxDeliveryRowV1(
                effect_id=effect.effect_id,
                status=H02OutboxStatusV1.PENDING,
                lease_owner=None,
                lease_expiry=None,
                attempt_count=0,
                last_error=None,
                ack_receipt_root=None,
            ),
        )
        columns = {row[1] for row in connection.execute("PRAGMA table_info(publication_outbox)")}
        assert {
            "effect_id",
            "commit_id",
            "ordinal",
            "destination",
            "payload_root",
            "adapter_profile_root",
            "status",
            "lease_owner",
            "lease_expiry",
            "attempt_count",
            "last_error",
            "ack_receipt_root",
        } <= columns
    finally:
        connection.close()


def test_i02_operational_mutation_preserves_semantic_effect_identity() -> None:
    snapshot, effect, anf_row = _snapshot_with_effect()
    connection = create_database(snapshot, (anf_row,))
    try:
        connection.execute(
            """
            UPDATE publication_outbox
            SET status = 'LEASED', lease_owner = 'worker-i02',
                lease_expiry = 7, attempt_count = 1,
                last_error = 'retryable transport', ack_receipt_root = NULL
            WHERE effect_id = ?
            """,
            (effect.effect_id,),
        )
        state = read_state(connection)
        rows = read_outbox_delivery_rows(connection, state.snapshot)
        assert rows[0].status is H02OutboxStatusV1.LEASED
        assert rows[0].lease_owner == "worker-i02"
        assert rows[0].attempt_count == 1
        assert state.snapshot.outbox_rows[0].effect_id == effect.effect_id
        assert state.snapshot.outbox_rows[0].effect_id == derive_effect_id(
            commit_id=snapshot.atom_rows[0].commit_id,
            ordinal=effect.ordinal,
            destination=effect.destination,
            payload_root=effect.payload_root,
            writer_profile_root=snapshot.atom_rows[0].writer_profile_root,
        )
    finally:
        connection.close()


def test_i02_invalid_lease_and_ack_shapes_fail_closed() -> None:
    with pytest.raises(H02Error):
        H02OutboxDeliveryRowV1(
            effect_id=tagged_digest("i02/invalid-lease"),
            status=H02OutboxStatusV1.LEASED,
            lease_owner=None,
            lease_expiry=None,
            attempt_count=0,
            last_error=None,
            ack_receipt_root=None,
        )
    with pytest.raises(H02Error):
        H02OutboxDeliveryRowV1(
            effect_id=tagged_digest("i02/invalid-ack"),
            status=H02OutboxStatusV1.ACKED,
            lease_owner=None,
            lease_expiry=None,
            attempt_count=1,
            last_error=None,
            ack_receipt_root=None,
        )


def test_i02_sql_check_rejects_leased_row_without_lease_fields() -> None:
    snapshot, effect, anf_row = _snapshot_with_effect()
    connection = create_database(snapshot, (anf_row,))
    try:
        with pytest.raises(sqlite3.IntegrityError):
            connection.execute(
                "UPDATE publication_outbox SET status = 'LEASED' WHERE effect_id = ?",
                (effect.effect_id,),
            )
    finally:
        connection.close()


def test_i02_orphan_effect_without_an_atom_is_rejected() -> None:
    authority = initial_authority_state(
        tagged_digest("i02/orphan-legacy"),
        tagged_digest("i02/orphan-target"),
    )
    snapshot = encode_history(
        AuthorizedHistoryV1(
            genesis_state_root=tagged_digest("i02/orphan-genesis"),
            authority_epochs=(authority,),
            atoms=(),
            acks=(),
        )
    )
    connection = create_database(snapshot)
    orphan_commit = tagged_digest("i02/orphan-commit")
    orphan_effect = tagged_digest("i02/orphan-effect")
    try:
        connection.execute("PRAGMA foreign_keys = OFF")
        connection.execute(
            """
            INSERT INTO publication_outbox(
                effect_id, commit_id, ordinal, destination, payload_root,
                adapter_profile_root, status, lease_owner, lease_expiry,
                attempt_count, last_error, ack_receipt_root
            ) VALUES (?, ?, 0, 'orphan', ?, ?, 'PENDING', NULL, NULL, 0, NULL, NULL)
            """,
            (
                orphan_effect,
                orphan_commit,
                tagged_digest("i02/orphan-payload"),
                tagged_digest("i02/orphan-adapter"),
            ),
        )
        connection.execute("PRAGMA foreign_keys = ON")
        with pytest.raises(H02StorageError):
            read_state(connection)
    finally:
        connection.close()
