"""Focused E05 expected-root CAS and uniqueness tests."""

from __future__ import annotations

import sqlite3

import pytest

from experiments.fcis_m6_e04_retry_classifier import (
    POST_STATE_ROOT_V1,
    build_attempt,
    build_reopen_receipt,
    build_state,
)
from experiments.fcis_m6_e05_expected_root_cas import (
    E05DurableStateV1,
    E05StorageError,
    create_database,
    publish,
    read_state,
)
from src.core.fcis_m6_e05_expected_root_cas import (
    E05CodeV1,
    E05Error,
    E05PublicationRequestV1,
    E05RejectV1,
)


def _fixture() -> tuple[sqlite3.Connection, E05PublicationRequestV1]:
    attempt = build_attempt()
    pre_state = build_state()
    post_state = build_state(
        attempts=((attempt, POST_STATE_ROOT_V1),),
        current_state_root=POST_STATE_ROOT_V1,
    )
    request = E05PublicationRequestV1(
        attempt=attempt,
        pre_state=pre_state,
        post_state=post_state,
        reopen_receipt=build_reopen_receipt(pre_state),
    )
    return create_database(pre_state), request


def _reject(result: object, code: E05CodeV1) -> E05RejectV1:
    assert isinstance(result, E05RejectV1)
    value = result
    assert value.code is code
    return value


def test_single_transaction_commits_complete_publication_and_effect() -> None:
    connection, request = _fixture()
    result = publish(connection, request)

    assert getattr(result, "publication_sequence", None) == 1
    state = read_state(connection)
    assert type(state) is E05DurableStateV1
    assert state.current_state_root == request.post_state.current_state_root
    assert state.snapshot_root == request.post_state.snapshot_root
    assert len(state.publications) == 1
    row = state.publications[0]
    assert row.attempt_root == request.attempt.attempt_root
    assert row.fingerprint == request.attempt.fingerprint
    assert row.commit_id == request.attempt.commit.commit_id
    assert row.nullifier_root == request.attempt.commit.nullifier.nullifier_root
    assert len(row.effects) == len(request.attempt.commit.effects)
    assert connection.execute("SELECT COUNT(*) FROM e05_publications").fetchone()[0] == 1
    assert connection.execute("SELECT COUNT(*) FROM e05_nullifiers").fetchone()[0] == 1
    assert connection.execute("SELECT COUNT(*) FROM e05_effects").fetchone()[0] == 1


def test_retry_with_old_pre_state_is_a_stale_snapshot_no_op() -> None:
    connection, request = _fixture()
    assert getattr(publish(connection, request), "publication_sequence", None) == 1
    before = read_state(connection)

    result = publish(connection, request)

    _reject(result, E05CodeV1.STALE_SNAPSHOT_CAS)
    assert read_state(connection) == before


def test_authority_epoch_and_root_are_part_of_the_sql_cas() -> None:
    connection, request = _fixture()
    connection.execute("UPDATE e05_head SET authority_epoch_index = authority_epoch_index + 1")
    before = read_state(connection)

    result = publish(connection, request)

    _reject(result, E05CodeV1.STALE_AUTHORITY_CAS)
    assert read_state(connection) == before
    assert connection.execute("SELECT COUNT(*) FROM e05_publications").fetchone()[0] == 0


def test_current_state_root_is_part_of_the_sql_cas() -> None:
    connection, request = _fixture()
    connection.execute("UPDATE e05_head SET current_state_root = ?", ("f" * 64,))
    before = read_state(connection)

    result = publish(connection, request)

    _reject(result, E05CodeV1.STALE_STATE_CAS)
    assert read_state(connection) == before
    assert connection.execute("SELECT COUNT(*) FROM e05_nullifiers").fetchone()[0] == 0


def test_cas_starts_before_any_datastore_read() -> None:
    connection, request = _fixture()
    statements: list[str] = []
    connection.set_trace_callback(statements.append)

    result = publish(connection, request)

    assert getattr(result, "publication_sequence", None) == 1
    normalized = [statement.strip().upper() for statement in statements]
    assert normalized[0] == "BEGIN IMMEDIATE"
    update_index = next(
        index for index, item in enumerate(normalized) if item.startswith("UPDATE E05_HEAD")
    )
    select_indices = [index for index, item in enumerate(normalized) if item.startswith("SELECT")]
    assert select_indices
    assert normalized[update_index].startswith("UPDATE E05_HEAD")


def test_trigger_abort_rolls_back_head_and_all_unique_rows() -> None:
    connection, request = _fixture()
    before = read_state(connection)
    connection.execute(
        """
        CREATE TRIGGER force_e05_abort
        AFTER INSERT ON e05_nullifiers
        BEGIN
            SELECT RAISE(ABORT, 'forced E05 abort');
        END
        """
    )

    result = publish(connection, request)

    _reject(result, E05CodeV1.SQL_ROLLBACK)
    assert read_state(connection) == before
    for table in ("e05_publications", "e05_nullifiers", "e05_effects"):
        assert connection.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0] == 0


def test_effect_uniqueness_is_owned_by_the_sql_schema() -> None:
    connection, request = _fixture()
    assert getattr(publish(connection, request), "publication_sequence", None) == 1
    with pytest.raises(sqlite3.IntegrityError):
        connection.execute(
            """
            INSERT INTO e05_effects(
                effect_id, commit_id, ordinal, destination, payload_root,
                writer_profile_root, adapter_profile_root
            ) SELECT effect_id, commit_id, ordinal, destination, payload_root,
                         writer_profile_root, adapter_profile_root
            FROM e05_effects LIMIT 1
            """
        )


def test_forged_state_cannot_cross_the_e05_boundary() -> None:
    connection, request = _fixture()
    forged = object.__new__(type(request.pre_state))
    object.__setattr__(forged, "genesis_state_root", request.pre_state.genesis_state_root)
    object.__setattr__(forged, "current_state_root", request.pre_state.current_state_root)
    object.__setattr__(forged, "authority_epoch_index", request.pre_state.authority_epoch_index)
    object.__setattr__(forged, "authority_state_root", request.pre_state.authority_state_root)
    object.__setattr__(forged, "allowed_writer_roots", request.pre_state.allowed_writer_roots)
    object.__setattr__(forged, "deployment_config_root", request.pre_state.deployment_config_root)
    object.__setattr__(forged, "verifier_profile_root", request.pre_state.verifier_profile_root)
    object.__setattr__(forged, "commits", request.pre_state.commits)
    object.__setattr__(forged, "snapshot_root", "f" * 64)

    with pytest.raises(E05Error, match="provenance"):
        E05PublicationRequestV1(
            attempt=request.attempt,
            pre_state=forged,
            post_state=request.post_state,
            reopen_receipt=request.reopen_receipt,
        )
    assert read_state(connection).publications == ()


def test_reopen_receipt_mismatch_is_rejected_before_begin() -> None:
    connection, request = _fixture()
    other_attempt = build_attempt()
    other = build_state(
        attempts=((other_attempt, POST_STATE_ROOT_V1),),
        current_state_root=POST_STATE_ROOT_V1,
    )
    with pytest.raises(E05Error, match="crossed"):
        E05PublicationRequestV1(
            attempt=request.attempt,
            pre_state=request.pre_state,
            post_state=request.post_state,
            reopen_receipt=build_reopen_receipt(other),
        )
    assert read_state(connection).publications == ()


def test_seeded_state_reopens_all_prior_publication_rows() -> None:
    attempt = build_attempt()
    seeded = build_state(
        attempts=((attempt, POST_STATE_ROOT_V1),),
        current_state_root=POST_STATE_ROOT_V1,
    )
    connection = create_database(seeded)
    state = read_state(connection)

    assert len(state.publications) == 1
    assert state.publications[0].attempt_root == attempt.attempt_root
    assert state.next_publication_sequence == 2


def test_nested_attempt_wire_mutation_is_rejected_on_reopen() -> None:
    connection, request = _fixture()
    assert getattr(publish(connection, request), "publication_sequence", None) == 1
    connection.execute(
        "UPDATE e05_publications SET attempt_wire = ?",
        (b'{"attempt_root":"' + (b"f" * 64) + b'"}',),
    )

    with pytest.raises(E05StorageError, match="canonical object|unexpected field"):
        read_state(connection)


def test_missing_effect_or_crossed_nullifier_is_rejected_on_reopen() -> None:
    connection, request = _fixture()
    assert getattr(publish(connection, request), "publication_sequence", None) == 1
    connection.execute("DELETE FROM e05_effects")
    with pytest.raises(E05StorageError, match="effect cardinality"):
        read_state(connection)

    connection, request = _fixture()
    assert getattr(publish(connection, request), "publication_sequence", None) == 1
    connection.execute("UPDATE e05_nullifiers SET fingerprint = ?", ("f" * 64,))
    with pytest.raises(E05StorageError, match="nullifier projections"):
        read_state(connection)
