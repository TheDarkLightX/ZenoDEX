"""Focused E03 uniqueness, rollback, and concurrency tests."""

from __future__ import annotations

import sqlite3
import threading
from pathlib import Path
from typing import cast

import pytest

import src.core.fcis_m6_e03_unique_commit_port as e03_core
from experiments.fcis_m6_e03_database_uniqueness import (
    E03CommitV1,
    E03DatabaseCodeV1,
    E03RejectV1,
    create_e03_connection,
    persist_e03_commit,
    read_e03_counts,
)
from src.core.fcis_m6_e01_request_identity import (
    E01CommandFamilyV1,
    _mint_authenticated_command_v1,
    derive_request_identity_v1,
)
from src.core.fcis_m6_e02_nonce_nullifier import E02NullifierV1, derive_nonce_nullifier_v1
from src.core.fcis_m6_e03_unique_commit_port import (
    E03CommitIdentityV1,
    E03EffectSpecV1,
    E03Error,
    derive_e03_commit_identity_v1,
    is_verified_e03_commit_identity_v1,
)
from tools.build_fcis_m6_e03_database_uniqueness import build_candidate

_ROOT = "a" * 64
_OTHER_ROOT = "b" * 64
_PAYLOAD_ROOT = "c" * 64
_WRITER_ROOT = "d" * 64
_ADAPTER_ROOT = "e" * 64


def _effect(payload_root: str = _PAYLOAD_ROOT) -> E03EffectSpecV1:
    return E03EffectSpecV1(
        ordinal=0,
        destination="research-destination",
        payload_root=payload_root,
        writer_profile_root=_WRITER_ROOT,
        adapter_profile_root=_ADAPTER_ROOT,
    )


def _candidate(
    *,
    sequence: int = 1,
    commit_id: str,
    nullifier: object | None = None,
    payload_root: str = _PAYLOAD_ROOT,
) -> E03CommitIdentityV1:
    baseline = build_candidate()
    selected = baseline.nullifier if nullifier is None else cast(E02NullifierV1, nullifier)
    return derive_e03_commit_identity_v1(
        sequence=sequence,
        commit_id=commit_id,
        nullifier=selected,
        effects=(_effect(payload_root),),
    )


def _second_nullifier() -> E02NullifierV1:
    command = _mint_authenticated_command_v1(
        command_root=_OTHER_ROOT,
        sender_id="alice",
        command_family=E01CommandFamilyV1.STATE_CHANGE,
        nonce=8,
        authentication_profile_root=_ROOT,
        authentication_evidence_root=_OTHER_ROOT,
    )
    identity = derive_request_identity_v1(
        authenticated_command=command,
        deployment_config_root=_ROOT,
        expected_sequence=43,
        authority_epoch_index=3,
    )
    return derive_nonce_nullifier_v1(request_identity=identity, current_nonce=7)


def _assert_rejected(result: object, code: E03DatabaseCodeV1) -> E03RejectV1:
    assert type(result) is E03RejectV1
    rejected = cast(E03RejectV1, result)
    assert rejected.code is code
    return rejected


def test_candidate_derives_effect_and_fingerprint_from_complete_identity() -> None:
    candidate = build_candidate()
    assert is_verified_e03_commit_identity_v1(candidate)
    assert (
        candidate.fingerprint == "6cb9fdd797c4f1b462eaf9f65c19b07690a4092da32b844a942c026714555ad1"
    )
    assert candidate.effects[0].derive_effect_id(candidate.commit_id) == (
        "b9255903f7bdf3b4c49f89232d0d362289e72c0446e28491f17b7f1f0a2b7103"
    )
    changed = _candidate(commit_id=_ROOT, payload_root=_OTHER_ROOT)
    assert changed.fingerprint != candidate.fingerprint
    assert changed.effects[0].derive_effect_id(changed.commit_id) != (
        candidate.effects[0].derive_effect_id(candidate.commit_id)
    )


def test_constructor_forge_and_mutation_do_not_cross_authority_boundary() -> None:
    candidate = build_candidate()
    with pytest.raises(E03Error, match="verifier-owned"):
        E03CommitIdentityV1(
            sequence=candidate.sequence,
            commit_id=candidate.commit_id,
            nullifier=candidate.nullifier,
            effects=candidate.effects,
            fingerprint=candidate.fingerprint,
        )

    forged = object.__new__(E03CommitIdentityV1)
    for name in ("sequence", "commit_id", "nullifier", "effects", "fingerprint"):
        object.__setattr__(forged, name, object.__getattribute__(candidate, name))
    assert not is_verified_e03_commit_identity_v1(forged)

    object.__setattr__(candidate, "commit_id", _OTHER_ROOT)
    assert not is_verified_e03_commit_identity_v1(candidate)
    connection = create_e03_connection()
    _assert_rejected(persist_e03_commit(connection, candidate), E03DatabaseCodeV1.INVALID_REQUEST)


def test_candidate_replays_from_retained_sources_without_process_registry() -> None:
    candidate = build_candidate()
    assert not hasattr(e03_core, "_E03_COMMIT_REGISTRY_V1")
    assert not hasattr(e03_core, "_E03_COMMIT_SNAPSHOTS_V1")

    replayed = derive_e03_commit_identity_v1(
        sequence=candidate.sequence,
        commit_id=candidate.commit_id,
        nullifier=candidate.nullifier,
        effects=candidate.effects,
    )
    assert replayed is not candidate
    assert is_verified_e03_commit_identity_v1(replayed)
    assert replayed.to_wire() == candidate.to_wire()


def test_nested_effect_mutation_breaks_the_retained_fingerprint_seal() -> None:
    candidate = build_candidate()
    object.__setattr__(candidate.effects[0], "payload_root", _OTHER_ROOT)
    assert not is_verified_e03_commit_identity_v1(candidate)
    connection = create_e03_connection()
    _assert_rejected(persist_e03_commit(connection, candidate), E03DatabaseCodeV1.INVALID_REQUEST)


def test_closed_effect_bounds_and_order_reject() -> None:
    with pytest.raises(E03Error, match="ordinal"):
        E03EffectSpecV1(
            ordinal=True,
            destination="research-destination",
            payload_root=_PAYLOAD_ROOT,
            writer_profile_root=_WRITER_ROOT,
            adapter_profile_root=_ADAPTER_ROOT,
        )
    with pytest.raises(E03Error, match="control"):
        E03EffectSpecV1(
            ordinal=0,
            destination="bad\nvalue",
            payload_root=_PAYLOAD_ROOT,
            writer_profile_root=_WRITER_ROOT,
            adapter_profile_root=_ADAPTER_ROOT,
        )
    candidate = build_candidate()
    with pytest.raises(E03Error, match="exact tuple"):
        derive_e03_commit_identity_v1(
            sequence=1,
            commit_id=_ROOT,
            nullifier=candidate.nullifier,
            effects=cast(tuple[E03EffectSpecV1, ...], [_effect()]),
        )


def test_successful_insert_publishes_complete_identity_set() -> None:
    connection = create_e03_connection()
    result = persist_e03_commit(connection, build_candidate())
    assert type(result) is E03CommitV1
    assert read_e03_counts(connection) == (1, 1, 1)


def test_preexisting_loose_schema_is_rejected(tmp_path: Path) -> None:
    database = tmp_path / "e03-loose.sqlite3"
    connection = sqlite3.connect(database)
    connection.executescript(
        """
        CREATE TABLE e03_publication_commits (
            sequence INTEGER,
            commit_id TEXT,
            fingerprint TEXT,
            nullifier_root TEXT,
            request_identity_root TEXT
        );
        CREATE TABLE e03_publication_nullifiers (
            nullifier_root TEXT,
            commit_id TEXT,
            fingerprint TEXT
        );
        CREATE TABLE e03_publication_effects (
            effect_id TEXT,
            commit_id TEXT,
            ordinal INTEGER,
            destination TEXT,
            payload_root TEXT,
            writer_profile_root TEXT,
            adapter_profile_root TEXT
        );
        """
    )
    connection.close()

    with pytest.raises(E03Error, match="schema"):
        create_e03_connection(database)


def test_point_of_use_connection_contract_rejects_drift_without_writes() -> None:
    candidate = build_candidate()

    foreign_keys_off = create_e03_connection()
    foreign_keys_off.execute("PRAGMA foreign_keys = OFF")
    rejected = _assert_rejected(
        persist_e03_commit(foreign_keys_off, candidate),
        E03DatabaseCodeV1.INVALID_REQUEST,
    )
    assert rejected.path == ("connection", "foreign_keys")
    assert read_e03_counts(foreign_keys_off) == (0, 0, 0)

    schema_drift = create_e03_connection()
    schema_drift.execute(
        "CREATE TRIGGER hostile_e03_trigger AFTER INSERT ON e03_publication_commits BEGIN SELECT 1; END"
    )
    rejected = _assert_rejected(
        persist_e03_commit(schema_drift, candidate),
        E03DatabaseCodeV1.INVALID_REQUEST,
    )
    assert rejected.path == ("connection", "schema")
    assert read_e03_counts(schema_drift) == (0, 0, 0)


def test_active_caller_transaction_is_rejected_without_rollback() -> None:
    connection = create_e03_connection()
    connection.execute("CREATE TEMP TABLE caller_sentinel(value INTEGER NOT NULL)")
    connection.execute("BEGIN")
    connection.execute("INSERT INTO caller_sentinel(value) VALUES (7)")

    rejected = _assert_rejected(
        persist_e03_commit(connection, build_candidate()),
        E03DatabaseCodeV1.INVALID_REQUEST,
    )
    assert rejected.path == ("connection", "active_transaction")
    assert connection.in_transaction
    assert connection.execute("SELECT value FROM caller_sentinel").fetchone() == (7,)
    assert read_e03_counts(connection) == (0, 0, 0)
    connection.rollback()


def test_duplicate_commit_and_same_nullifier_collision_are_atomic() -> None:
    connection = create_e03_connection()
    first = build_candidate()
    assert type(persist_e03_commit(connection, first)) is E03CommitV1
    before = read_e03_counts(connection)

    _assert_rejected(
        persist_e03_commit(connection, first),
        E03DatabaseCodeV1.CONSTRAINT_COLLISION,
    )
    assert read_e03_counts(connection) == before

    same_nullifier = _candidate(sequence=2, commit_id=_OTHER_ROOT)
    _assert_rejected(
        persist_e03_commit(connection, same_nullifier),
        E03DatabaseCodeV1.CONSTRAINT_COLLISION,
    )
    assert read_e03_counts(connection) == before


def test_effect_primary_key_is_enforced_even_for_hostile_raw_insert() -> None:
    connection = create_e03_connection()
    first = build_candidate()
    second = _candidate(sequence=2, commit_id=_OTHER_ROOT, nullifier=_second_nullifier())
    assert type(persist_e03_commit(connection, first)) is E03CommitV1
    assert type(persist_e03_commit(connection, second)) is E03CommitV1
    effect = first.effects[0]
    with pytest.raises(sqlite3.IntegrityError, match="UNIQUE"):
        connection.execute("BEGIN")
        try:
            connection.execute(
                """
                INSERT INTO e03_publication_effects(
                    effect_id, commit_id, ordinal, destination, payload_root,
                    writer_profile_root, adapter_profile_root
                ) VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    effect.derive_effect_id(first.commit_id),
                    second.commit_id,
                    0,
                    effect.destination,
                    effect.payload_root,
                    effect.writer_profile_root,
                    effect.adapter_profile_root,
                ),
            )
        finally:
            connection.rollback()
    assert read_e03_counts(connection) == (2, 2, 2)


def test_partial_insert_failure_rolls_back_all_identity_rows() -> None:
    connection = create_e03_connection()

    def deny_nullifier_insert(
        action: int,
        argument_one: str | None,
        _argument_two: str | None,
        _database: str | None,
        _trigger: str | None,
    ) -> int:
        if action == sqlite3.SQLITE_INSERT and argument_one == "e03_publication_nullifiers":
            return sqlite3.SQLITE_DENY
        return sqlite3.SQLITE_OK

    connection.set_authorizer(deny_nullifier_insert)
    try:
        result = persist_e03_commit(connection, build_candidate())
    finally:
        connection.set_authorizer(None)
    _assert_rejected(result, E03DatabaseCodeV1.SQL_ROLLBACK)
    assert read_e03_counts(connection) == (0, 0, 0)


def test_concurrent_duplicate_insertions_have_one_winner(tmp_path: Path) -> None:
    database = tmp_path / "e03-concurrency.sqlite3"
    candidate = build_candidate()
    start = threading.Barrier(2)
    results: list[object] = []
    failures: list[BaseException] = []

    def worker() -> None:
        connection = create_e03_connection(database)
        try:
            start.wait(timeout=5)
            results.append(persist_e03_commit(connection, candidate))
        except BaseException as exc:  # pragma: no cover - diagnostic guard
            failures.append(exc)
        finally:
            connection.close()

    threads = (threading.Thread(target=worker), threading.Thread(target=worker))
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(timeout=10)
    assert not failures
    assert len(results) == 2
    committed = [result for result in results if type(result) is E03CommitV1]
    rejected = [result for result in results if type(result) is E03RejectV1]
    assert len(committed) == 1
    assert len(rejected) == 1
    assert cast(E03RejectV1, rejected[0]).code is E03DatabaseCodeV1.CONSTRAINT_COLLISION
    connection = create_e03_connection(database)
    assert read_e03_counts(connection) == (1, 1, 1)
