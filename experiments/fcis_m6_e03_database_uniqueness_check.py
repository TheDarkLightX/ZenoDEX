"""Independent deterministic checks for the FCIS M6 E03 uniqueness packet."""

from __future__ import annotations

import hashlib
import json
import sqlite3
import sys
import threading
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

import src.core.fcis_m6_e03_unique_commit_port as e03_core  # noqa: E402
from experiments.fcis_m6_e03_database_uniqueness import (  # noqa: E402
    E03_MIGRATION_SHA256_V1,
    E03CommitV1,
    E03DatabaseCodeV1,
    E03RejectV1,
    create_e03_connection,
    persist_e03_commit,
    read_e03_counts,
)
from src.core.fcis_m6_e01_request_identity import (  # noqa: E402
    E01CommandFamilyV1,
    _mint_authenticated_command_v1,
    derive_request_identity_v1,
)
from src.core.fcis_m6_e02_nonce_nullifier import (  # noqa: E402
    E02NullifierV1,
    derive_nonce_nullifier_v1,
)
from src.core.fcis_m6_e03_unique_commit_port import (  # noqa: E402
    E03CommitIdentityV1,
    E03EffectSpecV1,
    E03Error,
    derive_e03_commit_identity_v1,
    is_verified_e03_commit_identity_v1,
)
from tools.build_fcis_m6_e03_database_uniqueness import (  # noqa: E402
    DEFAULT_OUTPUT_PATH,
    build_candidate,
    build_payload,
)


def _second_nullifier() -> E02NullifierV1:
    command = _mint_authenticated_command_v1(
        command_root="b" * 64,
        sender_id="alice",
        command_family=E01CommandFamilyV1.STATE_CHANGE,
        nonce=8,
        authentication_profile_root="a" * 64,
        authentication_evidence_root="b" * 64,
    )
    identity = derive_request_identity_v1(
        authenticated_command=command,
        deployment_config_root="a" * 64,
        expected_sequence=43,
        authority_epoch_index=3,
    )
    return derive_nonce_nullifier_v1(request_identity=identity, current_nonce=7)


def _candidate(
    *,
    sequence: int = 1,
    commit_id: str,
    nullifier: E02NullifierV1,
    payload_root: str,
) -> E03CommitIdentityV1:
    return derive_e03_commit_identity_v1(
        sequence=sequence,
        commit_id=commit_id,
        nullifier=nullifier,
        effects=(
            E03EffectSpecV1(
                ordinal=0,
                destination="research-destination",
                payload_root=payload_root,
                writer_profile_root="d" * 64,
                adapter_profile_root="e" * 64,
            ),
        ),
    )


def _expect_collision(result: object) -> None:
    if type(result) is not E03RejectV1:
        raise AssertionError(f"expected E03 rejection, got {result!r}")
    if cast(E03RejectV1, result).code is not E03DatabaseCodeV1.CONSTRAINT_COLLISION:
        raise AssertionError(f"wrong E03 collision code: {result!r}")


def _migration_hash() -> str:
    digest = hashlib.sha256()
    with (_ROOT / "config/deploy/fcis_m6_e03_uniqueness_v1.sql").open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _concurrent_duplicate_check(candidate: E03CommitIdentityV1) -> None:
    database = _ROOT / "docs/research/m6_tasks/.e03-check.sqlite3"
    if database.exists():
        database.unlink()
    barrier = threading.Barrier(2)
    results: list[object] = []
    failures: list[BaseException] = []

    def worker() -> None:
        connection = create_e03_connection(database)
        try:
            barrier.wait(timeout=5)
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
    try:
        if failures or len(results) != 2:
            raise AssertionError(f"concurrency workers failed: {failures!r}, {results!r}")
        if sum(type(result) is E03CommitV1 for result in results) != 1:
            raise AssertionError(f"concurrency did not produce one winner: {results!r}")
        rejected = [result for result in results if type(result) is E03RejectV1]
        if len(rejected) != 1:
            raise AssertionError(f"concurrency rejection count is wrong: {results!r}")
        _expect_collision(rejected[0])
        connection = create_e03_connection(database)
        if read_e03_counts(connection) != (1, 1, len(candidate.effects)):
            raise AssertionError("concurrent duplicate left the wrong durable rows")
        connection.close()
    finally:
        if database.exists():
            database.unlink()


def _loose_schema_check() -> None:
    database = _ROOT / "docs/research/m6_tasks/.e03-loose-check.sqlite3"
    if database.exists():
        database.unlink()
    connection = sqlite3.connect(database)
    try:
        connection.executescript(
            """
            CREATE TABLE e03_publication_commits (
                sequence INTEGER, commit_id TEXT, fingerprint TEXT,
                nullifier_root TEXT, request_identity_root TEXT
            );
            CREATE TABLE e03_publication_nullifiers (
                nullifier_root TEXT, commit_id TEXT, fingerprint TEXT
            );
            CREATE TABLE e03_publication_effects (
                effect_id TEXT, commit_id TEXT, ordinal INTEGER,
                destination TEXT, payload_root TEXT,
                writer_profile_root TEXT, adapter_profile_root TEXT
            );
            """
        )
    finally:
        connection.close()
    try:
        try:
            unexpected = create_e03_connection(database)
        except E03Error:
            pass
        else:
            unexpected.close()
            raise AssertionError("E03 accepted a pre-existing loose schema")
    finally:
        if database.exists():
            database.unlink()


def _check_vector_and_replay() -> tuple[str, E03CommitIdentityV1]:
    baseline = build_payload()
    vector_path = _ROOT / DEFAULT_OUTPUT_PATH
    vector = json.loads(vector_path.read_text(encoding="utf-8"))
    if baseline != vector:
        raise AssertionError("E03 vector is not the independently regenerated payload")
    if baseline["migration_sql_sha256"] != _migration_hash():
        raise AssertionError("E03 migration hash is not source-bound")
    if baseline["migration_sql_sha256"] != E03_MIGRATION_SHA256_V1:
        raise AssertionError("E03 adapter migration pin differs from the vector")

    candidate = build_candidate()
    if not is_verified_e03_commit_identity_v1(candidate):
        raise AssertionError("E03 candidate lost verifier provenance")
    if candidate.to_wire() != baseline["candidate"]:
        raise AssertionError("E03 candidate does not match its vector")
    if hasattr(e03_core, "_E03_COMMIT_REGISTRY_V1") or hasattr(
        e03_core, "_E03_COMMIT_SNAPSHOTS_V1"
    ):
        raise AssertionError("E03 still depends on a process-local proof registry")
    replayed = derive_e03_commit_identity_v1(
        sequence=candidate.sequence,
        commit_id=candidate.commit_id,
        nullifier=candidate.nullifier,
        effects=candidate.effects,
    )
    if replayed is candidate or replayed.to_wire() != candidate.to_wire():
        raise AssertionError("E03 source replay did not reconstruct the exact identity")
    candidate_wire = baseline["candidate"]
    if type(candidate_wire) is not dict or type(candidate_wire.get("fingerprint")) is not str:
        raise AssertionError("E03 vector candidate fingerprint is malformed")
    return cast(str, candidate_wire["fingerprint"]), candidate


def _deny_nullifier_insert(
    action: int,
    argument_one: str | None,
    *_ignored: str | None,
) -> int:
    if action == sqlite3.SQLITE_INSERT and argument_one == "e03_publication_nullifiers":
        return sqlite3.SQLITE_DENY
    return sqlite3.SQLITE_OK


def _check_database_atomicity(candidate: E03CommitIdentityV1) -> None:
    connection = create_e03_connection()
    try:
        committed = persist_e03_commit(connection, candidate)
        if type(committed) is not E03CommitV1:
            raise AssertionError(f"valid E03 candidate was rejected: {committed!r}")
        if read_e03_counts(connection) != (1, 1, 1):
            raise AssertionError("complete E03 publication row set was not committed")
        _expect_collision(persist_e03_commit(connection, candidate))
        if read_e03_counts(connection) != (1, 1, 1):
            raise AssertionError("duplicate E03 commit changed durable row counts")

        same_nullifier = _candidate(
            sequence=2,
            commit_id="f" * 64,
            nullifier=candidate.nullifier,
            payload_root="c" * 64,
        )
        _expect_collision(persist_e03_commit(connection, same_nullifier))
        if read_e03_counts(connection) != (1, 1, 1):
            raise AssertionError("nullifier collision left a partial commit row")

        connection.set_authorizer(_deny_nullifier_insert)
        try:
            rollback_result = persist_e03_commit(
                connection,
                _candidate(
                    sequence=2,
                    commit_id="e" * 64,
                    nullifier=_second_nullifier(),
                    payload_root="f" * 64,
                ),
            )
        finally:
            connection.set_authorizer(None)
        if type(rollback_result) is not E03RejectV1:
            raise AssertionError("forced E03 abort was accepted")
        if cast(E03RejectV1, rollback_result).code is not E03DatabaseCodeV1.SQL_ROLLBACK:
            raise AssertionError("forced E03 abort did not report SQL rollback")
        if read_e03_counts(connection) != (1, 1, 1):
            raise AssertionError("forced E03 abort left partial rows")
    finally:
        connection.close()


def _check_construction_and_mutation(candidate: E03CommitIdentityV1) -> None:
    try:
        E03CommitIdentityV1(
            sequence=candidate.sequence,
            commit_id=candidate.commit_id,
            nullifier=candidate.nullifier,
            effects=candidate.effects,
            fingerprint=candidate.fingerprint,
        )
    except E03Error:
        pass
    else:
        raise AssertionError("caller-minted E03 identity crossed the boundary")

    object.__setattr__(candidate, "commit_id", "0" * 64)
    if is_verified_e03_commit_identity_v1(candidate):
        raise AssertionError("mutated E03 identity retained verifier provenance")
    nested_mutation = build_candidate()
    object.__setattr__(nested_mutation.effects[0], "payload_root", "0" * 64)
    if is_verified_e03_commit_identity_v1(nested_mutation):
        raise AssertionError("nested E03 mutation crossed the fingerprint seal")


def _check_connection_contract() -> None:
    foreign_keys_off = create_e03_connection()
    foreign_keys_off.execute("PRAGMA foreign_keys = OFF")
    foreign_key_result = persist_e03_commit(foreign_keys_off, build_candidate())
    if type(foreign_key_result) is not E03RejectV1 or foreign_key_result.path != (
        "connection",
        "foreign_keys",
    ):
        raise AssertionError("E03 accepted a connection without foreign-key authority")
    foreign_keys_off.close()

    schema_drift = create_e03_connection()
    schema_drift.execute(
        "CREATE TRIGGER hostile_e03_check AFTER INSERT ON e03_publication_commits "
        "BEGIN SELECT 1; END"
    )
    schema_result = persist_e03_commit(schema_drift, build_candidate())
    if type(schema_result) is not E03RejectV1 or schema_result.path != (
        "connection",
        "schema",
    ):
        raise AssertionError("E03 accepted a drifted SQLite schema")
    schema_drift.close()

    active = create_e03_connection()
    active.execute("CREATE TEMP TABLE caller_sentinel(value INTEGER NOT NULL)")
    active.execute("BEGIN")
    active.execute("INSERT INTO caller_sentinel(value) VALUES (7)")
    active_result = persist_e03_commit(active, build_candidate())
    if type(active_result) is not E03RejectV1 or active_result.path != (
        "connection",
        "active_transaction",
    ):
        raise AssertionError("E03 accepted a caller-owned active transaction")
    if not active.in_transaction or active.execute(
        "SELECT value FROM caller_sentinel"
    ).fetchone() != (7,):
        raise AssertionError("E03 rolled back caller-owned transaction state")
    active.rollback()
    active.close()


def run_checks() -> None:
    fingerprint, candidate = _check_vector_and_replay()
    _check_database_atomicity(candidate)
    _check_construction_and_mutation(candidate)
    _check_connection_contract()
    _loose_schema_check()
    _concurrent_duplicate_check(build_candidate())
    print("E03_UNIQUENESS_MATCH", fingerprint)


if __name__ == "__main__":
    run_checks()
