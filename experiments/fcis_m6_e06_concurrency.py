"""Independent-connection E06 concurrency harness for the E05 CAS port."""

from __future__ import annotations

import sqlite3
import tempfile
import threading
from dataclasses import dataclass
from pathlib import Path
from typing import Final, TypeAlias, cast

from experiments.fcis_m6_e04_retry_classifier import (
    POST_STATE_ROOT_V1,
    build_attempt,
    build_reopen_receipt,
    build_state,
)
from experiments.fcis_m6_e05_expected_root_cas import (
    create_connection,
    initialize_database,
    publish,
    read_state,
)
from src.core.fcis_m6_e03_unique_commit_port import (
    E03EffectSpecV1,
    _mint_e03_commit_identity_v1,
)
from src.core.fcis_m6_e04_retry_classifier import E04AttemptV1
from src.core.fcis_m6_e05_expected_root_cas import (
    E05CommitReceiptV1,
    E05PublicationRequestV1,
    E05RejectV1,
)
from tools.build_fcis_m6_e03_database_uniqueness import build_candidate

MAX_RACE_WORKERS_V1: Final = 2
E06ResultV1: TypeAlias = E05CommitReceiptV1 | E05RejectV1


class E06ConcurrencyError(ValueError):
    """Raised when a concurrency witness cannot be collected safely."""


@dataclass(frozen=True, slots=True)
class E06RaceObservationV1:
    """Stable summary of one two-actor linearization race."""

    name: str
    result_kinds: tuple[str, ...]
    reject_codes: tuple[str, ...]
    publication_count: int
    nullifier_count: int
    effect_count: int
    final_current_state_root: str
    final_authority_epoch_index: int

    def __post_init__(self) -> None:
        if type(self.name) is not str or not self.name:
            raise E06ConcurrencyError("race name must be a nonempty string")
        if self.result_kinds != tuple(sorted(self.result_kinds)):
            raise E06ConcurrencyError("race result kinds must be ordered")
        if self.reject_codes != tuple(sorted(self.reject_codes)):
            raise E06ConcurrencyError("race reject codes must be ordered")
        if len(self.result_kinds) != MAX_RACE_WORKERS_V1:
            raise E06ConcurrencyError("race must have exactly two actors")
        if any(type(value) is not str for value in self.result_kinds + self.reject_codes):
            raise E06ConcurrencyError("race labels must be strings")
        if any(
            type(value) is not int or value < 0
            for value in (self.publication_count, self.nullifier_count, self.effect_count)
        ):
            raise E06ConcurrencyError("row counts must be nonnegative integers")
        if (
            type(self.final_current_state_root) is not str
            or len(self.final_current_state_root) != 64
        ):
            raise E06ConcurrencyError("final state root is malformed")

    def to_wire(self) -> dict[str, object]:
        return {
            "name": self.name,
            "result_kinds": list(self.result_kinds),
            "reject_codes": list(self.reject_codes),
            "publication_count": self.publication_count,
            "nullifier_count": self.nullifier_count,
            "effect_count": self.effect_count,
            "final_current_state_root": self.final_current_state_root,
            "final_authority_epoch_index": self.final_authority_epoch_index,
        }


def _request_for_attempt(attempt: object) -> E05PublicationRequestV1:
    exact_attempt = cast("E04AttemptV1", attempt)
    pre_state = build_state()
    post_state = build_state(
        attempts=((exact_attempt, POST_STATE_ROOT_V1),),
        current_state_root=POST_STATE_ROOT_V1,
    )
    return E05PublicationRequestV1(
        attempt=exact_attempt,
        pre_state=pre_state,
        post_state=post_state,
        reopen_receipt=build_reopen_receipt(pre_state),
    )


def _same_nullifier_attempt() -> object:
    baseline = build_candidate()
    other_commit = _mint_e03_commit_identity_v1(
        sequence=baseline.sequence,
        commit_id="f" * 64,
        nullifier=baseline.nullifier,
        effects=(
            E03EffectSpecV1(
                ordinal=0,
                destination="other-command-destination",
                payload_root="e" * 64,
                writer_profile_root="2" * 64,
                adapter_profile_root="4" * 64,
            ),
        ),
    )
    return build_attempt(commit=other_commit)


def _same_id_different_fingerprint_attempt() -> object:
    baseline = build_candidate()
    other_commit = _mint_e03_commit_identity_v1(
        sequence=baseline.sequence,
        commit_id=baseline.commit_id,
        nullifier=baseline.nullifier,
        effects=(
            E03EffectSpecV1(
                ordinal=0,
                destination="changed-fingerprint-destination",
                payload_root="e" * 64,
                writer_profile_root="2" * 64,
                adapter_profile_root="4" * 64,
            ),
        ),
    )
    return build_attempt(commit=other_commit)


def _prepare_database(path: Path) -> None:
    connection = create_connection(path)
    try:
        initialize_database(connection, build_state())
    finally:
        connection.close()


def _result_kind(result: E06ResultV1) -> str:
    if type(result) is E05CommitReceiptV1:
        return "committed"
    if type(result) is E05RejectV1:
        return "rejected"
    raise E06ConcurrencyError("worker returned an unexpected result type")


def _reject_code(result: E06ResultV1) -> str:
    if type(result) is E05RejectV1:
        return str(result.code.value)
    return ""


def _two_publisher_race(
    path: Path,
    requests: tuple[E05PublicationRequestV1, E05PublicationRequestV1],
    name: str,
) -> E06RaceObservationV1:
    barrier = threading.Barrier(MAX_RACE_WORKERS_V1)
    results: list[E06ResultV1] = []
    failures: list[BaseException] = []
    lock = threading.Lock()

    def worker(request: E05PublicationRequestV1) -> None:
        connection: sqlite3.Connection | None = None
        try:
            connection = create_connection(path)
            barrier.wait(timeout=10)
            result = publish(connection, request)
            with lock:
                results.append(cast(E06ResultV1, result))
        except BaseException as exc:  # pragma: no cover - diagnostic guard
            with lock:
                failures.append(exc)
        finally:
            if connection is not None:
                connection.close()

    threads = tuple(threading.Thread(target=worker, args=(request,)) for request in requests)
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(timeout=20)
    if failures or len(results) != MAX_RACE_WORKERS_V1:
        raise E06ConcurrencyError(f"race workers failed: {failures!r}, {results!r}")

    connection = create_connection(path)
    try:
        state = read_state(connection)
    finally:
        connection.close()
    return E06RaceObservationV1(
        name=name,
        result_kinds=tuple(sorted(_result_kind(result) for result in results)),
        reject_codes=tuple(
            sorted(code for code in (_reject_code(result) for result in results) if code)
        ),
        publication_count=len(state.publications),
        nullifier_count=_count_rows(path, "e05_nullifiers"),
        effect_count=_count_rows(path, "e05_effects"),
        final_current_state_root=state.current_state_root,
        final_authority_epoch_index=state.authority_epoch_index,
    )


def _count_rows(path: Path, table: str) -> int:
    connection = create_connection(path)
    try:
        value = connection.execute(f"SELECT COUNT(*) FROM {table}").fetchone()
        if value is None:
            raise E06ConcurrencyError(f"row count missing for {table}")
        return int(value[0])
    finally:
        connection.close()


def _locked_head_change(
    path: Path,
    barrier: threading.Barrier,
    ready: threading.Event,
    *,
    authority_root: str,
    deployment_root: str,
) -> None:
    connection = create_connection(path)
    try:
        connection.execute("BEGIN IMMEDIATE")
        ready.set()
        barrier.wait(timeout=10)
        connection.execute(
            """
            UPDATE e05_head
            SET authority_epoch_index = authority_epoch_index + 1,
                authority_state_root = ?, deployment_config_root = ?
            WHERE singleton = 1
            """,
            (authority_root, deployment_root),
        )
        connection.commit()
    finally:
        connection.close()


def _authority_race(path: Path, *, name: str, deployment_root: str) -> E06RaceObservationV1:
    request = _request_for_attempt(build_attempt())
    barrier = threading.Barrier(MAX_RACE_WORKERS_V1)
    ready = threading.Event()
    failures: list[BaseException] = []

    def migration_worker() -> None:
        try:
            _locked_head_change(
                path,
                barrier,
                ready,
                authority_root="f" * 64,
                deployment_root=deployment_root,
            )
        except BaseException as exc:  # pragma: no cover - diagnostic guard
            failures.append(exc)

    migration = threading.Thread(target=migration_worker)
    migration.start()
    if not ready.wait(timeout=10):
        raise E06ConcurrencyError("authority worker did not acquire its transaction")
    connection = create_connection(path)
    try:
        barrier.wait(timeout=10)
        result = publish(connection, request)
    finally:
        connection.close()
    migration.join(timeout=20)
    if failures:
        raise E06ConcurrencyError(f"authority worker failed: {failures!r}")
    if type(result) is not E05RejectV1:
        raise E06ConcurrencyError(f"authority race unexpectedly committed: {result!r}")
    connection = create_connection(path)
    try:
        state = read_state(connection)
    finally:
        connection.close()
    return E06RaceObservationV1(
        name=name,
        result_kinds=tuple(sorted(("head_changed", "rejected"))),
        reject_codes=(result.code.value,),
        publication_count=len(state.publications),
        nullifier_count=_count_rows(path, "e05_nullifiers"),
        effect_count=_count_rows(path, "e05_effects"),
        final_current_state_root=state.current_state_root,
        final_authority_epoch_index=state.authority_epoch_index,
    )


def run_campaign() -> tuple[E06RaceObservationV1, ...]:
    """Run all five required E06 race families in fresh databases."""

    with tempfile.TemporaryDirectory(prefix="fcis-m6-e06-") as directory:
        root = Path(directory)
        cases: list[E06RaceObservationV1] = []
        for name, attempts in (
            ("same_command_retry", (build_attempt(), build_attempt())),
            ("same_sender_nonce_different_command", (build_attempt(), _same_nullifier_attempt())),
            (
                "same_commit_id_different_fingerprint",
                (build_attempt(), _same_id_different_fingerprint_attempt()),
            ),
        ):
            path = root / f"{name}.sqlite3"
            _prepare_database(path)
            cases.append(
                _two_publisher_race(
                    path,
                    (_request_for_attempt(attempts[0]), _request_for_attempt(attempts[1])),
                    name,
                )
            )

        for name, deployment_root in (
            ("commit_racing_quiescence", "e" * 64),
            ("commit_racing_authority_switch", "d" * 64),
        ):
            path = root / f"{name}.sqlite3"
            _prepare_database(path)
            cases.append(_authority_race(path, name=name, deployment_root=deployment_root))
        return tuple(cases)


__all__ = (
    "E06ConcurrencyError",
    "E06RaceObservationV1",
    "run_campaign",
)
