"""Research-only process-restart harness for the H03 SQLite fault points.

Each case uses a file-backed SQLite database, launches a fresh Python worker,
injects one ordinary publication fault, lets the worker exit without an
explicit rollback, and reopens the file from a new connection. The comparator
checks the complete ``SQLiteStateV1`` against independently prepared PRE and
POST states. This remains a harness refinement and does not establish
filesystem durability or production datastore behavior.
"""

from __future__ import annotations

import os
import sqlite3
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Final

from experiments.fcis_m6_d08_combined_anf_check import build_instance
from experiments.fcis_m6_h02_sqlite_publication import (
    ANFPublicationWitnessV1,
    H02CommitV1,
    H02Error,
    H03CrashPointV1,
    H03FaultHookV1,
    H03InjectedCrash,
    SQLitePublicationRequestV1,
    SQLiteStateV1,
    create_connection,
    initialize_database,
    publish_atom,
    read_state,
)
from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_d08_combined_anf import (
    D08CombinedANFAcceptV1,
    D08CombinedANFInstanceV1,
    verify_combined_anf_v1,
)

_ROOT: Final[Path] = Path(__file__).resolve().parents[1]
_CRASH_EXIT: Final[int] = 73
_WORKER_ERROR_EXIT: Final[int] = 74


class H04RecoveryClassV1(Enum):
    PRE = "pre"
    POST = "post"
    REJECTED = "rejected"


@dataclass(frozen=True, slots=True)
class H04RecoveryResultV1:
    crash_point: H03CrashPointV1
    worker_exit_code: int
    classification: H04RecoveryClassV1
    pre_snapshot_root: str
    post_snapshot_root: str
    observed_snapshot_root: str | None
    error: str | None = None

    def __post_init__(self) -> None:
        if type(self.crash_point) is not H03CrashPointV1:
            raise H02Error("H04 crash point has the wrong exact type")
        if type(self.worker_exit_code) is not int:
            raise H02Error("H04 worker exit code has the wrong exact type")
        if type(self.classification) is not H04RecoveryClassV1:
            raise H02Error("H04 classification has the wrong exact type")
        for name in ("pre_snapshot_root", "post_snapshot_root"):
            value = object.__getattribute__(self, name)
            if (
                type(value) is not str
                or len(value) != 64
                or any(character not in "0123456789abcdef" for character in value)
            ):
                raise H02Error(f"{name} must be a lowercase 64-character digest")
        if self.observed_snapshot_root is not None:
            if (
                type(self.observed_snapshot_root) is not str
                or len(self.observed_snapshot_root) != 64
                or any(
                    character not in "0123456789abcdef" for character in self.observed_snapshot_root
                )
            ):
                raise H02Error("observed_snapshot_root must be a digest or None")
        if self.error is not None and type(self.error) is not str:
            raise H02Error("H04 error must be a string or None")


def _build_fixture() -> tuple[D08CombinedANFInstanceV1, SQLitePublicationRequestV1]:
    instance = build_instance()
    verified = verify_combined_anf_v1(instance)
    if type(verified) is not D08CombinedANFAcceptV1:
        raise H02Error(f"D08 fixture was not accepted: {verified!r}")
    witness = ANFPublicationWitnessV1(instance, verified)
    connection = create_connection()
    try:
        initialize_database(connection, instance.pre_snapshot)
        pre_state = read_state(connection)
    finally:
        connection.close()
    request = SQLitePublicationRequestV1(
        atom=instance.publication_atom,
        anf_witness=witness,
        expected_snapshot_root=pre_state.snapshot.snapshot_root,
        expected_publication_root=pre_state.publication_root,
        expected_state_root=pre_state.snapshot.current_state_root,
        expected_authority_epoch=pre_state.snapshot.authority_epochs[-1].epoch_index,
        expected_authority_root=pre_state.snapshot.authority_epochs[-1].root,
    )
    return instance, request


def _seed_file(path: Path, snapshot: dra.DurableSnapshotV1) -> None:
    connection = create_connection(path)
    try:
        initialize_database(connection, snapshot)
    finally:
        connection.close()


def _run_worker(path: Path, point: H03CrashPointV1) -> int:
    connection = create_connection(path)
    try:
        _, request = _build_fixture()
        publish_atom(connection, request, H03FaultHookV1(point))
    except H03InjectedCrash:
        return _CRASH_EXIT
    except Exception as exc:  # pragma: no cover - surfaced as a worker code
        print(f"H04 worker failure: {type(exc).__name__}: {exc}", file=sys.stderr)
        return _WORKER_ERROR_EXIT
    finally:
        connection.close()
    return _WORKER_ERROR_EXIT


def _classify(
    *,
    point: H03CrashPointV1,
    worker_exit_code: int,
    pre_state: SQLiteStateV1,
    post_state: SQLiteStateV1,
    observed: SQLiteStateV1 | None,
    error: str | None,
) -> H04RecoveryResultV1:
    observed_root = None if observed is None else observed.snapshot.snapshot_root
    if worker_exit_code != _CRASH_EXIT:
        classification = H04RecoveryClassV1.REJECTED
    elif observed is None:
        classification = H04RecoveryClassV1.REJECTED
    elif observed == pre_state:
        classification = H04RecoveryClassV1.PRE
    elif observed == post_state:
        classification = H04RecoveryClassV1.POST
    else:
        classification = H04RecoveryClassV1.REJECTED
        error = error or "reopen produced a third durable layout"
    return H04RecoveryResultV1(
        crash_point=point,
        worker_exit_code=worker_exit_code,
        classification=classification,
        pre_snapshot_root=pre_state.snapshot.snapshot_root,
        post_snapshot_root=post_state.snapshot.snapshot_root,
        observed_snapshot_root=observed_root,
        error=error,
    )


def run_recovery_case(point: H03CrashPointV1) -> H04RecoveryResultV1:
    """Run one real child-process fault and classify its fresh reopen."""

    if type(point) is not H03CrashPointV1:
        raise H02Error("H04 crash point has the wrong exact type")
    instance, request = _build_fixture()
    with tempfile.TemporaryDirectory(prefix="fcis-m6-h04-") as directory:
        root = Path(directory)
        seed_path = root / "seed.sqlite"
        post_path = root / "post.sqlite"
        _seed_file(seed_path, instance.pre_snapshot)
        _seed_file(post_path, instance.pre_snapshot)

        pre_connection = create_connection(seed_path)
        try:
            pre_state = read_state(pre_connection)
        finally:
            pre_connection.close()

        post_connection = create_connection(post_path)
        try:
            committed = publish_atom(post_connection, request)
            if type(committed) is not H02CommitV1:
                raise H02Error(f"H04 POST fixture was not committed: {committed!r}")
            post_state = read_state(post_connection)
        finally:
            post_connection.close()

        environment = os.environ.copy()
        current_python_path = environment.get("PYTHONPATH", "")
        environment["PYTHONPATH"] = str(_ROOT) + os.pathsep + current_python_path
        completed = subprocess.run(
            (
                sys.executable,
                "-m",
                "experiments.fcis_m6_h04_crash_recovery",
                "--worker",
                str(seed_path),
                point.value,
            ),
            cwd=_ROOT,
            env=environment,
            capture_output=True,
            check=False,
            timeout=60,
        )

        observed: SQLiteStateV1 | None = None
        error: str | None = None
        reopen_connection = create_connection(seed_path)
        try:
            try:
                observed = read_state(reopen_connection)
            except (H02Error, dra.DurableRetractionError, sqlite3.Error) as exc:
                error = f"{type(exc).__name__}: {exc}"
        finally:
            reopen_connection.close()
        if completed.stderr:
            error = completed.stderr.decode("utf-8", errors="replace").strip() or error
        return _classify(
            point=point,
            worker_exit_code=completed.returncode,
            pre_state=pre_state,
            post_state=post_state,
            observed=observed,
            error=error,
        )


def main(argv: list[str]) -> int:
    if len(argv) != 4 or argv[1] != "--worker":
        print(
            "usage: python -m experiments.fcis_m6_h04_crash_recovery "
            "--worker <sqlite-path> <crash-point>",
            file=sys.stderr,
        )
        return 2
    path = Path(argv[2])
    try:
        point = H03CrashPointV1(argv[3])
    except ValueError:
        return _WORKER_ERROR_EXIT
    return _run_worker(path, point)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))


__all__ = (
    "H04RecoveryClassV1",
    "H04RecoveryResultV1",
    "main",
    "run_recovery_case",
)
