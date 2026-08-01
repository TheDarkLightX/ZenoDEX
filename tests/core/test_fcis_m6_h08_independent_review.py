"""Independent H08 attacks against the frozen H02/H03 research adapter."""

from __future__ import annotations

import sqlite3
from pathlib import Path
from typing import Final, cast

import pytest

from experiments.fcis_m6_d08_combined_anf_check import build_instance
from experiments.fcis_m6_h02_sqlite_publication import (
    ANFPublicationWitnessV1,
    H02CodeV1,
    H02CommitV1,
    H02Error,
    H02RejectV1,
    H02StorageError,
    H03CrashPointV1,
    H03FaultHookV1,
    H03InjectedCrash,
    SQLitePublicationRequestV1,
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

_AUTHORITY_POINTS: Final[frozenset[H03CrashPointV1]] = frozenset(
    {
        H03CrashPointV1.BEFORE_AUTHORITY_EPOCH_INSERT,
        H03CrashPointV1.AFTER_AUTHORITY_EPOCH_INSERT,
        H03CrashPointV1.BEFORE_AUTHORITY_WRITER_INSERT,
        H03CrashPointV1.AFTER_AUTHORITY_WRITER_INSERT,
    }
)
_ORDINARY_POINTS: Final[tuple[H03CrashPointV1, ...]] = tuple(
    point for point in H03CrashPointV1 if point not in _AUTHORITY_POINTS
)


def _fixture() -> tuple[D08CombinedANFInstanceV1, ANFPublicationWitnessV1]:
    instance = build_instance()
    verified = verify_combined_anf_v1(instance)
    if type(verified) is not D08CombinedANFAcceptV1:
        raise AssertionError(f"D08 fixture was not accepted: {verified!r}")
    return instance, ANFPublicationWitnessV1(instance, verified)


def _request(
    connection: sqlite3.Connection,
    instance: D08CombinedANFInstanceV1,
    witness: ANFPublicationWitnessV1,
) -> SQLitePublicationRequestV1:
    state = read_state(connection)
    authority = state.snapshot.authority_epochs[-1]
    return SQLitePublicationRequestV1(
        atom=instance.publication_atom,
        anf_witness=witness,
        expected_snapshot_root=state.snapshot.snapshot_root,
        expected_publication_root=state.publication_root,
        expected_state_root=state.snapshot.current_state_root,
        expected_authority_epoch=authority.epoch_index,
        expected_authority_root=authority.root,
    )


def _seed(
    path: Path,
) -> tuple[sqlite3.Connection, D08CombinedANFInstanceV1, ANFPublicationWitnessV1]:
    instance, witness = _fixture()
    connection = create_connection(path)
    initialize_database(connection, instance.pre_snapshot)
    return connection, instance, witness


def test_h08_stale_cas_is_rejected_across_two_connections(tmp_path: Path) -> None:
    path = tmp_path / "stale-cas.sqlite"
    first, instance, witness = _seed(path)
    second = create_connection(path)
    try:
        first_request = _request(first, instance, witness)
        second_request = _request(second, instance, witness)
        first_result = publish_atom(first, first_request)
        assert type(first_result) is H02CommitV1
        before_retry = read_state(second)

        retry = publish_atom(second, second_request)

        assert type(retry) is H02RejectV1
        assert cast(H02RejectV1, retry).code is H02CodeV1.STALE_SNAPSHOT_CAS
        assert read_state(second) == before_retry
    finally:
        first.close()
        second.close()


@pytest.mark.parametrize("point", _ORDINARY_POINTS)  # type: ignore[untyped-decorator]
def test_h08_crash_points_reopen_as_exact_pre_or_post(
    tmp_path: Path,
    point: H03CrashPointV1,
) -> None:
    seed_path = tmp_path / f"seed-{point.value}.sqlite"
    post_path = tmp_path / f"post-{point.value}.sqlite"
    seed, instance, witness = _seed(seed_path)
    post, _, post_witness = _seed(post_path)
    pre_state = read_state(seed)
    post_result = publish_atom(post, _request(post, instance, post_witness))
    assert type(post_result) is H02CommitV1
    expected_post = read_state(post)
    post.close()

    try:
        with pytest.raises(H03InjectedCrash):
            publish_atom(seed, _request(seed, instance, witness), H03FaultHookV1(point))
    finally:
        seed.close()

    reopened = create_connection(seed_path)
    try:
        expected = (
            expected_post if point is H03CrashPointV1.AFTER_COMMIT_BEFORE_RESPONSE else pre_state
        )
        assert read_state(reopened) == expected
    finally:
        reopened.close()


def test_h08_missing_evidence_row_is_rejected(tmp_path: Path) -> None:
    connection, instance, witness = _seed(tmp_path / "missing-evidence.sqlite")
    try:
        result = publish_atom(connection, _request(connection, instance, witness))
        assert type(result) is H02CommitV1
        connection.execute("PRAGMA foreign_keys = OFF")
        connection.execute(
            "DELETE FROM publication_evidence WHERE commit_id = ? AND kind = ?",
            (instance.publication_atom.commit_id, "command"),
        )
        connection.execute("PRAGMA foreign_keys = ON")
        with pytest.raises(H02StorageError):
            read_state(connection)
    finally:
        connection.close()


def test_h08_surplus_orphan_evidence_row_is_rejected(tmp_path: Path) -> None:
    connection, instance, witness = _seed(tmp_path / "surplus-evidence.sqlite")
    try:
        result = publish_atom(connection, _request(connection, instance, witness))
        assert type(result) is H02CommitV1
        connection.execute("PRAGMA foreign_keys = OFF")
        connection.execute(
            """
            INSERT INTO publication_evidence(commit_id, kind, value_root)
            VALUES (?, 'command', ?)
            """,
            (dra.tagged_digest("h08-phantom-commit"), dra.tagged_digest("h08-phantom-value")),
        )
        connection.execute("PRAGMA foreign_keys = ON")
        with pytest.raises(H02StorageError):
            read_state(connection)
    finally:
        connection.close()


def test_h08_preexisting_non_snapshot_row_is_rejected_before_initialization(
    tmp_path: Path,
) -> None:
    instance, _ = _fixture()
    connection = create_connection(tmp_path / "contaminated-init.sqlite")
    authority = instance.pre_snapshot.authority_epochs[0]
    connection.execute(
        """
        INSERT INTO authority_epochs(
            epoch_index, phase, legacy_profile_root, target_profile_root,
            active_profile_root, transport_root, transition_root
        ) VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (
            1,
            authority.phase.value,
            authority.legacy_profile_root,
            authority.target_profile_root,
            authority.active_profile_root,
            authority.transport_root,
            authority.transition_root,
        ),
    )

    try:
        with pytest.raises(H02Error, match="authority_epochs"):
            initialize_database(connection, instance.pre_snapshot)
        assert connection.execute("SELECT COUNT(*) FROM snapshot_meta").fetchone() == (0,)
        assert connection.execute("SELECT COUNT(*) FROM authority_epochs").fetchone() == (1,)
        with pytest.raises(H02StorageError, match="metadata"):
            read_state(connection)
    finally:
        connection.close()
