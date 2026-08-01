"""Focused H03 deterministic logical crash-point tests."""

from __future__ import annotations

import json
import sqlite3
from dataclasses import replace
from functools import lru_cache
from pathlib import Path
from typing import Final, cast

import pytest

from experiments.fcis_m6_d08_combined_anf_check import build_instance
from experiments.fcis_m6_h02_sqlite_publication import (
    H03_CRASH_MANIFEST_V1,
    ANFPublicationWitnessV1,
    H02CodeV1,
    H02CommitV1,
    H02RejectV1,
    H03CrashPointV1,
    H03FaultHookV1,
    H03InjectedCrash,
    SQLitePublicationRequestV1,
    _insert_authority,
    create_connection,
    create_database,
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
_PUBLICATION_POINTS: Final[tuple[H03CrashPointV1, ...]] = tuple(
    point for point in H03_CRASH_MANIFEST_V1 if point not in _AUTHORITY_POINTS
)
_MANIFEST_PATH: Final[Path] = (
    Path(__file__).resolve().parents[2] / "docs/research/m6_tasks/TASK_H03_CRASH_MANIFEST_V1.json"
)


@lru_cache(maxsize=1)
def _instance() -> D08CombinedANFInstanceV1:
    return build_instance()


@lru_cache(maxsize=1)
def _request_template() -> SQLitePublicationRequestV1:
    instance = _instance()
    verified = verify_combined_anf_v1(instance)
    if type(verified) is not D08CombinedANFAcceptV1:
        raise AssertionError(f"D08 fixture was not accepted: {verified!r}")
    witness = ANFPublicationWitnessV1(instance, verified)
    connection = create_database(instance.pre_snapshot)
    pre_state = read_state(connection)
    return SQLitePublicationRequestV1(
        atom=instance.publication_atom,
        anf_witness=witness,
        expected_snapshot_root=pre_state.snapshot.snapshot_root,
        expected_publication_root=pre_state.publication_root,
        expected_state_root=pre_state.snapshot.current_state_root,
        expected_authority_epoch=pre_state.snapshot.authority_epochs[-1].epoch_index,
        expected_authority_root=pre_state.snapshot.authority_epochs[-1].root,
    )


def _prepare() -> tuple[
    sqlite3.Connection,
    dra.DurableSnapshotV1,
    SQLitePublicationRequestV1,
]:
    instance = _instance()
    template = _request_template()
    connection = create_database(instance.pre_snapshot)
    return connection, instance.pre_snapshot, template


def test_crash_manifest_is_exhaustive_and_ordered() -> None:
    assert H03_CRASH_MANIFEST_V1 == tuple(H03CrashPointV1)
    assert len(H03_CRASH_MANIFEST_V1) == 20
    assert len(_PUBLICATION_POINTS) == 16
    payload = cast(dict[str, object], json.loads(_MANIFEST_PATH.read_text(encoding="utf-8")))
    points = cast(list[dict[str, object]], payload["points"])
    assert tuple(point["value"] for point in points) == tuple(
        point.value for point in H03_CRASH_MANIFEST_V1
    )


@pytest.mark.parametrize("point", _PUBLICATION_POINTS)  # type: ignore[untyped-decorator]
def test_each_publication_crash_point_is_reachable_and_repeatable(
    point: H03CrashPointV1,
) -> None:
    observed: list[H03CrashPointV1] = []
    for _ in range(2):
        connection, pre_snapshot, request = _prepare()
        with pytest.raises(H03InjectedCrash) as caught:
            publish_atom(connection, request, H03FaultHookV1(point))
        observed.append(caught.value.point)

        if connection.in_transaction:
            connection.rollback()
        if point is H03CrashPointV1.AFTER_COMMIT_BEFORE_RESPONSE:
            row = connection.execute(
                "SELECT current_state_root FROM snapshot_meta WHERE singleton = 1"
            ).fetchone()
            assert row == (request.anf_witness.instance.post_snapshot.current_state_root,)
        else:
            row = connection.execute(
                "SELECT current_state_root FROM snapshot_meta WHERE singleton = 1"
            ).fetchone()
            assert row == (pre_snapshot.current_state_root,)

    assert observed == [point, point]


@pytest.mark.parametrize("point", tuple(_AUTHORITY_POINTS))  # type: ignore[untyped-decorator]
def test_each_authority_insert_crash_point_is_reachable_and_repeatable(
    point: H03CrashPointV1,
) -> None:
    instance = _instance()
    previous = instance.pre_snapshot.authority_epochs[-1]
    next_authority = dra.advance_authority_state(
        previous,
        dra.MigrationPhaseV1.SHADOW_REPLAY,
        cast(str, dra.tagged_digest("h03-fault-transport")),
    )
    observed: list[H03CrashPointV1] = []

    for _ in range(2):
        connection = create_connection()
        connection.execute("BEGIN")
        with pytest.raises(H03InjectedCrash) as caught:
            _insert_authority(connection, next_authority, H03FaultHookV1(point))
        observed.append(caught.value.point)
        connection.rollback()
        assert connection.execute("SELECT COUNT(*) FROM authority_epochs").fetchone() == (0,)
        assert connection.execute("SELECT COUNT(*) FROM authority_allowed_writers").fetchone() == (
            0,
        )

    assert observed == [point, point]


def test_fault_hook_type_mismatch_rejects_before_begin() -> None:
    connection, _, request = _prepare()

    result = publish_atom(connection, request, object())

    assert type(result) is H02RejectV1
    assert result.code is H02CodeV1.INVALID_REQUEST
    assert not connection.in_transaction


def test_fault_hook_does_not_change_a_successful_publication() -> None:
    connection, _, request = _prepare()

    result = publish_atom(connection, replace(request), H03FaultHookV1())

    assert type(result) is H02CommitV1
    assert not connection.in_transaction
