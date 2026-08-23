from __future__ import annotations

import json
import multiprocessing
from pathlib import Path

import pytest

from src.integration.autotrader_execution_journal import (
    execution_journal_ids,
    mark_execution_sent,
    reserve_execution_id,
)

_SUBMISSION_ROOT = "0x" + "42" * 32


def _pending_row() -> dict[str, object]:
    return {
        "schema": "zenodex/autotrader-execution-journal/v3",
        "execution_id": "atlas-execution",
        "surface": "autotrader_live_execute_once",
        "state": "PENDING",
        "submission_root": _SUBMISSION_ROOT,
    }


def _reserve_same_execution_id(path: str, start, outcomes) -> None:
    start.wait()
    try:
        reserve_execution_id(
            path=path,
            execution_keys=set(),
            execution_id="cross-process-execution",
            surface="autotrader_live_execute_once",
            submission_root=_SUBMISSION_ROOT,
        )
    except ValueError as exc:
        outcomes.put(str(exc))
    else:
        outcomes.put("reserved")


def test_execution_journal_atomic_reservation_allows_one_cross_process_winner(
    tmp_path: Path,
) -> None:
    context = multiprocessing.get_context("fork")
    start = context.Event()
    outcomes = context.Queue()
    journal = tmp_path / "execution-journal.jsonl"
    workers = [
        context.Process(
            target=_reserve_same_execution_id,
            args=(str(journal), start, outcomes),
        )
        for _index in range(4)
    ]

    for worker in workers:
        worker.start()
    start.set()
    observed = [outcomes.get(timeout=10) for _worker in workers]
    for worker in workers:
        worker.join(timeout=10)

    assert all(worker.exitcode == 0 for worker in workers)
    assert observed.count("reserved") == 1
    assert observed.count("execution_replay") == 3
    assert len(journal.read_text(encoding="utf-8").splitlines()) == 1


def test_execution_journal_binds_sent_transition_to_reserved_submission_root(
    tmp_path: Path,
) -> None:
    # Arrange: reserve one exact signed submission before the external send.
    journal = tmp_path / "execution-journal.jsonl"
    reserve_execution_id(
        path=str(journal),
        execution_keys=set(),
        execution_id="root-bound-execution",
        surface="autotrader_live_execute_once",
        submission_root=_SUBMISSION_ROOT,
    )

    # Act: attempt to mark a different signed submission as the accepted one.
    with pytest.raises(ValueError, match="execution_journal_submission_root_mismatch"):
        mark_execution_sent(
            path=str(journal),
            execution_id="root-bound-execution",
            surface="autotrader_live_execute_once",
            submission_root="0x" + "43" * 32,
        )
    mark_execution_sent(
        path=str(journal),
        execution_id="root-bound-execution",
        surface="autotrader_live_execute_once",
        submission_root=_SUBMISSION_ROOT,
    )
    with pytest.raises(ValueError, match="execution_journal_submission_root_mismatch"):
        mark_execution_sent(
            path=str(journal),
            execution_id="root-bound-execution",
            surface="autotrader_live_execute_once",
            submission_root="0x" + "43" * 32,
        )

    # Assert: both durable rows carry the same exact submission root.
    rows = [json.loads(line) for line in journal.read_text(encoding="utf-8").splitlines()]
    assert rows == [
        {
            "schema": "zenodex/autotrader-execution-journal/v3",
            "execution_id": "root-bound-execution",
            "surface": "autotrader_live_execute_once",
            "state": "PENDING",
            "submission_root": _SUBMISSION_ROOT,
        },
        {
            "schema": "zenodex/autotrader-execution-journal/v3",
            "execution_id": "root-bound-execution",
            "surface": "autotrader_live_execute_once",
            "state": "SENT",
            "submission_root": _SUBMISSION_ROOT,
        },
    ]


def test_execution_journal_rejects_duplicate_json_fields(tmp_path: Path) -> None:
    # Arrange: a forged row presents two meanings for the authoritative root.
    journal = tmp_path / "execution-journal.jsonl"
    journal.write_text(
        "{"
        '"schema":"zenodex/autotrader-execution-journal/v3",'
        '"execution_id":"duplicate-field",'
        '"surface":"autotrader_live_execute_once",'
        '"state":"PENDING",'
        f'"submission_root":"{_SUBMISSION_ROOT}",'
        f'"submission_root":"{"0x" + "43" * 32}"'
        "}\n",
        encoding="utf-8",
    )

    # Act / Assert: no JSON parser last-key rule can choose the journal meaning.
    with pytest.raises(ValueError, match="duplicate JSON field"):
        execution_journal_ids(str(journal))


@pytest.mark.parametrize(
    ("mutation", "row", "expected"),
    [
        ("valid_v3", _pending_row(), "ok"),
        (
            "unknown_schema",
            {**_pending_row(), "schema": "zenodex/autotrader-execution-journal/v999"},
            "execution journal row has unsupported schema",
        ),
        (
            "extra_field",
            {**_pending_row(), "extra": 1},
            "execution journal row has unexpected fields",
        ),
        (
            "sent_without_pending",
            {**_pending_row(), "state": "SENT"},
            "execution journal execution must start PENDING",
        ),
        (
            "uppercase_root",
            {**_pending_row(), "submission_root": "0x" + "AB" * 32},
            "execution journal submission_root must be a canonical root",
        ),
        (
            "short_root",
            {**_pending_row(), "submission_root": "0x" + "42" * 31},
            "execution journal submission_root must be a canonical root",
        ),
        (
            "boolean_state",
            {**_pending_row(), "state": True},
            "execution journal row has invalid state",
        ),
        (
            "blank_execution_id",
            {**_pending_row(), "execution_id": ""},
            "execution journal row missing execution_id",
        ),
        (
            "noncanonical_execution_id",
            {**_pending_row(), "execution_id": " atlas-execution"},
            "execution journal execution_id must be canonical",
        ),
        (
            "execution_id_with_internal_whitespace",
            {**_pending_row(), "execution_id": "atlas execution"},
            "execution journal execution_id must not contain whitespace",
        ),
        (
            "execution_id_too_long",
            {**_pending_row(), "execution_id": "x" * 129},
            "execution journal execution_id too long",
        ),
        (
            "boolean_surface",
            {**_pending_row(), "surface": True},
            "execution journal row missing surface",
        ),
        (
            "unknown_surface",
            {**_pending_row(), "surface": "autotrader_live_unknown"},
            "execution journal row has unsupported surface",
        ),
        (
            "valid_v2_pending",
            {
                "schema": "zenodex/autotrader-execution-journal/v2",
                "execution_id": "legacy-pending",
                "surface": "autotrader_live_execute_once",
                "state": "PENDING",
            },
            "ok",
        ),
        (
            "v2_sent_without_pending",
            {
                "schema": "zenodex/autotrader-execution-journal/v2",
                "execution_id": "legacy-invalid",
                "surface": "autotrader_live_execute_once",
                "state": "SENT",
            },
            "execution journal execution must start PENDING",
        ),
        (
            "valid_v1_consumed",
            {
                "schema": "zenodex/autotrader-execution-journal/v1",
                "execution_id": "legacy-consumed",
                "surface": "autotrader_live_execute_once",
                "consumed_at_unix_s": 1,
            },
            "ok",
        ),
    ],
)
def test_execution_journal_boundary_atlas(
    tmp_path: Path,
    mutation: str,
    row: dict[str, object],
    expected: str,
) -> None:
    # Arrange: preserve the journal row shape while flipping one boundary.
    journal = tmp_path / f"{mutation}.jsonl"
    journal.write_text(json.dumps(row, sort_keys=True) + "\n", encoding="utf-8")

    # Act: capture the exact deterministic outcome label.
    try:
        execution_journal_ids(str(journal))
    except ValueError as exc:
        outcome = str(exc)
    else:
        outcome = "ok"

    # Assert: each mutation remains pinned to its intended accept/reject branch.
    assert outcome == expected
