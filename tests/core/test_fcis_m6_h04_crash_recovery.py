"""Focused H04 fresh-process PRE/POST recovery tests."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Final, cast

import pytest

from experiments.fcis_m6_h02_sqlite_publication import (
    H03_CRASH_MANIFEST_V1,
    H03CrashPointV1,
)
from experiments.fcis_m6_h04_crash_recovery import (
    H04RecoveryClassV1,
    run_recovery_case,
)

_AUTHORITY_POINTS: Final[frozenset[H03CrashPointV1]] = frozenset(
    {
        H03CrashPointV1.BEFORE_AUTHORITY_EPOCH_INSERT,
        H03CrashPointV1.AFTER_AUTHORITY_EPOCH_INSERT,
        H03CrashPointV1.BEFORE_AUTHORITY_WRITER_INSERT,
        H03CrashPointV1.AFTER_AUTHORITY_WRITER_INSERT,
    }
)
_RECOVERY_POINTS: Final[tuple[H03CrashPointV1, ...]] = tuple(
    point for point in H03_CRASH_MANIFEST_V1 if point not in _AUTHORITY_POINTS
)
_MATRIX_PATH: Final[Path] = (
    Path(__file__).resolve().parents[2] / "docs/research/m6_tasks/TASK_H04_RECOVERY_MATRIX_V1.json"
)


def test_recovery_matrix_matches_the_closed_ordinary_points() -> None:
    payload = cast(dict[str, object], json.loads(_MATRIX_PATH.read_text(encoding="utf-8")))
    cases = cast(list[dict[str, object]], payload["cases"])
    assert tuple(case["crash_point"] for case in cases) == tuple(
        point.value for point in _RECOVERY_POINTS
    )
    expected = tuple(
        "post" if point is H03CrashPointV1.AFTER_COMMIT_BEFORE_RESPONSE else "pre"
        for point in _RECOVERY_POINTS
    )
    assert tuple(case["expected"] for case in cases) == expected


@pytest.mark.parametrize("point", _RECOVERY_POINTS)  # type: ignore[untyped-decorator]
def test_fresh_process_reopen_is_exact_pre_or_post(point: H03CrashPointV1) -> None:
    result = run_recovery_case(point)

    assert result.worker_exit_code == 73
    expected = (
        H04RecoveryClassV1.POST
        if point is H03CrashPointV1.AFTER_COMMIT_BEFORE_RESPONSE
        else H04RecoveryClassV1.PRE
    )
    assert result.classification is expected
    assert result.observed_snapshot_root == (
        result.post_snapshot_root
        if expected is H04RecoveryClassV1.POST
        else result.pre_snapshot_root
    )
    assert result.error is None
