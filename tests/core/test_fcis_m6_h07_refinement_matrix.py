"""Focused H07 abstract-to-SQL refinement matrix tests."""

from __future__ import annotations

from pathlib import Path

from tools.check_fcis_m6_h07_refinement_matrix import check_matrix


def test_h07_refinement_matrix_is_complete() -> None:
    path = (
        Path(__file__).resolve().parents[2]
        / "docs/research/m6_tasks/TASK_H07_REFINEMENT_MATRIX_V1.json"
    )
    check_matrix(path)
