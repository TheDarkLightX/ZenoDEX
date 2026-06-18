from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools.check_acceptance_tcb_coverage import BRANCH_THRESHOLDS, main


def _coverage_report(*, num_branches: object = 100, covered_branches: object = 100) -> dict[str, object]:
    return {
        "files": {
            path: {
                "summary": {
                    "num_branches": num_branches,
                    "covered_branches": covered_branches,
                }
            }
            for path in BRANCH_THRESHOLDS
        }
    }


def _write_report(tmp_path: Path, report: dict[str, object]) -> Path:
    report_path = tmp_path / "coverage.json"
    report_path.write_text(json.dumps(report, sort_keys=True), encoding="utf-8")
    return report_path


def test_acceptance_tcb_coverage_accepts_strict_counts(tmp_path: Path) -> None:
    report_path = _write_report(tmp_path, _coverage_report())

    assert main(["check_acceptance_tcb_coverage.py", str(report_path)]) == 0


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("num_branches", "100"),
        ("covered_branches", True),
        ("num_branches", -1),
        ("covered_branches", -1),
    ],
)
def test_acceptance_tcb_coverage_rejects_coerced_or_negative_counts(
    tmp_path: Path,
    field: str,
    value: object,
) -> None:
    kwargs = {"num_branches": 100, "covered_branches": 100}
    kwargs[field] = value
    report_path = _write_report(tmp_path, _coverage_report(**kwargs))

    assert main(["check_acceptance_tcb_coverage.py", str(report_path)]) == 1


def test_acceptance_tcb_coverage_rejects_impossible_covered_count(tmp_path: Path) -> None:
    report_path = _write_report(tmp_path, _coverage_report(num_branches=10, covered_branches=11))

    assert main(["check_acceptance_tcb_coverage.py", str(report_path)]) == 1
