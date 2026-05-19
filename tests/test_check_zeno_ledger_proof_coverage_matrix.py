from __future__ import annotations

import json
import subprocess
import sys
from copy import deepcopy
from pathlib import Path

from tools.check_zeno_ledger_proof_coverage_matrix import (
    MATRIX_PATH,
    validate_proof_coverage_matrix_v0,
)
from tools.check_zeno_ledger_risc0_real_proof_smoke_report import DEFAULT_REQUIRED_CASES


ROOT = Path(__file__).resolve().parents[1]


def _load_matrix() -> dict[str, object]:
    return json.loads(MATRIX_PATH.read_text(encoding="utf-8"))


def test_default_matrix_is_accepted() -> None:
    result = validate_proof_coverage_matrix_v0(_load_matrix())

    assert result["ok"] is True
    assert set(result["declared_required_cases"]) == set(DEFAULT_REQUIRED_CASES)
    assert set(result["covered_required_cases"]) == set(DEFAULT_REQUIRED_CASES)
    assert result["open_gap_count"] >= 1


def test_rejects_missing_declared_required_case() -> None:
    matrix = _load_matrix()
    matrix["current_required_real_proof_cases"] = ["empty"]

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("current_required_real_proof_cases mismatch" in error for error in result["errors"])


def test_rejects_missing_covered_required_case() -> None:
    matrix = _load_matrix()
    matrix["coverage"] = [
        entry
        for entry in matrix["coverage"]
        if not (isinstance(entry, dict) and entry.get("required_case") == "swap_exact_out")
    ]

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("covered_required cases mismatch" in error for error in result["errors"])


def test_rejects_unknown_required_case_in_coverage() -> None:
    matrix = _load_matrix()
    matrix["coverage"] = deepcopy(matrix["coverage"])
    for entry in matrix["coverage"]:
        if isinstance(entry, dict) and entry.get("required_case") == "empty":
            entry["required_case"] = "unsupported_case"
            break

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("required_case unsupported:unsupported_case" in error for error in result["errors"])


def test_rejects_open_gap_without_blockers() -> None:
    matrix = _load_matrix()
    matrix["coverage"] = deepcopy(matrix["coverage"])
    for entry in matrix["coverage"]:
        if isinstance(entry, dict) and entry.get("status") == "open_gap":
            entry["blocking_for"] = []
            break

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("blocking_for must be a non-empty list" in error for error in result["errors"])


def test_rejects_missing_evidence_file() -> None:
    matrix = _load_matrix()
    matrix["coverage"] = deepcopy(matrix["coverage"])
    first_entry = matrix["coverage"][0]
    assert isinstance(first_entry, dict)
    first_entry["evidence_files"] = ["missing/nope.txt"]

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("missing_path:missing/nope.txt" in error for error in result["errors"])


def test_cli_pretty_accepts_default_matrix() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(ROOT / "tools/check_zeno_ledger_proof_coverage_matrix.py"),
            "--pretty",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    result = json.loads(completed.stdout)
    assert result["ok"] is True
