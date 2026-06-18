from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import pytest

import tools.check_derivatives_evidence_manifest as checker


def _valid_report() -> dict[str, Any]:
    return {
        "model_id": "perp-epoch-v1",
        "ir_hash": "abc123",
        "verdict": "VERIFIED",
        "failed_queries": 0,
        "inconclusive_queries": 0,
        "passed_queries": 7,
        "scope": {
            "kind": "inductive",
            "k": 1,
            "solver_timeout_ms": 25_000,
            "fail_closed": True,
        },
        "z3_passed": True,
        "cvc5_available": True,
        "cvc5_passed": True,
        "solvers_agreed": True,
        "tool_versions": {
            "esso_code_hash": "esso-head",
            "solvers": {
                "z3": "z3 4.13.3",
                "cvc5": "cvc5 1.2.0",
            },
        },
    }


def _valid_entry(report_path: Path) -> dict[str, Any]:
    return {
        "report_path": str(report_path),
        "model_id": "perp-epoch-v1",
        "ir_hash": "abc123",
        "passed_queries": 7,
        "solver_timeout_ms": 25_000,
        "solvers": ["z3", "cvc5"],
        "toolchain": {
            "esso_code_hash": "esso-head",
            "solvers": {
                "z3": "z3 4.13.3",
                "cvc5": "cvc5 1.2.0",
            },
        },
    }


def _write_report(tmp_path: Path, report: dict[str, Any]) -> Path:
    path = tmp_path / "report.json"
    path.write_text(json.dumps(report, sort_keys=True), encoding="utf-8")
    return path


def test_derivatives_verify_multi_accepts_strictly_typed_report(tmp_path: Path) -> None:
    report_path = _write_report(tmp_path, _valid_report())

    checker._check_verify_multi(_valid_entry(report_path))


@pytest.mark.parametrize(
    ("path", "value", "match"),
    [
        (("failed_queries",), "0", "failed_queries: expected int"),
        (("passed_queries",), True, "passed_queries: expected int"),
        (("scope", "k"), "1", "scope.k: expected int"),
        (("scope", "fail_closed"), 1, "scope.fail_closed: expected bool"),
        (("z3_passed",), 1, "z3_passed: expected bool"),
        (("solvers_agreed",), "true", "solvers_agreed: expected bool"),
    ],
)
def test_derivatives_verify_multi_rejects_coerced_report_fields(
    tmp_path: Path,
    path: tuple[str, ...],
    value: object,
    match: str,
) -> None:
    report = _valid_report()
    target: dict[str, Any] = report
    for key in path[:-1]:
        next_target = target[key]
        assert isinstance(next_target, dict)
        target = next_target
    target[path[-1]] = value
    report_path = _write_report(tmp_path, report)

    with pytest.raises(checker.ManifestError, match=match):
        checker._check_verify_multi(_valid_entry(report_path))


def test_derivatives_verify_multi_rejects_coerced_expected_entry_fields(tmp_path: Path) -> None:
    report_path = _write_report(tmp_path, _valid_report())
    entry = copy.deepcopy(_valid_entry(report_path))
    entry["passed_queries"] = "7"

    with pytest.raises(checker.ManifestError, match="expected passed_queries: expected int"):
        checker._check_verify_multi(entry)
