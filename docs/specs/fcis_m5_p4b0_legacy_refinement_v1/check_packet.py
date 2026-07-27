#!/usr/bin/env python3
"""Fail-closed consistency check for the M5-P4B0 implementation packet."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parent
_REQUIRED_FILES = frozenset(
    {
        "CONTRACT.md",
        "IMPLEMENTOR_PROMPT.md",
        "README.md",
        "REVIEW_CHECKLIST.md",
        "TEST_MATRIX.md",
        "check_packet.py",
        "requirements.json",
    }
)
_REQUIREMENT_PATTERN = re.compile(r"P4B0-\d{3}")
_TEST_PATTERN = re.compile(r"P4B0-[A-Z]+-\d{3}")


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _load_requirements() -> dict[str, object]:
    value = json.loads(
        (_ROOT / "requirements.json").read_text(encoding="utf-8"),
        object_pairs_hook=_strict_object,
    )
    if type(value) is not dict:
        raise ValueError("requirements.json must contain one object")
    return cast(dict[str, object], value)


def _fail(message: str) -> None:
    raise SystemExit(f"ERROR: {message}")


def main() -> int:
    actual_files = {
        path.name
        for path in _ROOT.iterdir()
        if path.is_file() and not path.name.endswith((".orig", ".rej", "~"))
    }
    forbidden_backups = sorted(
        path.name
        for path in _ROOT.iterdir()
        if path.is_file() and path.name.endswith((".orig", ".rej", "~"))
    )
    if forbidden_backups:
        _fail(f"backup/reject files present: {forbidden_backups}")
    if actual_files != _REQUIRED_FILES:
        _fail(
            f"packet files changed: missing={sorted(_REQUIRED_FILES - actual_files)}, "
            f"unknown={sorted(actual_files - _REQUIRED_FILES)}"
        )
    requirements = _load_requirements()
    if requirements.get("schema") != ("zenodex/fcis-m5-p4b0-legacy-refinement-requirements/v1"):
        _fail("requirements schema mismatch")
    if requirements.get("required_ancestor") != "fd1ef9f1":
        _fail("required ancestor mismatch")
    normative = requirements.get("normative_files")
    if type(normative) is not list or set(normative) != _REQUIRED_FILES:
        _fail("normative_files must equal the complete packet file set")
    raw_rows = requirements.get("requirements")
    if type(raw_rows) is not list or any(type(row) is not dict for row in raw_rows):
        _fail("requirements must be a list of objects")
    rows = cast(list[dict[str, object]], raw_rows)
    ids = [row.get("id") for row in rows]
    if ids != [f"P4B0-{index:03d}" for index in range(1, 21)]:
        _fail("requirement IDs must be exactly P4B0-001 through P4B0-020")
    contract = (_ROOT / "CONTRACT.md").read_text(encoding="utf-8")
    matrix = (_ROOT / "TEST_MATRIX.md").read_text(encoding="utf-8")
    checklist = (_ROOT / "REVIEW_CHECKLIST.md").read_text(encoding="utf-8")
    declared_tests: list[str] = []
    for row in rows:
        requirement_id = cast(str, row["id"])
        if requirement_id not in contract or requirement_id not in checklist:
            _fail(f"{requirement_id} missing from contract or review checklist")
        tests = row.get("test_ids")
        if type(tests) is not list or not tests or any(type(test) is not str for test in tests):
            _fail(f"{requirement_id} test_ids malformed")
        declared_tests.extend(cast(list[str], tests))
    if len(declared_tests) != len(set(declared_tests)):
        _fail("test IDs are duplicated across requirements")
    matrix_tests = set(_TEST_PATTERN.findall(matrix))
    if matrix_tests != set(declared_tests):
        _fail(
            f"test matrix mismatch: missing={sorted(set(declared_tests) - matrix_tests)}, "
            f"unknown={sorted(matrix_tests - set(declared_tests))}"
        )
    if set(_REQUIREMENT_PATTERN.findall(contract)) != set(cast(list[str], ids)):
        _fail("contract requirement inventory is incomplete or contains unknown IDs")
    prompt = (_ROOT / "IMPLEMENTOR_PROMPT.md").read_text(encoding="utf-8")
    for required_text in (
        "fd1ef9f1",
        "M5_P4B0_REFINEMENT_EVIDENCE_ONLY",
        "Do not switch mounted authority",
        "admit(declared_schema, value, path, context)",
        "--require-all-refine",
    ):
        if required_text not in prompt:
            _fail(f"implementor prompt omits required boundary text: {required_text}")
    print(
        json.dumps(
            {
                "ok": True,
                "requirements": len(rows),
                "declared_tests": len(declared_tests),
                "normative_files": len(_REQUIRED_FILES),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
