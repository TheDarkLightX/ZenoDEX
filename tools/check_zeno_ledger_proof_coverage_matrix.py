#!/usr/bin/env python3
"""Validate the ZenoLedger proof coverage matrix."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_zeno_ledger_risc0_real_proof_smoke_report import (  # noqa: E402
    DEFAULT_REQUIRED_CASES,
    PROOF_TYPE,
)

MATRIX_PATH = ROOT / "docs" / "ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json"
MATRIX_SCHEMA = "zenodex.zeno_ledger.proof_coverage_matrix.v0"
CHECK_SCHEMA = "zenodex.zeno_ledger.proof_coverage_matrix_check.v0"
ALLOWED_STATUSES = {"covered_required", "covered_model_only", "open_gap"}


def validate_proof_coverage_matrix_v0(matrix: Any, *, root: Path = ROOT) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(matrix, "matrix", errors)
    if obj.get("schema") != MATRIX_SCHEMA:
        errors.append("schema mismatch")
    if obj.get("proof_type") != PROOF_TYPE:
        errors.append("proof_type mismatch")

    declared_cases = _str_list(
        obj.get("current_required_real_proof_cases"),
        "current_required_real_proof_cases",
        errors,
    )
    _require_unique(declared_cases, "current_required_real_proof_cases", errors)
    declared_set = set(declared_cases)
    expected_cases = set(DEFAULT_REQUIRED_CASES)
    if declared_set != expected_cases:
        errors.append(
            "current_required_real_proof_cases mismatch: "
            f"missing={','.join(sorted(expected_cases - declared_set)) or '-'} "
            f"unexpected={','.join(sorted(declared_set - expected_cases)) or '-'}"
        )

    supported_kinds = _str_list(
        obj.get("current_supported_intent_kinds"),
        "current_supported_intent_kinds",
        errors,
    )
    _require_unique(supported_kinds, "current_supported_intent_kinds", errors)

    coverage = _list(obj.get("coverage"), "coverage", errors)
    seen_ids: set[str] = set()
    covered_required: set[str] = set()
    open_gap_count = 0
    model_only_count = 0

    for index, raw_entry in enumerate(coverage):
        entry_errors: list[str] = []
        entry = _mapping(raw_entry, f"coverage[{index}]", entry_errors)
        entry_id = _str(entry.get("id"), f"coverage[{index}].id", entry_errors)
        if entry_id is not None:
            if entry_id in seen_ids:
                entry_errors.append(f"coverage[{index}].id duplicate:{entry_id}")
            seen_ids.add(entry_id)
        status = _str(entry.get("status"), f"coverage[{index}].status", entry_errors)
        if status is not None and status not in ALLOWED_STATUSES:
            entry_errors.append(f"coverage[{index}].status unsupported:{status}")

        evidence_files = _str_list(entry.get("evidence_files"), f"coverage[{index}].evidence_files", entry_errors)
        _require_unique(evidence_files, f"coverage[{index}].evidence_files", entry_errors)
        for path_text in evidence_files:
            _require_existing_repo_path(root, path_text, f"coverage[{index}].evidence_files", entry_errors)

        if status == "covered_required":
            _str(entry.get("claim"), f"coverage[{index}].claim", entry_errors)
            required_case = _str(entry.get("required_case"), f"coverage[{index}].required_case", entry_errors)
            if required_case is not None:
                if required_case not in expected_cases:
                    entry_errors.append(f"coverage[{index}].required_case unsupported:{required_case}")
                if required_case in covered_required:
                    entry_errors.append(f"coverage[{index}].required_case duplicate:{required_case}")
                covered_required.add(required_case)
        elif status == "covered_model_only":
            model_only_count += 1
            _str(entry.get("claim"), f"coverage[{index}].claim", entry_errors)
        elif status == "open_gap":
            open_gap_count += 1
            _str(entry.get("gap"), f"coverage[{index}].gap", entry_errors)
            blockers = _str_list(entry.get("blocking_for"), f"coverage[{index}].blocking_for", entry_errors)
            _require_unique(blockers, f"coverage[{index}].blocking_for", entry_errors)

        errors.extend(entry_errors)

    if covered_required != expected_cases:
        errors.append(
            "covered_required cases mismatch: "
            f"missing={','.join(sorted(expected_cases - covered_required)) or '-'} "
            f"unexpected={','.join(sorted(covered_required - expected_cases)) or '-'}"
        )
    if open_gap_count == 0:
        errors.append("coverage must include at least one open_gap entry")

    return {
        "schema": CHECK_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "proof_type": obj.get("proof_type"),
        "required_cases": sorted(DEFAULT_REQUIRED_CASES),
        "declared_required_cases": sorted(declared_set),
        "covered_required_cases": sorted(covered_required),
        "coverage_entry_count": len(coverage),
        "open_gap_count": open_gap_count,
        "covered_model_only_count": model_only_count,
    }


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if isinstance(value, list) and value:
        return value
    errors.append(f"{name} must be a non-empty list")
    return []


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if isinstance(value, str) and value:
        return value
    errors.append(f"{name} must be a non-empty string")
    return None


def _str_list(value: Any, name: str, errors: list[str]) -> list[str]:
    items = _list(value, name, errors)
    out: list[str] = []
    for index, item in enumerate(items):
        text = _str(item, f"{name}[{index}]", errors)
        if text is not None:
            out.append(text)
    return out


def _require_unique(items: list[str], name: str, errors: list[str]) -> None:
    seen: set[str] = set()
    for item in items:
        if item in seen:
            errors.append(f"{name} duplicate:{item}")
        seen.add(item)


def _require_existing_repo_path(root: Path, path_text: str, name: str, errors: list[str]) -> None:
    path = (root / path_text).resolve()
    if root.resolve() not in path.parents and path != root.resolve():
        errors.append(f"{name} path outside repo:{path_text}")
        return
    if not path.exists():
        errors.append(f"{name} missing_path:{path_text}")


def _load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("matrix", nargs="?", type=Path, default=MATRIX_PATH)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    result = validate_proof_coverage_matrix_v0(_load_json(args.matrix))
    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
