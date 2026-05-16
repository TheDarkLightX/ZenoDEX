#!/usr/bin/env python3
"""Validate the production traceability matrix."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
MATRIX_PATH = ROOT / "docs" / "production_traceability_matrix.json"
RESULT_SCHEMA = "zenodex.production_traceability_matrix_check.v1"
MATRIX_SCHEMA = "zenodex.production_traceability_matrix.v1"
ALLOWED_STATUSES = {"supported", "supported_scoped", "supported_replay", "supported_ratchet", "open"}


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_str(value: object, *, name: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not allow_empty and value == "":
        raise ValueError(f"{name} must be non-empty")
    return value


def _require_str_list(value: object, *, name: str, allow_empty: bool = False) -> list[str]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    if not allow_empty and not value:
        raise ValueError(f"{name} must be non-empty")
    out: list[str] = []
    for index, item in enumerate(value):
        out.append(_require_str(item, name=f"{name}[{index}]"))
    return out


def _path_exists(path: str) -> bool:
    return (ROOT / path).exists()


def validate_matrix(matrix: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if matrix.get("schema") != MATRIX_SCHEMA:
        errors.append("schema mismatch")
        return errors
    entries = matrix.get("entries")
    if not isinstance(entries, list) or not entries:
        errors.append("entries must be a non-empty list")
        return errors

    seen_ids: set[str] = set()
    for index, raw_entry in enumerate(entries):
        prefix = f"entries[{index}]"
        try:
            entry = _require_mapping(raw_entry, name=prefix)
            entry_id = _require_str(entry.get("id"), name=f"{prefix}.id")
            if entry_id in seen_ids:
                errors.append(f"{prefix}.id duplicate:{entry_id}")
            seen_ids.add(entry_id)
            status = _require_str(entry.get("status"), name=f"{prefix}.status")
            if status not in ALLOWED_STATUSES:
                errors.append(f"{prefix}.status unsupported:{status}")
            _require_str(entry.get("invariant"), name=f"{prefix}.invariant")
            _require_str(entry.get("residual_limits"), name=f"{prefix}.residual_limits")
            runtime_paths = _require_str_list(entry.get("runtime_guard_paths"), name=f"{prefix}.runtime_guard_paths")
            test_paths = _require_str_list(entry.get("test_paths"), name=f"{prefix}.test_paths")
            evidence_commands = _require_str_list(entry.get("evidence_commands"), name=f"{prefix}.evidence_commands")
            for path in runtime_paths + test_paths:
                if not _path_exists(path):
                    errors.append(f"{prefix}.missing_path:{path}")
            for command in evidence_commands:
                if "\n" in command or "\r" in command:
                    errors.append(f"{prefix}.evidence_command_multiline:{entry_id}")
        except Exception as exc:
            errors.append(f"{prefix}:{exc}")
    return errors


def run_check() -> dict[str, object]:
    matrix = _require_mapping(json.loads(MATRIX_PATH.read_text(encoding="utf-8")), name="matrix")
    errors = validate_matrix(matrix)
    return {
        "schema": RESULT_SCHEMA,
        "ok": not errors,
        "matrix_path": str(MATRIX_PATH.relative_to(ROOT)),
        "entry_count": len(matrix.get("entries", [])) if isinstance(matrix.get("entries"), list) else 0,
        "errors": errors,
    }


def main() -> int:
    result = run_check()
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
