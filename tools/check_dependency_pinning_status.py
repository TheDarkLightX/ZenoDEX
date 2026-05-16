#!/usr/bin/env python3
"""Check dependency pinning status against the committed ratchet."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
STATUS_PATH = ROOT / "docs" / "dependency_pinning_status.json"
RESULT_SCHEMA = "zenodex.dependency_pinning_status_check.v1"
STATUS_SCHEMA = "zenodex.dependency_pinning_status.v1"

_EXACT_PIN_RE = re.compile(r"^[A-Za-z0-9_.-]+(\[[A-Za-z0-9_,.-]+\])?==[^=<>!~]+$")


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_str_list(value: object, *, name: str) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
        raise TypeError(f"{name} must be a list of non-empty strings")
    return list(value)


def _requirement_lines(path: Path) -> list[str]:
    out: list[str] = []
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.split("#", 1)[0].strip()
        if not line or line.startswith("-r ") or line.startswith("--"):
            continue
        out.append(line)
    return out


def _is_exact_pin(requirement: str) -> bool:
    return bool(_EXACT_PIN_RE.fullmatch(requirement))


def _actual_unpinned(files: list[str]) -> list[str]:
    found: list[str] = []
    for relpath in files:
        path = ROOT / relpath
        for requirement in _requirement_lines(path):
            if not _is_exact_pin(requirement):
                found.append(f"{relpath}:{requirement}")
    return sorted(found)


def run_check() -> dict[str, object]:
    status = _require_mapping(json.loads(STATUS_PATH.read_text(encoding="utf-8")), name="status")
    errors: list[str] = []
    if status.get("schema") != STATUS_SCHEMA:
        errors.append("schema mismatch")
        return {"schema": RESULT_SCHEMA, "ok": False, "errors": errors}

    files = _require_str_list(status.get("python_requirement_files"), name="python_requirement_files")
    expected_unpinned = sorted(
        _require_str_list(status.get("known_unpinned_python_requirements"), name="known_unpinned_python_requirements")
    )
    actual_unpinned = _actual_unpinned(files)
    if actual_unpinned != expected_unpinned:
        missing = sorted(set(expected_unpinned) - set(actual_unpinned))
        unexpected = sorted(set(actual_unpinned) - set(expected_unpinned))
        if missing:
            errors.append(f"known_unpinned_missing:{missing}")
        if unexpected:
            errors.append(f"new_unpinned_python_requirements:{unexpected}")

    for required in _require_str_list(status.get("exact_python_pins_required"), name="exact_python_pins_required"):
        relpath, _, requirement = required.partition(":")
        if not relpath or not requirement:
            errors.append(f"malformed_exact_pin_requirement:{required}")
            continue
        if requirement not in _requirement_lines(ROOT / relpath):
            errors.append(f"missing_exact_python_pin:{required}")
        elif not _is_exact_pin(requirement):
            errors.append(f"not_exact_python_pin:{required}")

    for relpath in _require_str_list(status.get("required_lock_artifacts"), name="required_lock_artifacts"):
        if not (ROOT / relpath).is_file():
            errors.append(f"missing_lock_artifact:{relpath}")

    return {
        "schema": RESULT_SCHEMA,
        "ok": not errors,
        "python_requirement_files": files,
        "known_unpinned_count": len(expected_unpinned),
        "errors": errors,
    }


def main() -> int:
    result = run_check()
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
