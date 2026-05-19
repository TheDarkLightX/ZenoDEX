#!/usr/bin/env python3
"""Check the production Python install helper uses hash-locked lockfiles."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT_SCHEMA = "zenodex.python_hash_lock_install_surface_check.v1"
INSTALL_SCRIPT = ROOT / "tools" / "install_python_hash_locked_deps.sh"
INSTALL_DOC = ROOT / "docs" / "PYTHON_HASH_LOCK_INSTALL.md"
LOCK_FILES = (
    "requirements-core.lock.txt",
    "requirements-agents.lock.txt",
    "requirements-dev.lock.txt",
)


def _read(path: Path, errors: list[str]) -> str:
    if not path.is_file():
        errors.append(f"missing_file:{path.relative_to(ROOT)}")
        return ""
    return path.read_text(encoding="utf-8")


def run_check() -> dict[str, object]:
    errors: list[str] = []
    script = _read(INSTALL_SCRIPT, errors)
    doc = _read(INSTALL_DOC, errors)

    if script:
        if "--require-hashes" not in script:
            errors.append("install_script_missing_require_hashes")
        if "pip install" not in script:
            errors.append("install_script_missing_pip_install")
        for lock_file in LOCK_FILES:
            if lock_file not in script:
                errors.append(f"install_script_missing_lock:{lock_file}")

    if doc:
        if "--require-hashes" not in doc:
            errors.append("install_doc_missing_require_hashes")
        for lock_file in LOCK_FILES:
            if lock_file not in doc:
                errors.append(f"install_doc_missing_lock:{lock_file}")

    return {
        "schema": RESULT_SCHEMA,
        "ok": not errors,
        "install_script": str(INSTALL_SCRIPT.relative_to(ROOT)),
        "install_doc": str(INSTALL_DOC.relative_to(ROOT)),
        "lock_files": list(LOCK_FILES),
        "errors": errors,
    }


def main() -> int:
    result = run_check()
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
