#!/usr/bin/env python3
"""Check Python lockfiles are exact-pinned and hash-pinned."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT_SCHEMA = "zenodex.python_hash_locks_check.v1"
DEFAULT_LOCK_FILES = (
    "requirements-core.lock.txt",
    "requirements-agents.lock.txt",
    "requirements-dev.lock.txt",
)

_PIN_RE = re.compile(r"^([A-Za-z0-9_.-]+(?:\[[A-Za-z0-9_,.-]+\])?)==([^\\\s]+)")
_HASH_RE = re.compile(r"--hash=sha256:([0-9a-f]{64})\b")


@dataclass(frozen=True)
class LockFileStats:
    relpath: str
    package_count: int
    hash_count: int
    errors: tuple[str, ...]


def _check_lock_file(relpath: str) -> LockFileStats:
    path = ROOT / relpath
    errors: list[str] = []
    package_count = 0
    hash_count = 0
    current_package: str | None = None
    current_hashes = 0

    if not path.is_file():
        return LockFileStats(relpath=relpath, package_count=0, hash_count=0, errors=(f"missing_lock_file:{relpath}",))

    def close_current(line_number: int) -> None:
        nonlocal current_package, current_hashes
        if current_package is not None and current_hashes == 0:
            errors.append(f"{relpath}:{line_number}:missing_hashes:{current_package}")
        current_package = None
        current_hashes = 0

    text = path.read_text(encoding="utf-8")
    if "pip-compile" not in text or "--generate-hashes" not in text:
        errors.append(f"{relpath}:missing_generate_hashes_header")

    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        stripped = raw_line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        found_hashes = _HASH_RE.findall(stripped)
        hash_count += len(found_hashes)

        is_continuation = raw_line[:1].isspace()
        if is_continuation:
            if current_package is None and found_hashes:
                errors.append(f"{relpath}:{line_number}:orphan_hash")
            current_hashes += len(found_hashes)
            continue

        if stripped.startswith("--"):
            if stripped.startswith("--hash"):
                errors.append(f"{relpath}:{line_number}:orphan_hash")
            continue

        close_current(line_number - 1)
        match = _PIN_RE.match(stripped)
        if not match:
            errors.append(f"{relpath}:{line_number}:non_exact_requirement:{stripped}")
            continue
        current_package = match.group(1)
        current_hashes = len(found_hashes)
        package_count += 1

    close_current(len(text.splitlines()))
    return LockFileStats(
        relpath=relpath,
        package_count=package_count,
        hash_count=hash_count,
        errors=tuple(errors),
    )


def run_check(lock_files: tuple[str, ...] = DEFAULT_LOCK_FILES) -> dict[str, object]:
    stats = [_check_lock_file(relpath) for relpath in lock_files]
    errors = [error for item in stats for error in item.errors]
    return {
        "schema": RESULT_SCHEMA,
        "ok": not errors,
        "lock_files": {
            item.relpath: {
                "package_count": item.package_count,
                "hash_count": item.hash_count,
            }
            for item in stats
        },
        "errors": errors,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit JSON output.")
    parser.add_argument("lock_files", nargs="*", help="Lock files to check.")
    args = parser.parse_args(argv)

    lock_files = tuple(args.lock_files) if args.lock_files else DEFAULT_LOCK_FILES
    result = run_check(lock_files)
    if args.json or not result["ok"]:
        print(json.dumps(result, sort_keys=True, indent=2))
    else:
        print("ok: Python hash lockfiles accepted")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
