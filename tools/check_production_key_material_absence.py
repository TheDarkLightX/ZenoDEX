#!/usr/bin/env python3
"""Scan tracked files for production key-management secret material."""

from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RESULT_SCHEMA = "zenodex.production_key_material_absence_check.v1"

SKIP_PREFIXES = (
    ".git/",
    "internal/",
)

SECRET_PATTERNS = {
    "pem_private_key": re.compile(r"BEGIN [A-Z ]*PRIVATE KEY"),
    "mnemonic_value": re.compile(r"(?i)\bmnemonic\s*:\s*\S+"),
    "seed_phrase_value": re.compile(r"(?i)\bseed phrase\s*:\s*\S+"),
    "secret_env_value": re.compile(r"\bSECRET\s*=\s*\S+"),
    "password_env_value": re.compile(r"\bPASSWORD\s*=\s*\S+"),
    "private_key_hex_literal": re.compile(
        r"(?i)\b(?:private_key_hex|bls_private_key_hex)\s*=\s*[\"']0x[0-9a-f]{64}[\"']"
    ),
}

INSTRUCTIONAL_ALLOWED = {
    ("tools/check_production_key_material_absence.py", "SECRET"),
    ("tools/check_production_key_material_absence.py", "PASSWORD"),
    ("docs/PRODUCTION_KEY_MANAGEMENT_AGENT_TASKS.md", "SECRET=|PASSWORD="),
    ("docs/PRODUCTION_KEY_MANAGEMENT_RUNBOOK.md", "mnemonic"),
    ("docs/PRODUCTION_KEY_MANAGEMENT_RUNBOOK.md", "private"),
    ("docs/PRODUCTION_KEY_MANAGEMENT_V0_SPEC.md", "seed phrases"),
    ("docs/PRODUCTION_KEY_MANAGEMENT_V0_SPEC.md", "private keys"),
}

TEST_FIXTURE_MARKERS = (
    "TEST_BLS_PRIVATE_KEY_A",
    "TEST_BLS_PRIVATE_KEY_B",
    "private_key=42",
    "private_key=43",
    "private_key=44",
    "private_key=45",
    "private_key=81",
    "private_key=144",
)


def _tracked_files() -> list[Path]:
    proc = subprocess.run(
        ["git", "ls-files"],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    paths: list[Path] = []
    for raw in proc.stdout.splitlines():
        if not raw or raw.startswith(SKIP_PREFIXES):
            continue
        paths.append(ROOT / raw)
    return sorted(paths)


def _is_text(path: Path) -> bool:
    try:
        chunk = path.read_bytes()[:4096]
    except OSError:
        return False
    return b"\x00" not in chunk


def _allowed_instructional(path: str, line: str) -> bool:
    return any(path == allowed_path and token in line for allowed_path, token in INSTRUCTIONAL_ALLOWED)


def _allowed_test_fixture(path: str, line: str) -> bool:
    if not path.startswith(("tests/", "tools/zenodex_oracle_", "tools/zeno_oracle_")):
        return False
    return any(marker in line.replace(" ", "") for marker in TEST_FIXTURE_MARKERS)


def _scan_file(path: Path) -> list[dict[str, object]]:
    if not _is_text(path):
        return []
    rel = str(path.relative_to(ROOT))
    issues: list[dict[str, object]] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except UnicodeDecodeError:
        return []
    for lineno, line in enumerate(lines, start=1):
        if _allowed_instructional(rel, line) or _allowed_test_fixture(rel, line):
            continue
        for kind, pattern in SECRET_PATTERNS.items():
            if pattern.search(line):
                issues.append(
                    {
                        "path": rel,
                        "line": lineno,
                        "kind": kind,
                    }
                )
    return issues


def run_check() -> dict[str, object]:
    files = _tracked_files()
    issues: list[dict[str, object]] = []
    for path in files:
        issues.extend(_scan_file(path))
    return {
        "schema": RESULT_SCHEMA,
        "ok": not issues,
        "checked_file_count": len(files),
        "issues": issues,
        "scope": "tracked files excluding internal evidence archives",
    }


def main() -> int:
    result = run_check()
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
