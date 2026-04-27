#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_WORKDIR = ROOT / "tools" / "dex-ui"
SEVERITIES = ("info", "low", "moderate", "high", "critical")


def severity_counts(payload: dict[str, Any]) -> dict[str, int]:
    metadata = payload.get("metadata")
    if isinstance(metadata, dict):
        vulnerabilities = metadata.get("vulnerabilities")
        if isinstance(vulnerabilities, dict):
            return {
                severity: int(vulnerabilities.get(severity, 0) or 0)
                for severity in SEVERITIES
            }

    counts = {severity: 0 for severity in SEVERITIES}
    vulnerabilities = payload.get("vulnerabilities")
    if not isinstance(vulnerabilities, dict):
        return counts
    for finding in vulnerabilities.values():
        if not isinstance(finding, dict):
            continue
        severity = finding.get("severity")
        if isinstance(severity, str) and severity in counts:
            counts[severity] += 1
    return counts


def audit_is_clean(payload: dict[str, Any]) -> tuple[bool, dict[str, int], int]:
    if payload.get("error"):
        counts = {severity: 0 for severity in SEVERITIES}
        return False, counts, 0
    counts = severity_counts(payload)
    total = sum(counts.values())
    return total == 0, counts, total


def _run_npm_audit(workdir: Path) -> dict[str, Any]:
    proc = subprocess.run(
        ["npm", "audit", "--json"],
        cwd=workdir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if not proc.stdout.strip():
        raise RuntimeError(f"npm audit produced no JSON output; stderr:\n{proc.stderr.strip()}")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"npm audit output was not valid JSON: {exc}") from exc


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run npm audit for the DEX UI and fail closed unless the audit reports "
            "zero vulnerabilities across all severities."
        )
    )
    parser.add_argument("--workdir", type=Path, default=DEFAULT_WORKDIR)
    parser.add_argument("--audit-json", type=Path, help="parse an existing npm audit JSON report")
    args = parser.parse_args(argv)

    try:
        if args.audit_json is None:
            payload = _run_npm_audit(args.workdir)
        else:
            payload = json.loads(args.audit_json.read_text(encoding="utf-8"))
    except (OSError, RuntimeError, json.JSONDecodeError) as exc:
        print(f"error: failed to read npm audit report: {exc}", file=sys.stderr)
        return 2

    ok, counts, total = audit_is_clean(payload)
    print(
        json.dumps(
            {
                "schema": "zenodex/dex-ui-dependency-audit-check/v1",
                "ok": ok,
                "total_vulnerabilities": total,
                "severity_counts": counts,
            },
            indent=2,
            sort_keys=True,
        )
    )
    if ok:
        return 0
    print(
        "error: DEX UI dependency audit found vulnerabilities; update the lockfile "
        "or document and gate a temporary exception",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
