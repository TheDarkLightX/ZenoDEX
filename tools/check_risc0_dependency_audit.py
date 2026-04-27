#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_WORKDIR = ROOT / "zk" / "state_proof_risc0"
DEFAULT_ALLOWED_VULNERABILITIES: frozenset[str] = frozenset()


def _advisory_id(entry: dict[str, Any]) -> str:
    advisory = entry.get("advisory")
    if isinstance(advisory, dict):
        raw = advisory.get("id")
        if isinstance(raw, str):
            return raw.strip()
    return ""


def vulnerability_ids(payload: dict[str, Any]) -> list[str]:
    vulnerabilities = payload.get("vulnerabilities")
    if not isinstance(vulnerabilities, dict):
        return []
    entries = vulnerabilities.get("list")
    if not isinstance(entries, list):
        return []
    ids: list[str] = []
    for entry in entries:
        if isinstance(entry, dict):
            advisory_id = _advisory_id(entry)
            if advisory_id:
                ids.append(advisory_id)
    return sorted(ids)


def warning_ids(payload: dict[str, Any]) -> list[str]:
    warnings = payload.get("warnings")
    if not isinstance(warnings, dict):
        return []
    ids: list[str] = []
    for entries in warnings.values():
        if not isinstance(entries, list):
            continue
        for entry in entries:
            if isinstance(entry, dict):
                advisory_id = _advisory_id(entry)
                if advisory_id:
                    ids.append(advisory_id)
    return sorted(ids)


def audit_is_acceptable(
    payload: dict[str, Any],
    *,
    allowed_vulnerabilities: Iterable[str] = DEFAULT_ALLOWED_VULNERABILITIES,
) -> tuple[bool, list[str], list[str], list[str]]:
    allowed = {item.strip() for item in allowed_vulnerabilities if item.strip()}
    vulns = vulnerability_ids(payload)
    warnings = warning_ids(payload)
    unexpected = sorted(vuln for vuln in vulns if vuln not in allowed)
    return not unexpected, vulns, warnings, unexpected


def _run_cargo_audit(workdir: Path, *, no_fetch: bool) -> dict[str, Any]:
    cmd = ["cargo", "audit", "--json"]
    if no_fetch:
        cmd.append("--no-fetch")
    proc = subprocess.run(
        cmd,
        cwd=workdir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if not proc.stdout.strip():
        raise RuntimeError(f"cargo audit produced no JSON output; stderr:\n{proc.stderr.strip()}")
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"cargo audit output was not valid JSON: {exc}") from exc
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run cargo-audit for the RISC Zero state-proof workspace and fail on any "
            "RustSec vulnerability unless a caller explicitly supplies a temporary allowlist."
        )
    )
    parser.add_argument("--workdir", type=Path, default=DEFAULT_WORKDIR)
    parser.add_argument("--audit-json", type=Path, help="parse an existing cargo-audit JSON report")
    parser.add_argument("--no-fetch", action="store_true", help="pass --no-fetch to cargo audit")
    parser.add_argument(
        "--allow",
        action="append",
        default=[],
        help="additional RustSec advisory id to allow temporarily",
    )
    args = parser.parse_args(argv)

    allowed = set(DEFAULT_ALLOWED_VULNERABILITIES)
    allowed.update(str(item).strip() for item in args.allow if str(item).strip())

    try:
        if args.audit_json is None:
            payload = _run_cargo_audit(args.workdir, no_fetch=args.no_fetch)
        else:
            payload = json.loads(args.audit_json.read_text(encoding="utf-8"))
    except (OSError, RuntimeError, json.JSONDecodeError) as exc:
        print(f"error: failed to read cargo audit report: {exc}", file=sys.stderr)
        return 2

    ok, vulns, warnings, unexpected = audit_is_acceptable(
        payload,
        allowed_vulnerabilities=allowed,
    )
    print(
        json.dumps(
            {
                "schema": "zenodex/risc0-dependency-audit-check/v1",
                "ok": ok,
                "allowed_vulnerabilities": sorted(allowed),
                "vulnerability_ids": vulns,
                "warning_ids": warnings,
                "unexpected_vulnerability_ids": unexpected,
            },
            indent=2,
            sort_keys=True,
        )
    )
    if ok:
        return 0
    print(
        "error: RISC Zero dependency vulnerabilities found; "
        "do not add a temporary exception without a new audit note",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
