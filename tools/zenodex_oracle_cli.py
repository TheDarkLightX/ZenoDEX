#!/usr/bin/env python3
"""Unified local CLI for the Zeno Oracle MVP verifier shell."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO = Path(__file__).resolve().parents[1]
TOOLS = REPO / "tools"

SURFACES: dict[str, str] = {
    "receipt": "zenodex_oracle.py",
    "budget": "zenodex_oracle_budget.py",
    "reporter-lifecycle": "zenodex_oracle_reporter_lifecycle.py",
    "signed-report": "zenodex_oracle_signed_report.py",
    "report-admission": "zenodex_oracle_report_admission.py",
    "median3": "zenodex_oracle_median3.py",
    "admitted-median3": "zenodex_oracle_admitted_median3.py",
    "aggregate-read": "zenodex_oracle_aggregate_read.py",
    "aggregate-adapter": "zenodex_oracle_aggregate_adapter.py",
    "feed": "zenodex_oracle_feed_registry.py",
    "source-diversity": "zenodex_oracle_source_diversity.py",
    "query-policy": "zenodex_oracle_query_policy.py",
    "adapter": "zenodex_oracle_adapter.py",
    "consumer-profiles": "zenodex_oracle_consumer_profiles.py",
    "economic-security": "zenodex_oracle_economic_security.py",
}

ALIASES: dict[str, str] = {
    "feed-registry": "feed",
    "reports": "signed-report",
    "lifecycle": "reporter-lifecycle",
    "admission": "report-admission",
    "source": "source-diversity",
    "profiles": "consumer-profiles",
    "economic": "economic-security",
}

CHAOS_SURFACES: dict[str, str] = {
    "receipt": "zenodex_oracle_chaos.py",
    "budget": "zenodex_oracle_budget_chaos.py",
    "reporter-lifecycle": "zenodex_oracle_reporter_lifecycle_chaos.py",
    "signed-report": "zenodex_oracle_signed_report_chaos.py",
    "report-admission": "zenodex_oracle_report_admission_chaos.py",
    "median3": "zenodex_oracle_median3_chaos.py",
    "admitted-median3": "zenodex_oracle_admitted_median3_chaos.py",
    "aggregate-read": "zenodex_oracle_aggregate_read_chaos.py",
    "aggregate-adapter": "zenodex_oracle_aggregate_adapter_chaos.py",
    "feed": "zenodex_oracle_feed_registry_chaos.py",
    "source-diversity": "zenodex_oracle_source_diversity_chaos.py",
    "query-policy": "zenodex_oracle_query_policy_chaos.py",
    "adapter": "zenodex_oracle_adapter_chaos.py",
    "consumer-profiles": "zenodex_oracle_consumer_profiles_chaos.py",
    "economic-security": "zenodex_oracle_economic_security_chaos.py",
}


def _resolve_surface(name: str, *, chaos: bool = False) -> str:
    resolved = ALIASES.get(name, name)
    known = CHAOS_SURFACES if chaos else SURFACES
    if resolved not in known:
        choices = ", ".join(sorted(known))
        raise SystemExit(f"unknown Oracle surface {name!r}; expected one of: {choices}")
    return resolved


def _script_path(script: str) -> Path:
    path = TOOLS / script
    if not path.is_file():
        raise SystemExit(f"missing Oracle tool: {path}")
    return path


def _run_script(script: str, args: list[str]) -> int:
    path = _script_path(script)
    proc = subprocess.run(
        [sys.executable, str(path), *args],
        cwd=REPO,
        check=False,
    )
    return int(proc.returncode)


def _run_script_json(script: str, args: list[str]) -> tuple[int, dict[str, Any] | None, str]:
    path = _script_path(script)
    proc = subprocess.run(
        [sys.executable, str(path), *args],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        return int(proc.returncode), None, proc.stderr or proc.stdout
    try:
        obj = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return 3, None, f"{script} returned non-json output: {exc}"
    if not isinstance(obj, dict):
        return 3, None, f"{script} returned non-object JSON"
    return 0, obj, ""


def cmd_list(_args: argparse.Namespace) -> int:
    obj = {
        "schema": "zenodex.oracle.cli_surface_list.v1",
        "surfaces": sorted(SURFACES),
        "aliases": dict(sorted(ALIASES.items())),
        "chaos_surfaces": sorted(CHAOS_SURFACES),
    }
    sys.stdout.write(json.dumps(obj, indent=2, sort_keys=True) + "\n")
    return 0


def cmd_doctor(_args: argparse.Namespace) -> int:
    missing = []
    for script in sorted(set(SURFACES.values()) | set(CHAOS_SURFACES.values())):
        if not (TOOLS / script).is_file():
            missing.append(script)
    obj = {
        "schema": "zenodex.oracle.cli_doctor.v1",
        "ok": not missing,
        "surface_count": len(SURFACES),
        "chaos_surface_count": len(CHAOS_SURFACES),
        "missing_scripts": missing,
    }
    sys.stdout.write(json.dumps(obj, indent=2, sort_keys=True) + "\n")
    return 0 if not missing else 2


def cmd_sample(args: argparse.Namespace) -> int:
    surface = _resolve_surface(args.surface)
    return _run_script(SURFACES[surface], ["sample", *args.args])


def cmd_verify(args: argparse.Namespace) -> int:
    surface = _resolve_surface(args.surface)
    return _run_script(SURFACES[surface], ["verify", *args.args])


def cmd_chaos(args: argparse.Namespace) -> int:
    if args.surface != "all":
        surface = _resolve_surface(args.surface, chaos=True)
        return _run_script(CHAOS_SURFACES[surface], args.args)

    results: list[dict[str, Any]] = []
    ok = True
    for surface, script in sorted(CHAOS_SURFACES.items()):
        code, obj, err = _run_script_json(script, args.args)
        surface_ok = code == 0 and obj is not None and obj.get("ok") is True
        ok = ok and surface_ok
        results.append(
            {
                "surface": surface,
                "script": script,
                "ok": surface_ok,
                "returncode": code,
                "case_count": None if obj is None else obj.get("case_count"),
                "rejected_case_count": None if obj is None else obj.get("rejected_case_count"),
                "failed_case_count": None if obj is None else obj.get("failed_case_count"),
                "error": err,
            }
        )
    receipt = {
        "schema": "zenodex.oracle.cli_chaos_all.v1",
        "ok": ok,
        "surface_count": len(results),
        "case_count": sum(int(item["case_count"] or 0) for item in results),
        "rejected_case_count": sum(int(item["rejected_case_count"] or 0) for item in results),
        "failed_case_count": sum(int(item["failed_case_count"] or 0) for item in results),
        "results": results,
    }
    sys.stdout.write(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return 0 if ok else 2


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_cmd = subparsers.add_parser("list", help="list available Oracle verifier surfaces")
    list_cmd.set_defaults(func=cmd_list)

    doctor = subparsers.add_parser("doctor", help="check local Oracle CLI tool availability")
    doctor.set_defaults(func=cmd_doctor)

    sample = subparsers.add_parser("sample", help="emit a sample artifact for a verifier surface")
    sample.add_argument("surface", help="surface name, for example feed or signed-report")
    sample.add_argument("args", nargs=argparse.REMAINDER, help="arguments forwarded to the surface sample command")
    sample.set_defaults(func=cmd_sample)

    verify = subparsers.add_parser("verify", help="verify an artifact for a verifier surface")
    verify.add_argument("surface", help="surface name, for example feed or signed-report")
    verify.add_argument("args", nargs=argparse.REMAINDER, help="arguments forwarded to the surface verify command")
    verify.set_defaults(func=cmd_verify)

    chaos = subparsers.add_parser("chaos", help="run a chaos replay for one surface or all surfaces")
    chaos.add_argument("surface", help="surface name or all")
    chaos.add_argument("args", nargs=argparse.REMAINDER, help="arguments forwarded to the chaos command")
    chaos.set_defaults(func=cmd_chaos)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
