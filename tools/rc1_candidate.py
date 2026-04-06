#!/usr/bin/env python3
"""Plan or execute the conservative RC1 candidate command set."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

try:
    from tools.rc1_readiness import MANIFEST_PATH, RC1Error, build_status_payload
except ModuleNotFoundError:  # pragma: no cover - script execution path
    from rc1_readiness import MANIFEST_PATH, RC1Error, build_status_payload


class CandidateError(RuntimeError):
    pass


def _sanitize_run_id(raw: str) -> str:
    text = re.sub(r"[^A-Za-z0-9._-]+", "-", raw.strip())
    text = text.strip("-.")
    return text or "run"


def _load_manifest() -> dict[str, Any]:
    try:
        data = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise CandidateError(f"missing RC1 scope manifest: {MANIFEST_PATH.relative_to(REPO_ROOT)}") from exc
    except json.JSONDecodeError as exc:
        raise CandidateError(f"invalid RC1 scope manifest JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise CandidateError("RC1 scope manifest must be an object")
    if data.get("schema") != "zenodex/rc1-scope-manifest/v1":
        raise CandidateError("RC1 scope manifest has unexpected schema")
    return data


def _build_steps(
    manifest: dict[str, Any],
    *,
    skip_prod_gate_ui: bool,
    skip_prod_gate_docker: bool,
) -> list[list[str]]:
    raw_steps = manifest.get("supported_commands", [])
    if not isinstance(raw_steps, list):
        raise CandidateError("supported_commands must be a list")
    steps: list[list[str]] = []
    for raw in raw_steps:
        if not isinstance(raw, list) or not raw or not all(isinstance(item, str) for item in raw):
            raise CandidateError("supported_commands entries must be non-empty string lists")
        step = [str(item) for item in raw]
        if step[:2] == ["bash", "tools/prod_gate.sh"]:
            if skip_prod_gate_ui:
                step.append("--skip-ui")
            if skip_prod_gate_docker:
                step.append("--skip-docker")
        steps.append(step)
    return steps


def _run_command(command: Sequence[str]) -> dict[str, Any]:
    started = time.monotonic()
    proc = subprocess.run(
        list(command),
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    duration = round(time.monotonic() - started, 3)
    return {
        "command": list(command),
        "ok": proc.returncode == 0,
        "returncode": proc.returncode,
        "duration_s": duration,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def _payload(
    *,
    readiness: dict[str, Any],
    steps: Sequence[Sequence[str]],
    results: Sequence[dict[str, Any]] | None,
    blocked_before_run: bool,
) -> dict[str, Any]:
    overall_ok = bool(readiness.get("overall_ok")) and not blocked_before_run
    if results is not None:
        overall_ok = overall_ok and all(bool(item.get("ok")) for item in results)
    return {
        "schema": "zenodex/rc1-candidate-report/v1",
        "readiness": readiness,
        "blocked_before_run": blocked_before_run,
        "steps": [list(step) for step in steps],
        "results": list(results) if results is not None else None,
        "overall_ok": overall_ok,
    }


def _write_report(path: str | None, payload: dict[str, Any]) -> None:
    if not path:
        return
    report_path = Path(path)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _default_report_path(*, campaign_root: str | None, timestamp_utc: str | None, run_id: str | None) -> str | None:
    if not campaign_root:
        return None
    ts = (timestamp_utc or time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())).strip()
    rid = _sanitize_run_id(run_id or "candidate")
    return str(Path(campaign_root) / f"{ts}_{rid}" / "candidate_report.json")


def _print_text_report(payload: dict[str, Any]) -> None:
    readiness = payload["readiness"]
    print("ZenoDex RC1 Candidate")
    print(f"readiness: {'READY' if readiness['overall_ok'] else 'BLOCKED'}")
    print(f"blocked_before_run: {'yes' if payload['blocked_before_run'] else 'no'}")
    print()
    print("Planned steps")
    for step in payload["steps"]:
        print("  " + " ".join(step))
    results = payload.get("results")
    if results is not None:
        print()
        print("Execution")
        for item in results:
            print(f"  [{'OK' if item['ok'] else 'FAIL'}] {' '.join(item['command'])} ({item['duration_s']}s)")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Plan or execute the conservative RC1 candidate workflow.")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    parser.add_argument("--plan", action="store_true", help="print the candidate plan without executing it")
    parser.add_argument(
        "--allow-blocked-readiness",
        action="store_true",
        help="allow execution even when rc1_readiness reports blocked",
    )
    parser.add_argument("--skip-prod-gate-ui", action="store_true", help="append --skip-ui to the production gate step")
    parser.add_argument(
        "--skip-prod-gate-docker",
        action="store_true",
        help="append --skip-docker to the production gate step",
    )
    parser.add_argument("--report-out", help="optional path to write the candidate JSON report")
    parser.add_argument(
        "--campaign-root",
        help="optional root directory for stable candidate receipt directories (writes <timestamp>_<run-id>/candidate_report.json)",
    )
    parser.add_argument("--timestamp-utc", help="optional UTC timestamp token for campaign output, e.g. 20260327T120000Z")
    parser.add_argument("--run-id", help="optional run id token for campaign output")
    args = parser.parse_args(argv)

    try:
        manifest = _load_manifest()
        readiness = build_status_payload()
    except (CandidateError, RC1Error) as exc:
        if args.format == "json":
            print(json.dumps({"ok": False, "error": str(exc)}, indent=2, sort_keys=True))
        else:
            print(f"error: {exc}")
        return 1

    steps = _build_steps(
        manifest,
        skip_prod_gate_ui=bool(args.skip_prod_gate_ui),
        skip_prod_gate_docker=bool(args.skip_prod_gate_docker),
    )
    report_out = args.report_out or _default_report_path(
        campaign_root=args.campaign_root,
        timestamp_utc=args.timestamp_utc,
        run_id=args.run_id,
    )

    blocked_before_run = bool(not readiness["overall_ok"] and not args.allow_blocked_readiness)
    if args.plan:
        payload = _payload(
            readiness=readiness,
            steps=steps,
            results=None,
            blocked_before_run=blocked_before_run,
        )
        _write_report(report_out, payload)
        if args.format == "json":
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            _print_text_report(payload)
        return 0 if not blocked_before_run else 1

    if blocked_before_run:
        payload = _payload(
            readiness=readiness,
            steps=steps,
            results=[],
            blocked_before_run=True,
        )
        _write_report(report_out, payload)
        if args.format == "json":
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            _print_text_report(payload)
        return 1

    results: list[dict[str, Any]] = []
    overall_ok = True
    for step in steps:
        result = _run_command(step)
        results.append(result)
        if not result["ok"]:
            overall_ok = False
            break

    payload = _payload(
        readiness=readiness,
        steps=steps,
        results=results,
        blocked_before_run=False,
    )
    payload["overall_ok"] = overall_ok and bool(readiness["overall_ok"])
    _write_report(report_out, payload)
    if args.format == "json":
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        _print_text_report(payload)
    return 0 if payload["overall_ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
