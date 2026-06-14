#!/usr/bin/env python3
"""Run `tools/prod_gate.sh` and archive a release-gate report."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_zenodex_production_readiness import (  # noqa: E402
    DEFAULT_RELEASE_GATE_REPORT,
    RELEASE_GATE_REPORT_SCHEMA,
    REQUIRED_RELEASE_GATE_CHECKS,
)

STAGE_MARKERS = {
    "container_hardening": "[gate] checking container hardening artifacts",
    "kernel_assurance": "[gate] kernel assurance OK",
    "python_tests": "[gate] running pytest",
    "ui_audit": "[gate] npm audit OK",
    "production_image_build": "[gate] building production image",
    "trivy_scan": "[gate] trivy OK",
}


def run_prod_gate_report(
    *,
    out_path: Path = DEFAULT_RELEASE_GATE_REPORT,
    gate_script: Path = ROOT / "tools" / "prod_gate.sh",
    timeout_sec: int = 7200,
    allow_dirty: bool = False,
) -> dict[str, Any]:
    """Run the release gate and write the report consumed by readiness checks."""
    out_path = out_path.resolve()
    gate_script = gate_script.resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    stdout_path = out_path.parent / "prod_gate_stdout.log"
    stderr_path = out_path.parent / "prod_gate_stderr.log"

    command_argv = ["bash", _display_path(gate_script)]
    run_argv = ["bash", str(gate_script)]
    started_at = _utc_now()
    start_ns = time.monotonic_ns()
    git_dirty_before = _git_dirty()
    commit_sha = _git_head()
    timed_out = False
    returncode: int | None

    with stdout_path.open("w", encoding="utf-8") as stdout_file, stderr_path.open(
        "w",
        encoding="utf-8",
    ) as stderr_file:
        try:
            proc = subprocess.run(
                run_argv,
                cwd=ROOT,
                check=False,
                stdout=stdout_file,
                stderr=stderr_file,
                text=True,
                timeout=timeout_sec,
            )
            returncode = proc.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
            returncode = None

    completed_at = _utc_now()
    duration_ms = (time.monotonic_ns() - start_ns) // 1_000_000
    stdout = stdout_path.read_text(encoding="utf-8", errors="replace")
    stderr = stderr_path.read_text(encoding="utf-8", errors="replace")
    check_results = _check_results(stdout=stdout, stderr=stderr, returncode=returncode)
    incomplete_reasons = _incomplete_reasons(
        returncode=returncode,
        timed_out=timed_out,
        git_dirty_before=git_dirty_before,
        allow_dirty=allow_dirty,
        check_results=check_results,
    )
    ok = not incomplete_reasons
    report = {
        "schema": RELEASE_GATE_REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "command": " ".join(command_argv),
        "command_argv": command_argv,
        "commit_sha": commit_sha,
        "git_dirty_before": git_dirty_before,
        "allow_dirty": allow_dirty,
        "started_at": started_at,
        "completed_at": completed_at,
        "duration_ms": duration_ms,
        "returncode": returncode,
        "timed_out": timed_out,
        "gate_script": _display_path(gate_script),
        "prod_gate_sha256": _sha256_file(gate_script),
        "producer": "tools/run_prod_gate_report.py",
        "producer_sha256": _sha256_file(Path(__file__).resolve()),
        "stdout_path": _display_path(stdout_path),
        "stderr_path": _display_path(stderr_path),
        "stdout_sha256": _sha256_file(stdout_path),
        "stderr_sha256": _sha256_file(stderr_path),
        "check_results": check_results,
        "incomplete_reasons": incomplete_reasons,
        "stdout_tail": _tail(stdout),
        "stderr_tail": _tail(stderr),
    }
    out_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def _check_results(*, stdout: str, stderr: str, returncode: int | None) -> dict[str, dict[str, Any]]:
    combined = stdout + "\n" + stderr
    results: dict[str, dict[str, Any]] = {}
    for check_id in REQUIRED_RELEASE_GATE_CHECKS:
        marker = STAGE_MARKERS[check_id]
        marker_seen = marker in combined
        ok = marker_seen
        results[check_id] = {
            "ok": ok,
            "status": "accepted" if ok else "rejected",
            "marker": marker,
            "marker_seen": marker_seen,
            "gate_returncode_ok": returncode == 0,
        }
    return results


def _incomplete_reasons(
    *,
    returncode: int | None,
    timed_out: bool,
    git_dirty_before: bool,
    allow_dirty: bool,
    check_results: dict[str, dict[str, Any]],
) -> list[str]:
    reasons: list[str] = []
    if timed_out:
        reasons.append("prod_gate_timed_out")
    if returncode != 0:
        reasons.append(f"prod_gate_returncode:{returncode}")
    if git_dirty_before and not allow_dirty:
        reasons.append("git_worktree_dirty_before_run")
    missing = sorted(check_id for check_id, result in check_results.items() if result.get("ok") is not True)
    if missing:
        reasons.append("release_gate_checks_not_accepted:" + ",".join(missing))
    return reasons


def _git_head() -> str | None:
    proc = _git("rev-parse", "HEAD")
    if proc.returncode != 0:
        return None
    head = proc.stdout.strip()
    return head or None


def _git_dirty() -> bool:
    proc = _git("status", "--short")
    return proc.returncode != 0 or bool(proc.stdout.strip())


def _git(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=10,
    )


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _display_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def _utc_now() -> str:
    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _tail(text: str, *, limit: int = 4000) -> str:
    return text[-limit:] if len(text) > limit else text


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=DEFAULT_RELEASE_GATE_REPORT)
    parser.add_argument("--gate-script", type=Path, default=ROOT / "tools" / "prod_gate.sh")
    parser.add_argument("--timeout-sec", type=int, default=7200)
    parser.add_argument(
        "--allow-dirty",
        action="store_true",
        help="Permit a dirty worktree in the generated report. Readiness checks still reject dirty reports.",
    )
    args = parser.parse_args(argv)

    report = run_prod_gate_report(
        out_path=args.out,
        gate_script=args.gate_script,
        timeout_sec=args.timeout_sec,
        allow_dirty=args.allow_dirty,
    )
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
