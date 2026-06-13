#!/usr/bin/env python3
"""Run the production pytest suite in deterministic groups.

The production gate still requires every discovered ``test*.py`` file to pass.
Grouping gives the release report a durable checkpoint after each batch, so a
long or interrupted gate leaves evidence about the exact group in progress.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_REPORT = ROOT / "runs" / "production_readiness" / "release_gate" / "pytest_groups_report.json"
DEFAULT_MAX_FILES_PER_GROUP = 10
DEFAULT_FORMAL_MAX_FILES_PER_GROUP = 1


@dataclass(frozen=True)
class PytestGroup:
    group_id: str
    targets: tuple[Path, ...]
    test_files: tuple[Path, ...]


Runner = Callable[[list[str], Path, Path, int | None], tuple[int | None, bool]]


def discover_pytest_groups(
    tests_root: Path = ROOT / "tests",
    *,
    max_files_per_group: int = DEFAULT_MAX_FILES_PER_GROUP,
    formal_max_files_per_group: int = DEFAULT_FORMAL_MAX_FILES_PER_GROUP,
) -> tuple[PytestGroup, ...]:
    tests_root = tests_root.resolve()
    if not tests_root.is_dir():
        raise FileNotFoundError(f"missing tests root: {tests_root}")
    if max_files_per_group < 1:
        raise ValueError("max_files_per_group must be positive")
    if formal_max_files_per_group < 1:
        raise ValueError("formal_max_files_per_group must be positive")

    groups: list[PytestGroup] = []
    root_files = tuple(sorted(tests_root.glob("test*.py")))
    if root_files:
        groups.extend(_chunked_groups("root_test_files", root_files, max_files_per_group))

    for child in sorted(path for path in tests_root.iterdir() if path.is_dir()):
        if child.name == "__pycache__":
            continue
        test_files = tuple(sorted(child.rglob("test*.py")))
        if not test_files:
            continue
        group_size = formal_max_files_per_group if child.name == "formal" else max_files_per_group
        groups.extend(_chunked_groups(f"dir_{child.name}", test_files, group_size))

    covered = {path.resolve() for group in groups for path in group.test_files}
    all_tests = {path.resolve() for path in tests_root.rglob("test*.py")}
    missing = sorted(all_tests - covered)
    extra = sorted(covered - all_tests)
    if missing or extra:
        raise ValueError(
            "pytest group discovery is not exact: "
            f"missing={[_rel(path) for path in missing]} extra={[_rel(path) for path in extra]}"
        )
    return tuple(groups)


def run_pytest_groups(
    *,
    report_path: Path = DEFAULT_REPORT,
    tests_root: Path = ROOT / "tests",
    max_files_per_group: int = DEFAULT_MAX_FILES_PER_GROUP,
    formal_max_files_per_group: int = DEFAULT_FORMAL_MAX_FILES_PER_GROUP,
    timeout_sec_per_group: int | None = None,
    runner: Runner | None = None,
) -> dict[str, Any]:
    report_path = report_path.resolve()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    log_dir = report_path.with_suffix("")
    _reset_log_dir(log_dir)
    runner = runner or _run_command
    groups = discover_pytest_groups(
        tests_root,
        max_files_per_group=max_files_per_group,
        formal_max_files_per_group=formal_max_files_per_group,
    )
    started_at = _utc_now()
    start_ns = time.monotonic_ns()
    report: dict[str, Any] = {
        "schema": "zenodex.release_pytest_groups.v1",
        "ok": False,
        "status": "running",
        "started_at": started_at,
        "completed_at": None,
        "duration_ms": None,
        "tests_root": _rel(tests_root),
        "max_files_per_group": max_files_per_group,
        "formal_max_files_per_group": formal_max_files_per_group,
        "group_count": len(groups),
        "all_test_file_count": sum(len(group.test_files) for group in groups),
        "log_dir": _rel(log_dir),
        "groups": [],
        "incomplete_reasons": [],
    }
    _write_report(report_path, report)

    for group in groups:
        stdout_path = log_dir / f"{group.group_id}.stdout.log"
        stderr_path = log_dir / f"{group.group_id}.stderr.log"
        argv = [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            *(_rel(target) for target in group.targets),
        ]
        group_started_at = _utc_now()
        group_start_ns = time.monotonic_ns()
        print(
            f"[gate][pytest] running {group.group_id} "
            f"({len(group.test_files)} files)",
            flush=True,
        )
        returncode, timed_out = runner(argv, stdout_path, stderr_path, timeout_sec_per_group)
        duration_ms = (time.monotonic_ns() - group_start_ns) // 1_000_000
        skip_only = _is_skip_only_pytest_exit(
            returncode=returncode,
            timed_out=timed_out,
            stdout_path=stdout_path,
            stderr_path=stderr_path,
        )
        accepted = (returncode == 0 and not timed_out) or skip_only
        group_report = {
            "group_id": group.group_id,
            "ok": accepted,
            "status": "accepted" if accepted else "rejected",
            "started_at": group_started_at,
            "completed_at": _utc_now(),
            "duration_ms": duration_ms,
            "returncode": returncode,
            "timed_out": timed_out,
            "skip_only": skip_only,
            "target_count": len(group.targets),
            "test_file_count": len(group.test_files),
            "targets": [_rel(target) for target in group.targets],
            "stdout_path": _rel(stdout_path),
            "stderr_path": _rel(stderr_path),
            "stdout_tail": _tail(stdout_path),
            "stderr_tail": _tail(stderr_path),
        }
        report["groups"].append(group_report)
        if group_report["ok"]:
            suffix = " (skip-only)" if skip_only else ""
            print(f"[gate][pytest] {group.group_id} OK{suffix}", flush=True)
            _write_report(report_path, report)
            continue

        report["status"] = "rejected"
        report["incomplete_reasons"] = [f"pytest_group_failed:{group.group_id}"]
        report["completed_at"] = _utc_now()
        report["duration_ms"] = (time.monotonic_ns() - start_ns) // 1_000_000
        _write_report(report_path, report)
        return report

    report["ok"] = True
    report["status"] = "accepted"
    report["completed_at"] = _utc_now()
    report["duration_ms"] = (time.monotonic_ns() - start_ns) // 1_000_000
    report["incomplete_reasons"] = []
    _write_report(report_path, report)
    print("[gate][pytest] all groups OK", flush=True)
    return report


def _run_command(
    argv: list[str],
    stdout_path: Path,
    stderr_path: Path,
    timeout_sec: int | None,
) -> tuple[int | None, bool]:
    with stdout_path.open("w", encoding="utf-8") as stdout_file, stderr_path.open(
        "w",
        encoding="utf-8",
    ) as stderr_file:
        try:
            proc = subprocess.run(
                argv,
                cwd=ROOT,
                check=False,
                stdout=stdout_file,
                stderr=stderr_file,
                text=True,
                timeout=timeout_sec,
            )
            return proc.returncode, False
        except subprocess.TimeoutExpired:
            return None, True


def _reset_log_dir(log_dir: Path) -> None:
    if log_dir.exists():
        for child in log_dir.iterdir():
            if child.is_dir():
                shutil.rmtree(child)
            else:
                child.unlink()
    log_dir.mkdir(parents=True, exist_ok=True)


def _is_skip_only_pytest_exit(
    *,
    returncode: int | None,
    timed_out: bool,
    stdout_path: Path,
    stderr_path: Path,
) -> bool:
    """Accept module-level optional-tool skips isolated into their own group."""
    if timed_out or returncode != 5:
        return False
    combined = (
        stdout_path.read_text(encoding="utf-8", errors="replace")
        + "\n"
        + stderr_path.read_text(encoding="utf-8", errors="replace")
    ).lower()
    if " skipped" not in combined:
        return False
    return not any(marker in combined for marker in (" failed", " error", " errors"))


def _chunked_groups(
    base_id: str,
    test_files: tuple[Path, ...],
    max_files_per_group: int,
) -> tuple[PytestGroup, ...]:
    chunks = [
        test_files[index : index + max_files_per_group]
        for index in range(0, len(test_files), max_files_per_group)
    ]
    if len(chunks) == 1:
        return (
            PytestGroup(
                group_id=base_id,
                targets=chunks[0],
                test_files=chunks[0],
            ),
        )
    return tuple(
        PytestGroup(
            group_id=f"{base_id}_{index:03d}",
            targets=chunk,
            test_files=chunk,
        )
        for index, chunk in enumerate(chunks, start=1)
    )


def _write_report(path: Path, report: dict[str, Any]) -> None:
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def _utc_now() -> str:
    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _tail(path: Path, *, limit: int = 4000) -> str:
    if not path.exists():
        return ""
    text = path.read_text(encoding="utf-8", errors="replace")
    return text[-limit:] if len(text) > limit else text


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--tests-root", type=Path, default=ROOT / "tests")
    parser.add_argument("--max-files-per-group", type=int, default=DEFAULT_MAX_FILES_PER_GROUP)
    parser.add_argument(
        "--formal-max-files-per-group",
        type=int,
        default=DEFAULT_FORMAL_MAX_FILES_PER_GROUP,
    )
    parser.add_argument("--timeout-sec-per-group", type=int, default=None)
    args = parser.parse_args(argv)

    report = run_pytest_groups(
        report_path=args.out,
        tests_root=args.tests_root,
        max_files_per_group=args.max_files_per_group,
        formal_max_files_per_group=args.formal_max_files_per_group,
        timeout_sec_per_group=args.timeout_sec_per_group,
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
