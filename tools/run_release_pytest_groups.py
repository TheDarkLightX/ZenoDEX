#!/usr/bin/env python3
"""Run the production pytest suite in deterministic groups.

The production gate still requires every discovered ``test*.py`` file to pass.
Grouping gives the release report a durable checkpoint after each batch, so a
long or interrupted gate leaves evidence about the exact group in progress.
"""

from __future__ import annotations

import argparse
import ast
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
    targets: tuple[str, ...]
    test_files: tuple[Path, ...]


@dataclass(frozen=True)
class ResumePrefix:
    groups: tuple[dict[str, Any], ...]
    source_report: str | None
    rejected_reasons: tuple[str, ...]


@dataclass(frozen=True)
class ResumeContext:
    report_path: Path
    log_dir: Path
    groups: tuple[PytestGroup, ...]
    tests_root: Path
    max_files_per_group: int
    formal_max_files_per_group: int
    commit_sha: str | None
    git_dirty_before: bool


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
        groups.extend(_group_test_files("root_test_files", root_files, max_files_per_group))

    for child in sorted(path for path in tests_root.iterdir() if path.is_dir()):
        if child.name == "__pycache__":
            continue
        test_files = tuple(sorted(child.rglob("test*.py")))
        if not test_files:
            continue
        group_size = formal_max_files_per_group if child.name == "formal" else max_files_per_group
        groups.extend(_group_test_files(f"dir_{child.name}", test_files, group_size))

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
    resume: bool = False,
    runner: Runner | None = None,
) -> dict[str, Any]:
    report_path = report_path.resolve()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    log_dir = report_path.with_suffix("")
    runner = runner or _run_command
    groups = discover_pytest_groups(
        tests_root,
        max_files_per_group=max_files_per_group,
        formal_max_files_per_group=formal_max_files_per_group,
    )
    commit_sha = _git_head()
    git_dirty_before = _git_dirty()
    resume_context = ResumeContext(
        report_path=report_path,
        log_dir=log_dir,
        groups=groups,
        tests_root=tests_root,
        max_files_per_group=max_files_per_group,
        formal_max_files_per_group=formal_max_files_per_group,
        commit_sha=commit_sha,
        git_dirty_before=git_dirty_before,
    )
    resume_prefix = _load_resume_prefix(
        context=resume_context,
        resume_requested=resume,
    )
    if not resume_prefix.groups:
        _reset_log_dir(log_dir)
    else:
        log_dir.mkdir(parents=True, exist_ok=True)

    started_at = _utc_now()
    start_ns = time.monotonic_ns()
    report = _new_running_report(
        context=resume_context,
        started_at=started_at,
        resume_requested=resume,
        resume_prefix=resume_prefix,
    )
    _write_report(report_path, report)

    for resumed_group in resume_prefix.groups:
        print(f"[gate][pytest] {resumed_group['group_id']} OK (resumed)", flush=True)

    for group in groups[len(resume_prefix.groups) :]:
        group_report = _run_one_group(
            group=group,
            log_dir=log_dir,
            runner=runner,
            timeout_sec_per_group=timeout_sec_per_group,
        )
        report["groups"].append(group_report)
        if group_report["ok"]:
            suffix = " (skip-only)" if group_report["skip_only"] else ""
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


def _new_running_report(
    *,
    context: ResumeContext,
    started_at: str,
    resume_requested: bool,
    resume_prefix: ResumePrefix,
) -> dict[str, Any]:
    return {
        "schema": "zenodex.release_pytest_groups.v1",
        "ok": False,
        "status": "running",
        "commit_sha": context.commit_sha,
        "git_dirty_before": context.git_dirty_before,
        "started_at": started_at,
        "completed_at": None,
        "duration_ms": None,
        "tests_root": _rel(context.tests_root),
        "max_files_per_group": context.max_files_per_group,
        "formal_max_files_per_group": context.formal_max_files_per_group,
        "group_count": len(context.groups),
        "all_test_file_count": _unique_test_file_count(context.groups),
        "log_dir": _rel(context.log_dir),
        "resume_requested": resume_requested,
        "resume_source_report": resume_prefix.source_report,
        "resumed_group_count": len(resume_prefix.groups),
        "resume_rejected_reasons": list(resume_prefix.rejected_reasons),
        "groups": list(resume_prefix.groups),
        "incomplete_reasons": [],
    }


def _run_one_group(
    *,
    group: PytestGroup,
    log_dir: Path,
    runner: Runner,
    timeout_sec_per_group: int | None,
) -> dict[str, Any]:
    stdout_path = log_dir / f"{group.group_id}.stdout.log"
    stderr_path = log_dir / f"{group.group_id}.stderr.log"
    argv = [
        sys.executable,
        "-m",
        "pytest",
        "-q",
        *group.targets,
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
    return {
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
        "targets": list(group.targets),
        "stdout_path": _rel(stdout_path),
        "stderr_path": _rel(stderr_path),
        "stdout_tail": _tail(stdout_path),
        "stderr_tail": _tail(stderr_path),
        "resumed_from_previous_report": False,
    }


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


def _load_resume_prefix(
    *,
    context: ResumeContext,
    resume_requested: bool,
) -> ResumePrefix:
    """Return a safe accepted prefix from a previous current-commit report.

    A release report may only reuse prior group evidence when the source code,
    grouping configuration, group identity, accepted verdicts, and referenced log
    files all still match. Any mismatch falls back to a fresh run.
    """
    if not resume_requested:
        return ResumePrefix(groups=(), source_report=None, rejected_reasons=())
    if context.git_dirty_before:
        return ResumePrefix(
            groups=(),
            source_report=None,
            rejected_reasons=("resume_current_worktree_dirty",),
        )
    if not context.report_path.exists():
        return ResumePrefix(
            groups=(),
            source_report=None,
            rejected_reasons=("resume_report_missing",),
        )

    try:
        previous = json.loads(context.report_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ResumePrefix(
            groups=(),
            source_report=None,
            rejected_reasons=("resume_report_unreadable",),
        )

    rejection = _resume_report_rejection_reason(
        previous=previous,
        context=context,
    )
    if rejection is not None:
        return ResumePrefix(groups=(), source_report=None, rejected_reasons=(rejection,))

    prefix: list[dict[str, Any]] = []
    for index, current_group in enumerate(context.groups):
        previous_groups = previous.get("groups")
        if not isinstance(previous_groups, list) or index >= len(previous_groups):
            break
        previous_group = previous_groups[index]
        if not isinstance(previous_group, dict):
            return ResumePrefix(
                groups=(),
                source_report=None,
                rejected_reasons=("resume_group_entry_invalid",),
            )
        rejection = _resume_group_rejection_reason(
            previous_group=previous_group,
            current_group=current_group,
            log_dir=context.log_dir,
        )
        if rejection == "resume_group_not_accepted":
            break
        if rejection is not None:
            return ResumePrefix(groups=(), source_report=None, rejected_reasons=(rejection,))
        resumed_group = dict(previous_group)
        resumed_group["resumed_from_previous_report"] = True
        prefix.append(resumed_group)

    return ResumePrefix(
        groups=tuple(prefix),
        source_report=_rel(context.report_path),
        rejected_reasons=(),
    )


def _resume_report_rejection_reason(
    *,
    previous: dict[str, Any],
    context: ResumeContext,
) -> str | None:
    if previous.get("schema") != "zenodex.release_pytest_groups.v1":
        return "resume_schema_mismatch"
    if previous.get("status") not in {"running", "accepted", "rejected"}:
        return "resume_status_not_resumable"
    if previous.get("commit_sha") != context.commit_sha:
        return "resume_commit_mismatch"
    if previous.get("git_dirty_before") is not False:
        return "resume_previous_worktree_dirty"
    if previous.get("tests_root") != _rel(context.tests_root):
        return "resume_tests_root_mismatch"
    if previous.get("max_files_per_group") != context.max_files_per_group:
        return "resume_max_files_per_group_mismatch"
    if previous.get("formal_max_files_per_group") != context.formal_max_files_per_group:
        return "resume_formal_max_files_per_group_mismatch"
    if previous.get("group_count") != len(context.groups):
        return "resume_group_count_mismatch"
    all_test_file_count = _unique_test_file_count(context.groups)
    if previous.get("all_test_file_count") != all_test_file_count:
        return "resume_test_file_count_mismatch"
    if previous.get("log_dir") != _rel(context.log_dir):
        return "resume_log_dir_mismatch"
    if not isinstance(previous.get("groups"), list):
        return "resume_groups_not_list"
    return None


def _resume_group_rejection_reason(
    *,
    previous_group: dict[str, Any],
    current_group: PytestGroup,
    log_dir: Path,
) -> str | None:
    expected_stdout = log_dir / f"{current_group.group_id}.stdout.log"
    expected_stderr = log_dir / f"{current_group.group_id}.stderr.log"
    if previous_group.get("group_id") != current_group.group_id:
        return "resume_group_id_mismatch"
    if previous_group.get("target_count") != len(current_group.targets):
        return "resume_group_target_count_mismatch"
    if previous_group.get("test_file_count") != len(current_group.test_files):
        return "resume_group_test_file_count_mismatch"
    if previous_group.get("targets") != list(current_group.targets):
        return "resume_group_targets_mismatch"
    if previous_group.get("stdout_path") != _rel(expected_stdout):
        return "resume_group_stdout_path_mismatch"
    if previous_group.get("stderr_path") != _rel(expected_stderr):
        return "resume_group_stderr_path_mismatch"
    if not expected_stdout.exists() or not expected_stderr.exists():
        return "resume_group_log_missing"
    if previous_group.get("ok") is not True or previous_group.get("status") != "accepted":
        return "resume_group_not_accepted"
    if previous_group.get("timed_out") is True:
        return "resume_group_timed_out"
    if previous_group.get("returncode") != 0 and previous_group.get("skip_only") is not True:
        return "resume_group_returncode_not_accepted"
    return None


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


def _group_test_files(
    base_id: str,
    test_files: tuple[Path, ...],
    max_files_per_group: int,
) -> tuple[PytestGroup, ...]:
    normal_files = tuple(path for path in test_files if not _has_slow_marker(path))
    slow_files = tuple(path for path in test_files if _has_slow_marker(path))
    groups = list(_chunked_groups(base_id, normal_files, max_files_per_group)) if normal_files else []
    for path in slow_files:
        groups.extend(_slow_nodeid_groups(base_id=base_id, path=path))
    return tuple(groups)


def _unique_test_file_count(groups: tuple[PytestGroup, ...]) -> int:
    return len({path.resolve() for group in groups for path in group.test_files})


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
                targets=tuple(_rel(path) for path in chunks[0]),
                test_files=chunks[0],
            ),
        )
    return tuple(
        PytestGroup(
            group_id=f"{base_id}_{index:03d}",
            targets=tuple(_rel(path) for path in chunk),
            test_files=chunk,
        )
        for index, chunk in enumerate(chunks, start=1)
    )


def _has_slow_marker(path: Path) -> bool:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return False
    return "@pytest.mark.slow" in text or "@mark.slow" in text


def _slow_nodeid_groups(*, base_id: str, path: Path) -> tuple[PytestGroup, ...]:
    test_names = _top_level_test_function_names(path)
    if not test_names:
        return (
            PytestGroup(
                group_id=f"{base_id}_{path.stem}_slow",
                targets=(_rel(path),),
                test_files=(path,),
            ),
        )
    file_target = _rel(path)
    return tuple(
        PytestGroup(
            group_id=f"{base_id}_{path.stem}_slow_{index:03d}",
            targets=(f"{file_target}::{test_name}",),
            test_files=(path,),
        )
        for index, test_name in enumerate(test_names, start=1)
    )


def _top_level_test_function_names(path: Path) -> tuple[str, ...]:
    try:
        module = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    except (OSError, SyntaxError):
        return ()
    return tuple(
        node.name
        for node in module.body
        if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef) and node.name.startswith("test_")
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
    parser.add_argument(
        "--resume",
        action="store_true",
        help="Reuse accepted groups from a current-commit report when the group identity and logs match.",
    )
    args = parser.parse_args(argv)

    report = run_pytest_groups(
        report_path=args.out,
        tests_root=args.tests_root,
        max_files_per_group=args.max_files_per_group,
        formal_max_files_per_group=args.formal_max_files_per_group,
        timeout_sec_per_group=args.timeout_sec_per_group,
        resume=args.resume,
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
