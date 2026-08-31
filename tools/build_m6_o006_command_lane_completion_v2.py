#!/usr/bin/env python3
"""Build O006 V2 from an exact direct-child Stage-A source commit."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import selectors
import subprocess
import sys
import time
from enum import Enum
from pathlib import Path
from typing import Final, NoReturn

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

try:
    from tools.build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _atomic_replace_regular_file_v1,
        _git_binary_v1,
        _git_environment_v1,
        _git_head_v1,
        _git_tree_entry_v1,
        _git_tree_v1,
        _kill_and_wait_v1,
        _read_bounded_regular_file_v1,
        _require_inert_path_v1,
        _run_git_v1,
    )
    from tools.m6_o006_command_lane_completion_v2 import (
        ARTIFACT_PATH_V2,
        BASE_COMMIT_V2,
        BASE_SOURCE_SPECS_V2,
        BASE_TREE_V2,
        MAX_ARTIFACT_BYTES_V2,
        MAX_SOURCE_BYTES_V2,
        STAGE_A_SOURCE_PATHS_V2,
        CommandLaneCompletionRejectV2,
        SourcePinV2,
        StageASnapshotV2,
        build_command_lane_completion_artifact_v2,
    )
except ModuleNotFoundError:
    from build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _atomic_replace_regular_file_v1,
        _git_binary_v1,
        _git_environment_v1,
        _git_head_v1,
        _git_tree_entry_v1,
        _git_tree_v1,
        _kill_and_wait_v1,
        _read_bounded_regular_file_v1,
        _require_inert_path_v1,
        _run_git_v1,
    )
    from m6_o006_command_lane_completion_v2 import (  # type: ignore[no-redef]
        ARTIFACT_PATH_V2,
        BASE_COMMIT_V2,
        BASE_SOURCE_SPECS_V2,
        BASE_TREE_V2,
        MAX_ARTIFACT_BYTES_V2,
        MAX_SOURCE_BYTES_V2,
        STAGE_A_SOURCE_PATHS_V2,
        CommandLaneCompletionRejectV2,
        SourcePinV2,
        StageASnapshotV2,
        build_command_lane_completion_artifact_v2,
    )

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
JSON_OUTPUT: Final = Path(ARTIFACT_PATH_V2)
_GIT_ID_RE: Final = re.compile(r"^[0-9a-f]{40}$")
_GIT_BLOB_TIMEOUT_SECONDS_V2: Final = 5.0
_GIT_BLOB_READ_CHUNK_BYTES_V2: Final = 65_536
_GIT_BLOB_STDERR_MAX_BYTES_V2: Final = 4_096
_GIT_CONFIG_SCOPES_V2: Final = frozenset({"command", "local", "worktree"})
_TRUE_CONFIG_VALUES_V2: Final = frozenset({"true", "yes", "on", "1"})
_FALSE_CONFIG_VALUES_V2: Final = frozenset({"false", "no", "off", "0"})


class SourceBindingModeV2(Enum):
    GIT_AND_WORKTREE = "GIT_AND_WORKTREE"
    GIT_ONLY = "GIT_ONLY"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise CommandLaneCompletionRejectV2(code, path, detail)


def _require_git_id(value: object, path: str, code: str) -> str:
    if type(value) is not str or _GIT_ID_RE.fullmatch(value) is None:
        _reject(code, path, "must be one lowercase forty-hex Git ID")
    return value


def _non_promisor(root: Path) -> None:
    status, stdout, stderr = _run_git_v1(
        root,
        (
            "config",
            "--includes",
            "--show-scope",
            "--get-regexp",
            r"^(extensions\.partialclone|remote\..*\.promisor)$",
        ),
        allowed_statuses=frozenset({0, 1}),
    )
    if stderr:
        _reject("GIT_CONFIG", "Git config", "unexpected sanitized Git config stderr")
    if status == 1:
        if stdout:
            _reject("GIT_CONFIG", "Git config", "missing config emitted stdout")
        return
    for row in stdout.splitlines():
        fields = row.split(maxsplit=2)
        if len(fields) != 3:
            _reject("GIT_CONFIG", "Git config", "malformed scoped config row")
        scope, key, raw_value = fields
        if scope not in _GIT_CONFIG_SCOPES_V2:
            _reject("GIT_CONFIG", key, "unexpected config scope")
        if key == "extensions.partialclone":
            _reject("GIT_PROMISOR_REPOSITORY", key, "partial clone is rejected")
        if re.fullmatch(r"remote\..+\.promisor", key) is None:
            _reject("GIT_CONFIG", key, "unexpected matched promisor key")
        value = raw_value.casefold()
        if value in _TRUE_CONFIG_VALUES_V2:
            _reject("GIT_PROMISOR_REPOSITORY", key, "promisor remote is rejected")
        if value not in _FALSE_CONFIG_VALUES_V2:
            _reject("GIT_CONFIG", key, "promisor value must be an exact boolean")


def _start_git_blob_process(root: Path, object_id: str, path: str) -> subprocess.Popen[bytes]:
    environment = _git_environment_v1()
    environment["GIT_NO_LAZY_FETCH"] = "1"
    argv = (
        _git_binary_v1(),
        "-c",
        "core.hooksPath=/dev/null",
        "-C",
        os.path.abspath(os.fspath(root)),
        "cat-file",
        "blob",
        object_id,
    )
    try:
        process = subprocess.Popen(
            argv,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            start_new_session=True,
        )
    except OSError as exc:
        _reject("GIT_BLOB_EXEC", path, f"{type(exc).__name__}; errno={exc.errno}")
    if process.stdout is None or process.stderr is None:
        _kill_and_wait_v1(process)
        _reject("GIT_BLOB_PIPE", path, "subprocess pipes were not created")
    return process


def _close_blob_reader(selector: selectors.BaseSelector, process: subprocess.Popen[bytes]) -> None:
    for resource in (selector, process.stdout, process.stderr):
        if resource is None:
            continue
        try:
            resource.close()
        except OSError:
            pass


def _read_git_blob(root: Path, blob: str, maximum: int, path: str) -> bytes:
    object_id = _require_git_id(blob, path, "GIT_BLOB_ID")
    if type(maximum) is not int or maximum < 0:
        _reject("GIT_BLOB_LIMIT", path, "maximum must be a nonnegative exact integer")
    process = _start_git_blob_process(root, object_id, path)
    if process.stdout is None or process.stderr is None:
        _kill_and_wait_v1(process)
        _reject("GIT_BLOB_PIPE", path, "subprocess pipes were not created")
    stdout_pipe = process.stdout
    stderr_pipe = process.stderr
    output = {"stdout": bytearray(), "stderr": bytearray()}
    selector = selectors.DefaultSelector()
    deadline = time.monotonic() + _GIT_BLOB_TIMEOUT_SECONDS_V2
    try:
        selector.register(stdout_pipe, selectors.EVENT_READ, "stdout")
        selector.register(stderr_pipe, selectors.EVENT_READ, "stderr")
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                _kill_and_wait_v1(process)
                _reject("GIT_BLOB_TIMEOUT", path, "Git blob read exceeded time ceiling")
            for key, _events in selector.select(timeout=min(0.05, remaining)):
                try:
                    chunk = os.read(key.fd, _GIT_BLOB_READ_CHUNK_BYTES_V2)
                except BlockingIOError:
                    continue
                except OSError as exc:
                    _kill_and_wait_v1(process)
                    _reject("GIT_BLOB_IO", path, f"{type(exc).__name__}; errno={exc.errno}")
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                stream = str(key.data)
                limit = maximum if stream == "stdout" else _GIT_BLOB_STDERR_MAX_BYTES_V2
                if len(output[stream]) + len(chunk) > limit:
                    _kill_and_wait_v1(process)
                    code = (
                        "GIT_BLOB_OUTPUT_LIMIT" if stream == "stdout" else "GIT_BLOB_STDERR_LIMIT"
                    )
                    _reject(code, path, "Git blob stream exceeded byte ceiling")
                output[stream].extend(chunk)
        try:
            status = process.wait(timeout=max(0.01, deadline - time.monotonic()))
        except subprocess.TimeoutExpired:
            _kill_and_wait_v1(process)
            _reject("GIT_BLOB_TIMEOUT", path, "Git blob read exceeded time ceiling")
    except CommandLaneCompletionRejectV2:
        _kill_and_wait_v1(process)
        raise
    except OSError as exc:
        _kill_and_wait_v1(process)
        _reject("GIT_BLOB_IO", path, f"{type(exc).__name__}; errno={exc.errno}")
    finally:
        _close_blob_reader(selector, process)
    if status != 0:
        _reject("GIT_BLOB_EXIT", path, f"Git cat-file exited with status {status}")
    if output["stderr"]:
        _reject("GIT_BLOB_STDERR", path, "Git blob read emitted stderr")
    return bytes(output["stdout"])


def _sole_parent(root: Path, commit: str) -> str:
    _status, stdout, stderr = _run_git_v1(root, ("rev-list", "--parents", "-n", "1", commit))
    parts = stdout.strip().split()
    if stderr or len(parts) != 2 or parts[0] != commit:
        _reject("STAGE_A_PARENT", commit, "Stage A must have exactly one parent")
    return _require_git_id(parts[1], commit, "STAGE_A_PARENT")


def _stage_a_delta(root: Path, stage_a: str) -> tuple[tuple[str, str], ...]:
    _status, stdout, stderr = _run_git_v1(
        root,
        (
            "diff-tree",
            "--no-commit-id",
            "--name-status",
            "--no-renames",
            "-r",
            "-z",
            stage_a,
        ),
    )
    if stderr:
        _reject("STAGE_A_DELTA", stage_a, "Git delta query emitted stderr")
    parts = stdout.split("\0")
    if parts and parts[-1] == "":
        parts.pop()
    if len(parts) % 2 != 0:
        _reject("STAGE_A_DELTA", stage_a, "malformed name-status output")
    rows = tuple((parts[index], parts[index + 1]) for index in range(0, len(parts), 2))
    return tuple(sorted(rows, key=lambda row: (row[1], row[0])))


def _require_absent(root: Path, commit: str, path: str, code: str) -> None:
    _status, stdout, stderr = _run_git_v1(
        root, ("ls-tree", "-z", "--full-tree", commit, "--", path)
    )
    if stdout or stderr:
        _reject(code, path, "path must be absent")


def _entry(root: Path, commit: str, path: str) -> tuple[str, str]:
    entry_path, mode, object_type, blob = _git_tree_entry_v1(root, commit, path)
    if entry_path != path or mode != "100644" or object_type != "blob":
        _reject("SOURCE_GIT_ENTRY", path, "must be an exact regular Git blob")
    return blob, mode


def _pin_from_blob(root: Path, commit: str, path: str) -> tuple[SourcePinV2, bytes]:
    blob, _mode = _entry(root, commit, path)
    raw = _read_git_blob(root, blob, MAX_SOURCE_BYTES_V2, path)
    return (
        SourcePinV2(
            path=path,
            git_blob_sha=blob,
            sha256=hashlib.sha256(raw).hexdigest(),
            size_bytes=len(raw),
        ),
        raw,
    )


def _base_pin(
    root: Path, stage_a: str, spec: tuple[str, str, str, int]
) -> tuple[SourcePinV2, bytes]:
    path, expected_blob, expected_sha, expected_size = spec
    base_blob, _base_mode = _entry(root, BASE_COMMIT_V2, path)
    stage_blob, _stage_mode = _entry(root, stage_a, path)
    if base_blob != expected_blob or stage_blob != expected_blob:
        _reject("BASE_SOURCE_GIT_DRIFT", path, "base or Stage-A Git blob drift")
    raw = _read_git_blob(root, stage_blob, MAX_SOURCE_BYTES_V2, path)
    pin = SourcePinV2(
        path=path,
        git_blob_sha=stage_blob,
        sha256=hashlib.sha256(raw).hexdigest(),
        size_bytes=len(raw),
    )
    if pin != SourcePinV2(path, expected_blob, expected_sha, expected_size):
        _reject("BASE_SOURCE_BYTE_DRIFT", path, "exact base bytes drift")
    return pin, raw


def _require_worktree_binding(root: Path, rows: tuple[tuple[SourcePinV2, bytes], ...]) -> None:
    for pin, expected in rows:
        actual = _read_bounded_regular_file_v1(
            root / pin.path, MAX_SOURCE_BYTES_V2, f"O006 V2 source {pin.path}"
        )
        if actual != expected:
            _reject("STAGE_A_WORKTREE_BINDING", pin.path, "working bytes differ from Stage A")


def load_stage_a_snapshot_v2(
    root: Path | str = REPO_ROOT,
    stage_a_commit: str | None = None,
    *,
    source_binding: SourceBindingModeV2 = SourceBindingModeV2.GIT_AND_WORKTREE,
) -> StageASnapshotV2:
    """Acquire an exact Stage A from Git, optionally binding working bytes."""

    if type(source_binding) is not SourceBindingModeV2:
        _reject("SOURCE_BINDING_MODE", "source_binding", "must be an exact source binding mode")
    bind_worktree = source_binding is SourceBindingModeV2.GIT_AND_WORKTREE
    inert_root = _require_inert_path_v1(root, "O006 V2 Stage-A root")
    _non_promisor(inert_root)
    captured_head = _require_git_id(_git_head_v1(inert_root), "HEAD", "GIT_HEAD")
    stage_a = (
        captured_head
        if stage_a_commit is None
        else _require_git_id(stage_a_commit, "stage_a_commit", "STAGE_A_COMMIT")
    )
    if _git_tree_v1(inert_root, BASE_COMMIT_V2) != BASE_TREE_V2:
        _reject("BASE_TREE", BASE_COMMIT_V2, "exact admitted base tree drift")
    if _sole_parent(inert_root, stage_a) != BASE_COMMIT_V2:
        _reject("BASE_NOT_DIRECT_PARENT", stage_a, "Stage A must directly follow admitted base")
    stage_a_tree = _require_git_id(
        _git_tree_v1(inert_root, stage_a), "stage_a_tree", "STAGE_A_TREE"
    )
    delta = _stage_a_delta(inert_root, stage_a)
    expected_delta = tuple(("A", path) for path in sorted(STAGE_A_SOURCE_PATHS_V2))
    if delta != expected_delta:
        _reject("STAGE_A_DELTA", stage_a, "Stage A must add only declared V2 paths")
    _require_absent(inert_root, stage_a, ARTIFACT_PATH_V2, "STAGE_A_ARTIFACT")
    for path in STAGE_A_SOURCE_PATHS_V2:
        _require_absent(inert_root, BASE_COMMIT_V2, path, "BASE_STAGE_A_SOURCE_PRESENT")

    base_rows = tuple(_base_pin(inert_root, stage_a, spec) for spec in BASE_SOURCE_SPECS_V2)
    stage_rows = tuple(
        _pin_from_blob(inert_root, stage_a, path) for path in STAGE_A_SOURCE_PATHS_V2
    )
    all_rows = base_rows + stage_rows
    if bind_worktree:
        _require_worktree_binding(inert_root, all_rows)
    rechecked_head = _require_git_id(_git_head_v1(inert_root), "HEAD", "GIT_HEAD")
    if bind_worktree:
        _require_worktree_binding(inert_root, all_rows)
    return StageASnapshotV2(
        captured_git_head=captured_head,
        rechecked_git_head=rechecked_head,
        stage_a_commit=stage_a,
        stage_a_tree=stage_a_tree,
        base_is_direct_parent=True,
        stage_a_delta=delta,
        base_source_pins=tuple(pin for pin, _raw in base_rows),
        stage_a_source_pins=tuple(pin for pin, _raw in stage_rows),
        source_bytes=tuple((pin.path, raw) for pin, raw in all_rows),
    )


def build_artifact_v2(root: Path | str = REPO_ROOT, stage_a_commit: str | None = None) -> bytes:
    return build_command_lane_completion_artifact_v2(load_stage_a_snapshot_v2(root, stage_a_commit))


def _failure_report(exc: CommandLaneCompletionRejectV2 | ShellRejectV1) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "current_applicable": False,
        "finding": {"code": exc.code, "detail": exc.detail, "path": exc.path},
        "historical_valid": False,
        "migration_authority": "NONE",
        "ok": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": "zenodex/m6-o006-command-lane-completion-build/v2",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm_gates_closed": [],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--stage-a")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        expected = build_artifact_v2(args.root, args.stage_a)
        output = args.root / JSON_OUTPUT
        if args.check:
            actual = _read_bounded_regular_file_v1(
                output, MAX_ARTIFACT_BYTES_V2, "O006 V2 artifact"
            )
            if actual != expected:
                _reject("ARTIFACT_DRIFT", str(JSON_OUTPUT), "artifact differs from Stage A")
        else:
            _atomic_replace_regular_file_v1(output, expected)
        print(
            json.dumps(
                {"artifact_sha256": hashlib.sha256(expected).hexdigest(), "ok": True},
                sort_keys=True,
            )
        )
        return 0
    except (CommandLaneCompletionRejectV2, ShellRejectV1) as exc:
        print(json.dumps(_failure_report(exc), sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
