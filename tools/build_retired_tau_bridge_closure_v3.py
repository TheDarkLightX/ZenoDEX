#!/usr/bin/env python3
"""Build the source-pinned, authority-free O-003B classification certificate."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import subprocess
import sys
from pathlib import Path
from typing import Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.build_m6_normative_requirements_v1 import (  # noqa: E402
    ShellRejectV1,
    _atomic_replace_regular_file_v1,
    _git_binary_v1,
    _git_environment_v1,
    _git_head_v1,
    _git_is_ancestor_v1,
    _git_scalar_v1,
    _git_tree_entry_v1,
    _git_tree_v1,
    _read_bounded_regular_file_v1,
    _require_inert_path_v1,
)
from tools.retired_tau_bridge_closure_v3 import (  # noqa: E402
    ARTIFACT_SCHEMA_V3,
    BASELINE_COMMIT_V3,
    BASELINE_PIN_PATHS_V3,
    BASELINE_TREE_V3,
    MAX_ARTIFACT_BYTES_V3,
    MAX_DISCOVERY_PATHS_V3,
    MAX_DISCOVERY_TOTAL_BYTES_V3,
    MAX_SOURCE_BYTES_V3,
    OUTPUT_PATH_V3,
    SUBJECT_PIN_PATHS_V3,
    ClosureRejectV3,
    PythonImportDiscoveryV3,
    SourceFileV3,
    SourceSnapshotV3,
    SubjectSnapshotV3,
    _git_blob_sha,
    build_artifact_v3,
    check_artifact_v3,
    discover_bridge_imports_v3,
    is_python_discovery_path_v3,
    require_terminal_snapshot_match_v3,
)

OUTPUT_PATH: Final = Path(OUTPUT_PATH_V3)
_GIT_TIMEOUT_SECONDS_V3: Final = 10.0
_GIT_DISCOVERY_TIMEOUT_SECONDS_V3: Final = 30.0
_GIT_TREE_OUTPUT_MAX_BYTES_V3: Final = 4_194_304


def _repository_root_identity_v3(root: Path | str) -> tuple[int, int]:
    inert_root = _require_inert_path_v1(root, "O-003B repository root")
    try:
        observed = os.stat(inert_root, follow_symlinks=False)
    except OSError as exc:
        raise ClosureRejectV3("ROOT_CHANGED", "repository root", type(exc).__name__) from exc
    if not stat.S_ISDIR(observed.st_mode):
        raise ClosureRejectV3(
            "ROOT_CHANGED",
            "repository root",
            "root must remain one non-symlink directory",
        )
    return observed.st_dev, observed.st_ino


def _run_git_bytes_v3(
    root: Path,
    arguments: tuple[str, ...],
    *,
    label: str,
    max_output_bytes: int,
    input_bytes: bytes | None = None,
) -> bytes:
    argv = (
        _git_binary_v1(),
        "-c",
        "core.hooksPath=/dev/null",
        "-C",
        os.path.abspath(os.fspath(root)),
        *arguments,
    )
    try:
        if input_bytes is None:
            process = subprocess.run(  # noqa: S603 - fixed absolute Git binary and argv
                argv,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=_git_environment_v1(),
                timeout=_GIT_DISCOVERY_TIMEOUT_SECONDS_V3,
                check=False,
            )
        else:
            process = subprocess.run(  # noqa: S603 - fixed absolute Git binary and argv
                argv,
                input=input_bytes,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=_git_environment_v1(),
                timeout=_GIT_DISCOVERY_TIMEOUT_SECONDS_V3,
                check=False,
            )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ClosureRejectV3("GIT_DISCOVERY_READ", label, type(exc).__name__) from exc
    if process.returncode != 0 or process.stderr:
        raise ClosureRejectV3(
            "GIT_DISCOVERY_READ",
            label,
            f"Git status {process.returncode}",
        )
    if len(process.stdout) > max_output_bytes:
        raise ClosureRejectV3(
            "GIT_DISCOVERY_OUTPUT",
            label,
            f"{len(process.stdout)} bytes exceeds ceiling",
        )
    return process.stdout


def _git_python_discovery_v3(
    root: Path,
    commit: str,
) -> PythonImportDiscoveryV3:
    raw_tree = _run_git_bytes_v3(
        root,
        ("ls-tree", "-rlz", "--full-tree", commit),
        label=f"Python tree {commit}",
        max_output_bytes=_GIT_TREE_OUTPUT_MAX_BYTES_V3,
    )
    entries: list[tuple[str, str, int]] = []
    for raw_record in raw_tree.split(b"\x00"):
        if not raw_record:
            continue
        if b"\t" not in raw_record:
            raise ClosureRejectV3(
                "GIT_DISCOVERY_TREE",
                commit,
                "tree record lacks path separator",
            )
        metadata, raw_path = raw_record.split(b"\t", 1)
        try:
            parts = metadata.decode("ascii").split()
            path = raw_path.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ClosureRejectV3(
                "GIT_DISCOVERY_TREE",
                commit,
                "tree record encoding",
            ) from exc
        if not is_python_discovery_path_v3(path):
            continue
        if len(parts) != 4:
            raise ClosureRejectV3("GIT_DISCOVERY_TREE", path, "metadata shape")
        mode, object_type, blob_sha, size_text = parts
        if mode not in {"100644", "100755"} or object_type != "blob":
            raise ClosureRejectV3(
                "GIT_DISCOVERY_ENTRY",
                path,
                "requires a regular Python blob",
            )
        try:
            size = int(size_text)
        except ValueError as exc:
            raise ClosureRejectV3(
                "GIT_DISCOVERY_SIZE",
                path,
                "non-integer blob size",
            ) from exc
        if size < 0 or size > MAX_SOURCE_BYTES_V3:
            raise ClosureRejectV3(
                "GIT_DISCOVERY_SIZE",
                path,
                f"{size} bytes exceeds per-file ceiling",
            )
        entries.append((path, blob_sha, size))
    entries.sort()
    paths = tuple(path for path, _, _ in entries)
    if not paths or len(paths) > MAX_DISCOVERY_PATHS_V3 or len(set(paths)) != len(paths):
        raise ClosureRejectV3(
            "GIT_DISCOVERY_PATH_SET",
            commit,
            f"invalid path count {len(paths)}",
        )
    total_bytes = sum(size for _, _, size in entries)
    if total_bytes > MAX_DISCOVERY_TOTAL_BYTES_V3:
        raise ClosureRejectV3(
            "GIT_DISCOVERY_TOTAL_BYTES",
            commit,
            f"{total_bytes} bytes exceeds ceiling",
        )
    batch_input = b"".join(f"{blob_sha}\n".encode("ascii") for _, blob_sha, _ in entries)
    batch = _run_git_bytes_v3(
        root,
        ("cat-file", "--batch"),
        label=f"Python blobs {commit}",
        max_output_bytes=total_bytes + len(entries) * 96,
        input_bytes=batch_input,
    )
    cursor = 0
    source: dict[str, bytes] = {}
    for path, expected_blob_sha, expected_size in entries:
        newline = batch.find(b"\n", cursor)
        if newline < 0:
            raise ClosureRejectV3("GIT_DISCOVERY_BLOB", path, "missing header")
        try:
            header = batch[cursor:newline].decode("ascii").split()
        except UnicodeDecodeError as exc:
            raise ClosureRejectV3(
                "GIT_DISCOVERY_BLOB",
                path,
                "header encoding",
            ) from exc
        cursor = newline + 1
        if header != [expected_blob_sha, "blob", str(expected_size)]:
            raise ClosureRejectV3("GIT_DISCOVERY_BLOB", path, "header mismatch")
        end = cursor + expected_size
        data = batch[cursor:end]
        if end >= len(batch) or batch[end : end + 1] != b"\n":
            raise ClosureRejectV3("GIT_DISCOVERY_BLOB", path, "truncated bytes")
        cursor = end + 1
        if len(data) != expected_size or _git_blob_sha(data) != expected_blob_sha:
            raise ClosureRejectV3("GIT_DISCOVERY_BLOB", path, "identity mismatch")
        source[path] = data
    if cursor != len(batch):
        raise ClosureRejectV3("GIT_DISCOVERY_BLOB", commit, "trailing bytes")
    return discover_bridge_imports_v3(source)


def _worktree_python_discovery_v3(root: Path) -> PythonImportDiscoveryV3:
    raw_paths = _run_git_bytes_v3(
        root,
        ("ls-files", "-z", "--cached", "--others", "--exclude-standard"),
        label="current worktree Python paths",
        max_output_bytes=_GIT_TREE_OUTPUT_MAX_BYTES_V3,
    )
    try:
        paths = tuple(
            sorted(
                path
                for path in (
                    raw_path.decode("utf-8") for raw_path in raw_paths.split(b"\x00") if raw_path
                )
                if is_python_discovery_path_v3(path)
            )
        )
    except UnicodeDecodeError as exc:
        raise ClosureRejectV3(
            "WORKTREE_DISCOVERY_PATH",
            "worktree",
            "path encoding",
        ) from exc
    if not paths or len(paths) > MAX_DISCOVERY_PATHS_V3 or len(set(paths)) != len(paths):
        raise ClosureRejectV3(
            "WORKTREE_DISCOVERY_PATH_SET",
            "worktree",
            f"invalid path count {len(paths)}",
        )
    source: dict[str, bytes] = {}
    total_bytes = 0
    for path in paths:
        data = _read_bounded_regular_file_v1(
            root / path,
            MAX_SOURCE_BYTES_V3,
            f"O-003B current Python source {path}",
        )
        total_bytes += len(data)
        if total_bytes > MAX_DISCOVERY_TOTAL_BYTES_V3:
            raise ClosureRejectV3(
                "WORKTREE_DISCOVERY_TOTAL_BYTES",
                "worktree",
                f"{total_bytes} bytes exceeds ceiling",
            )
        source[path] = data
    return discover_bridge_imports_v3(source)


def _git_blob_bytes_v3(root: Path, blob_sha: str, path: str) -> bytes:
    size_text = _git_scalar_v1(root, ("cat-file", "-s", blob_sha), f"blob size {path}")
    try:
        size = int(size_text)
    except ValueError as exc:
        raise ClosureRejectV3("GIT_BLOB_SIZE", path, "non-integer Git blob size") from exc
    if size < 0 or size > MAX_SOURCE_BYTES_V3:
        raise ClosureRejectV3("SOURCE_SIZE", path, f"Git blob size {size} exceeds ceiling")
    argv = (
        _git_binary_v1(),
        "-c",
        "core.hooksPath=/dev/null",
        "-C",
        os.path.abspath(os.fspath(root)),
        "cat-file",
        "blob",
        blob_sha,
    )
    try:
        process = subprocess.run(  # noqa: S603 - fixed absolute Git binary and argv
            argv,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=_git_environment_v1(),
            timeout=_GIT_TIMEOUT_SECONDS_V3,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ClosureRejectV3("GIT_BLOB_READ", path, type(exc).__name__) from exc
    if process.returncode != 0 or process.stderr:
        raise ClosureRejectV3("GIT_BLOB_READ", path, f"Git status {process.returncode}")
    if len(process.stdout) != size or _git_blob_sha(process.stdout) != blob_sha:
        raise ClosureRejectV3("GIT_BLOB_READ", path, "Git blob bytes or identity drift")
    return process.stdout


def _tree_source_file_v3(root: Path, commit: str, path: str) -> SourceFileV3:
    entry_path, mode, object_type, blob_sha = _git_tree_entry_v1(root, commit, path)
    if entry_path != path or mode not in {"100644", "100755"} or object_type != "blob":
        raise ClosureRejectV3(
            "GIT_ENTRY",
            path,
            "requires one regular Git blob",
        )
    return SourceFileV3(
        path=path,
        git_blob_sha=blob_sha,
        data=_git_blob_bytes_v3(root, blob_sha, path),
    )


def _subject_source_file_v3(
    root: Path,
    *,
    captured_head: str,
    subject_commit: str,
    path: str,
) -> SourceFileV3:
    subject_entry = _git_tree_entry_v1(root, subject_commit, path)
    current_entry = _git_tree_entry_v1(root, captured_head, path)
    if subject_entry != current_entry:
        raise ClosureRejectV3(
            "STAGE_A_SOURCE_DRIFT",
            path,
            "current Git entry differs from the Stage-A evidence subject",
        )
    entry_path, mode, object_type, blob_sha = subject_entry
    if entry_path != path or mode not in {"100644", "100755"} or object_type != "blob":
        raise ClosureRejectV3(
            "GIT_ENTRY",
            path,
            "requires one regular Git blob",
        )
    data = _read_bounded_regular_file_v1(
        root / path,
        MAX_SOURCE_BYTES_V3,
        f"O-003B V3 source {path}",
    )
    if _git_blob_sha(data) != blob_sha:
        raise ClosureRejectV3(
            "WORKTREE_SOURCE_DRIFT",
            path,
            "working bytes differ from the exact Stage-A source blob",
        )
    return SourceFileV3(path=path, git_blob_sha=blob_sha, data=data)


def load_subject_snapshot_v3(
    root: Path | str,
    *,
    evidence_commit: str | None = None,
) -> SubjectSnapshotV3:
    inert_root = _require_inert_path_v1(root, "O-003B V3 root")
    captured_head = _git_head_v1(inert_root)
    subject_commit = captured_head if evidence_commit is None else evidence_commit
    subject_tree = _git_tree_v1(inert_root, subject_commit)
    baseline_tree = _git_tree_v1(inert_root, BASELINE_COMMIT_V3)
    if baseline_tree != BASELINE_TREE_V3:
        raise ClosureRejectV3("BASELINE_TREE", "Git", "fixed O-002 baseline tree drift")

    baseline_files = tuple(
        _tree_source_file_v3(inert_root, BASELINE_COMMIT_V3, path) for path in BASELINE_PIN_PATHS_V3
    )
    subject_files = tuple(
        _subject_source_file_v3(
            inert_root,
            captured_head=captured_head,
            subject_commit=subject_commit,
            path=path,
        )
        for path in SUBJECT_PIN_PATHS_V3
    )
    baseline_discovery = _git_python_discovery_v3(
        inert_root,
        BASELINE_COMMIT_V3,
    )
    subject_discovery = _git_python_discovery_v3(
        inert_root,
        subject_commit,
    )
    current_discovery = _worktree_python_discovery_v3(inert_root)
    rechecked_head = _git_head_v1(inert_root)
    return SubjectSnapshotV3(
        captured_head=captured_head,
        rechecked_head=rechecked_head,
        baseline=SourceSnapshotV3(
            commit=BASELINE_COMMIT_V3,
            tree=baseline_tree,
            files=baseline_files,
            discovery=baseline_discovery,
        ),
        subject=SourceSnapshotV3(
            commit=subject_commit,
            tree=subject_tree,
            files=subject_files,
            discovery=subject_discovery,
        ),
        baseline_is_subject_ancestor=_git_is_ancestor_v1(
            inert_root,
            BASELINE_COMMIT_V3,
            subject_commit,
        ),
        subject_is_current_ancestor=_git_is_ancestor_v1(
            inert_root,
            subject_commit,
            captured_head,
        ),
        current_discovery=current_discovery,
    )


def build_certificate_v3(
    root: Path | str,
    *,
    evidence_commit: str | None = None,
) -> bytes:
    return build_artifact_v3(load_subject_snapshot_v3(root, evidence_commit=evidence_commit))


def _artifact_evidence_commit(raw: bytes) -> str:
    try:
        artifact = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ClosureRejectV3("ARTIFACT_JSON", "artifact", type(exc).__name__) from exc
    if type(artifact) is not dict or type(artifact.get("evidence_subject")) is not dict:
        raise ClosureRejectV3("ARTIFACT_SUBJECT", "artifact", "evidence subject missing")
    commit = artifact["evidence_subject"].get("commit")
    if type(commit) is not str:
        raise ClosureRejectV3("ARTIFACT_SUBJECT", "artifact", "evidence commit missing")
    return commit


def _failure_report(exc: ClosureRejectV3 | ShellRejectV1) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "closed_value_movement_gates": 0,
        "finding": {"code": exc.code, "detail": exc.detail, "path": exc.path},
        "ok": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": "zenodex/retired-tau-bridge-closure-build/v3",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        inert_root = _require_inert_path_v1(args.root, "O-003B V3 root")
        root_identity = _repository_root_identity_v3(inert_root)
        output = inert_root / OUTPUT_PATH
        if args.check:
            actual = _read_bounded_regular_file_v1(
                output,
                MAX_ARTIFACT_BYTES_V3,
                "O-003B V3 certificate",
            )
            snapshot = load_subject_snapshot_v3(
                inert_root,
                evidence_commit=_artifact_evidence_commit(actual),
            )
            report = check_artifact_v3(actual, snapshot)
            terminal_snapshot = load_subject_snapshot_v3(
                inert_root,
                evidence_commit=snapshot.subject.commit,
            )
            require_terminal_snapshot_match_v3(
                snapshot,
                terminal_snapshot,
                expected_head=snapshot.captured_head,
            )
            terminal_actual = _read_bounded_regular_file_v1(
                output,
                MAX_ARTIFACT_BYTES_V3,
                "O-003B V3 terminal certificate",
            )
            if terminal_actual != actual:
                raise ClosureRejectV3(
                    "STAGE_B_ARTIFACT_CHANGED",
                    OUTPUT_PATH.as_posix(),
                    "artifact bytes changed before terminal acceptance",
                )
            if _repository_root_identity_v3(inert_root) != root_identity:
                raise ClosureRejectV3(
                    "ROOT_CHANGED",
                    "repository root",
                    "root identity changed before terminal acceptance",
                )
            if _git_head_v1(inert_root) != snapshot.captured_head:
                raise ClosureRejectV3(
                    "HEAD_CHANGED",
                    snapshot.captured_head,
                    "HEAD changed before terminal builder acceptance",
                )
            print(json.dumps(report, sort_keys=True))
            return 0 if report["ok"] is True else 1

        expected = build_certificate_v3(inert_root)
        _atomic_replace_regular_file_v1(output, expected)
        print(
            json.dumps(
                {
                    "artifact": OUTPUT_PATH.as_posix(),
                    "artifact_schema": ARTIFACT_SCHEMA_V3,
                    "artifact_sha256": hashlib.sha256(expected).hexdigest(),
                    "closed_value_movement_gates": 0,
                    "ok": True,
                    "production_authority": "NONE",
                    "release_authority": "NONE",
                    "settlement_authority": "NONE",
                    "value_movement_authority": "NONE",
                },
                sort_keys=True,
            )
        )
        return 0
    except (ClosureRejectV3, ShellRejectV1) as exc:
        print(json.dumps(_failure_report(exc), sort_keys=True))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
