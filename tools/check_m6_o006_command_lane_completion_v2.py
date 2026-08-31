#!/usr/bin/env python3
"""Verify O006 V2 history, artifact-only Stage B, and current applicability."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

try:
    from tools.build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _git_head_v1,
        _git_is_ancestor_v1,
        _git_tree_v1,
        _read_bounded_regular_file_v1,
        _require_inert_path_v1,
        _run_git_v1,
    )
    from tools.build_m6_o006_command_lane_completion_v2 import (
        JSON_OUTPUT,
        REPO_ROOT,
        SourceBindingModeV2,
        _entry,
        _non_promisor,
        _read_git_blob,
        _require_absent,
        _require_git_id,
        _sole_parent,
        _stage_a_delta,
        load_stage_a_snapshot_v2,
    )
    from tools.m6_o006_command_lane_completion_v2 import (
        ARTIFACT_PATH_V2,
        CHECK_SCHEMA_V2,
        MAX_ARTIFACT_BYTES_V2,
        MAX_SOURCE_BYTES_V2,
        CommandLaneCompletionRejectV2,
        StageASnapshotV2,
        validate_command_lane_completion_artifact_v2,
    )
except ModuleNotFoundError:
    from build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _git_head_v1,
        _git_is_ancestor_v1,
        _git_tree_v1,
        _read_bounded_regular_file_v1,
        _require_inert_path_v1,
        _run_git_v1,
    )
    from build_m6_o006_command_lane_completion_v2 import (  # type: ignore[no-redef]
        JSON_OUTPUT,
        REPO_ROOT,
        SourceBindingModeV2,
        _entry,
        _non_promisor,
        _read_git_blob,
        _require_absent,
        _require_git_id,
        _sole_parent,
        _stage_a_delta,
        load_stage_a_snapshot_v2,
    )
    from m6_o006_command_lane_completion_v2 import (  # type: ignore[no-redef]
        ARTIFACT_PATH_V2,
        CHECK_SCHEMA_V2,
        MAX_ARTIFACT_BYTES_V2,
        MAX_SOURCE_BYTES_V2,
        CommandLaneCompletionRejectV2,
        StageASnapshotV2,
        validate_command_lane_completion_artifact_v2,
    )


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise CommandLaneCompletionRejectV2(code, path, detail)


def _root_identity(root: Path) -> tuple[int, int]:
    try:
        value = os.stat(root, follow_symlinks=False)
    except OSError as exc:
        _reject("ROOT_STAT", str(root), type(exc).__name__)
    if not stat.S_ISDIR(value.st_mode):
        _reject("ROOT_TYPE", str(root), "checker root must be a directory")
    return value.st_dev, value.st_ino


def _artifact_touch(root: Path, head: str) -> str:
    _status, stdout, stderr = _run_git_v1(
        root, ("rev-list", "--full-history", head, "--", ARTIFACT_PATH_V2)
    )
    rows = stdout.splitlines()
    if stderr or len(rows) != 1:
        _reject(
            "ARTIFACT_HISTORY_COUNT",
            ARTIFACT_PATH_V2,
            "current ancestry must contain exactly one artifact path touch",
        )
    return _require_git_id(rows[0], ARTIFACT_PATH_V2, "ARTIFACT_HISTORY")


def _require_stage_b_delta(root: Path, stage_b: str) -> None:
    delta = _stage_a_delta(root, stage_b)
    if delta != (("A", ARTIFACT_PATH_V2),):
        _reject("STAGE_B_DELTA", stage_b, "Stage B must add only the canonical V2 JSON")


def _committed_artifact(root: Path, stage_b: str) -> tuple[str, bytes]:
    blob, _mode = _entry(root, stage_b, ARTIFACT_PATH_V2)
    raw = _read_git_blob(root, blob, MAX_ARTIFACT_BYTES_V2, ARTIFACT_PATH_V2)
    return blob, raw


@dataclass(frozen=True)
class CurrentBindingV2:
    root: Path
    initial_identity: tuple[int, int]
    current_head: str
    current_tree: str
    stage_b: str
    snapshot: StageASnapshotV2
    working_artifact: bytes
    committed_artifact: bytes


def _require_current_applicability(binding: CurrentBindingV2) -> None:
    for pin in binding.snapshot.base_source_pins + binding.snapshot.stage_a_source_pins:
        try:
            current_blob, _mode = _entry(binding.root, binding.current_head, pin.path)
        except ShellRejectV1:
            _reject("CURRENT_SOURCE_DRIFT", pin.path, "current source is absent or malformed")
        if current_blob != pin.git_blob_sha:
            _reject("CURRENT_SOURCE_DRIFT", pin.path, "current Git blob differs from Stage A")
        current_raw = _read_bounded_regular_file_v1(
            binding.root / pin.path, MAX_SOURCE_BYTES_V2, f"O006 current source {pin.path}"
        )
        if current_raw != _read_git_blob(binding.root, current_blob, MAX_SOURCE_BYTES_V2, pin.path):
            _reject(
                "CURRENT_SOURCE_WORKTREE_DRIFT", pin.path, "working bytes differ from current Git"
            )
    try:
        stage_blob, _stage_mode = _entry(binding.root, binding.stage_b, ARTIFACT_PATH_V2)
        current_blob, _current_mode = _entry(binding.root, binding.current_head, ARTIFACT_PATH_V2)
    except ShellRejectV1:
        _reject("CURRENT_ARTIFACT_DRIFT", ARTIFACT_PATH_V2, "artifact is absent or malformed")
    if current_blob != stage_blob:
        _reject("CURRENT_ARTIFACT_DRIFT", ARTIFACT_PATH_V2, "artifact Git blob changed")
    if binding.working_artifact != binding.committed_artifact:
        _reject(
            "CURRENT_ARTIFACT_WORKTREE_DRIFT",
            ARTIFACT_PATH_V2,
            "working artifact differs from committed Stage B",
        )
    if _root_identity(binding.root) != binding.initial_identity:
        _reject("ROOT_IDENTITY_CHANGED", str(binding.root), "root identity changed")
    final_head = _require_git_id(_git_head_v1(binding.root), "HEAD", "GIT_HEAD")
    final_tree = _require_git_id(_git_tree_v1(binding.root, final_head), "HEAD tree", "GIT_TREE")
    if final_head != binding.current_head or final_tree != binding.current_tree:
        _reject("HEAD_CHANGED_DURING_CHECK", "HEAD", "HEAD or tree changed")


@dataclass(frozen=True)
class ReportStateV2:
    artifact_sha256: str = ""
    certificate_root: str | None = None
    current_applicable: bool = False
    finding: dict[str, str] | None = None
    historical_valid: bool = False


def _report(state: ReportStateV2) -> dict[str, object]:
    return {
        "artifact_sha256": state.artifact_sha256,
        "certificate_root": state.certificate_root,
        "current_applicable": state.current_applicable,
        "finding": state.finding,
        "historical_valid": state.historical_valid,
        "migration_authority": "NONE",
        "ok": state.historical_valid and state.current_applicable and state.finding is None,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": CHECK_SCHEMA_V2,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm_gates_closed": [],
    }


def _finding(exc: CommandLaneCompletionRejectV2 | ShellRejectV1) -> dict[str, str]:
    return {"code": exc.code, "detail": exc.detail, "path": exc.path}


@dataclass(frozen=True)
class InitialRepositoryStateV2:
    identity: tuple[int, int]
    head: str
    tree: str


def _initial_repository_state(root: Path) -> InitialRepositoryStateV2:
    identity = _root_identity(root)
    _non_promisor(root)
    head = _require_git_id(_git_head_v1(root), "HEAD", "GIT_HEAD")
    tree = _require_git_id(_git_tree_v1(root, head), "HEAD tree", "GIT_TREE")
    return InitialRepositoryStateV2(identity=identity, head=head, tree=tree)


def check_m6_o006_command_lane_completion_v2(
    root: Path | str = REPO_ROOT,
) -> dict[str, object]:
    """Validate committed history first, then current tree/worktree applicability."""

    historical_valid = False
    artifact_sha256 = ""
    certificate_root: str | None = None
    try:
        inert_root = _require_inert_path_v1(root, "O006 V2 checker root")
        initial = _initial_repository_state(inert_root)
        working_artifact = _read_bounded_regular_file_v1(
            inert_root / JSON_OUTPUT, MAX_ARTIFACT_BYTES_V2, "O006 V2 artifact"
        )
        stage_b = _artifact_touch(inert_root, initial.head)
        if not _git_is_ancestor_v1(inert_root, stage_b, initial.head):
            _reject("STAGE_B_ANCESTRY", stage_b, "artifact commit is outside current ancestry")
        stage_a = _sole_parent(inert_root, stage_b)
        _require_stage_b_delta(inert_root, stage_b)
        _require_absent(inert_root, stage_a, ARTIFACT_PATH_V2, "STAGE_A_ARTIFACT")
        _artifact_blob, committed_artifact = _committed_artifact(inert_root, stage_b)
        artifact_sha256 = hashlib.sha256(committed_artifact).hexdigest()
        historical_snapshot = load_stage_a_snapshot_v2(
            inert_root, stage_a, source_binding=SourceBindingModeV2.GIT_ONLY
        )
        certificate_root = validate_command_lane_completion_artifact_v2(
            committed_artifact, historical_snapshot
        )
        historical_valid = True
        _require_current_applicability(
            CurrentBindingV2(
                root=inert_root,
                initial_identity=initial.identity,
                current_head=initial.head,
                current_tree=initial.tree,
                stage_b=stage_b,
                snapshot=historical_snapshot,
                working_artifact=working_artifact,
                committed_artifact=committed_artifact,
            )
        )
        return _report(
            ReportStateV2(
                artifact_sha256=artifact_sha256,
                certificate_root=certificate_root,
                current_applicable=True,
                historical_valid=True,
            )
        )
    except (CommandLaneCompletionRejectV2, ShellRejectV1) as exc:
        return _report(
            ReportStateV2(
                artifact_sha256=artifact_sha256,
                certificate_root=certificate_root,
                current_applicable=False,
                finding=_finding(exc),
                historical_valid=historical_valid,
            )
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(argv)
    report = check_m6_o006_command_lane_completion_v2(args.root)
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
