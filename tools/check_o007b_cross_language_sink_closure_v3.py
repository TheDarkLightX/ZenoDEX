#!/usr/bin/env python3
"""Verify O-007B V3 history, artifact-only Stage B, and current applicability."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import o007b_cross_language_sink_closure_v3 as c  # noqa: E402
from tools.build_m6_normative_requirements_v1 import (  # noqa: E402
    ShellRejectV1,
    _git_head_v1,
    _git_is_ancestor_v1,
    _git_tree_entry_v1,
    _git_tree_v1,
    _read_bounded_regular_file_v1,
    _require_inert_path_v1,
    _run_git_v1,
)
from tools.build_m6_o006_command_lane_completion_v2 import (  # noqa: E402
    CommandLaneCompletionRejectV2,
    _non_promisor,
    _read_git_blob,
)
from tools.build_o007b_cross_language_sink_closure_v3 import (  # noqa: E402
    JSON_OUTPUT,
    MAX_ARTIFACT_BYTES_V3,
    MAX_SOURCE_BYTES_V3,
    REPO_ROOT,
    SourceBindingModeV3,
    _delta,
    _require_dependency_checks,
    _require_git_id,
    _sole_parent,
    collect_inventory_evidence_v3,
    load_stage_a_snapshot_v3,
)
from tools.o007a_deployed_sink_closure_v2 import O007AClosureRejectV2  # noqa: E402
from tools.o007b_cross_language_sink_closure_v3 import (  # noqa: E402
    O007BClosureRejectV3,
    SourcePinV3,
    StageASnapshotV3,
    validate_artifact_v3,
)


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise O007BClosureRejectV3(code, path, detail)


def _artifact_touch(root: Path, head: str) -> str:
    _status, stdout, stderr = _run_git_v1(
        root, ("rev-list", "--full-history", head, "--", c.ARTIFACT_PATH_V3)
    )
    rows = stdout.splitlines()
    if stderr or len(rows) != 1:
        _reject("ARTIFACT_HISTORY_COUNT", c.ARTIFACT_PATH_V3, "expected one path touch")
    return _require_git_id(rows[0], c.ARTIFACT_PATH_V3)


def _committed_blob(root: Path, commit: str, path: str, maximum: int) -> tuple[str, bytes]:
    recorded, mode, kind, blob = _git_tree_entry_v1(root, commit, path)
    if recorded != path or mode != "100644" or kind != "blob":
        _reject("ARTIFACT_GIT_ENTRY", path, "must be an exact regular Git blob")
    return blob, _read_git_blob(root, blob, maximum, path)


def _require_current_pin(root: Path, head: str, pin: SourcePinV3) -> None:
    try:
        recorded, mode, kind, blob = _git_tree_entry_v1(root, head, pin.path)
    except ShellRejectV1:
        _reject("CURRENT_SOURCE_DRIFT", pin.path, "source absent from current tree")
    if recorded != pin.path or mode != pin.git_mode or kind != "blob" or blob != pin.git_blob_sha:
        _reject("CURRENT_SOURCE_DRIFT", pin.path, "current Git blob differs from Stage A")
    current = _read_bounded_regular_file_v1(
        root / pin.path, MAX_SOURCE_BYTES_V3, f"O007B V3 current source {pin.path}"
    )
    if hashlib.sha256(current).hexdigest() != pin.sha256:
        _reject("CURRENT_SOURCE_WORKTREE_DRIFT", pin.path, "working bytes differ from Stage A")


@dataclass(frozen=True, slots=True)
class CheckStateV3:
    artifact_sha256: str = ""
    certificate_root: str | None = None
    current_applicable: bool = False
    finding: dict[str, str] | None = None
    historical_valid: bool = False
    stage_a_commit: str | None = None
    stage_b_commit: str | None = None


@dataclass(frozen=True, slots=True)
class HeadBindingV3:
    commit: str
    tree: str


@dataclass(frozen=True, slots=True)
class HistoricalSubjectV3:
    state: CheckStateV3
    stage_b: str
    snapshot: StageASnapshotV3
    artifact: bytes


def _report(state: CheckStateV3) -> dict[str, object]:
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
        "release_ready": False,
        "schema": c.CHECK_SCHEMA_V3,
        "settlement_authority": "NONE",
        "stage_a_commit": state.stage_a_commit,
        "stage_b_commit": state.stage_b_commit,
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm01_status": "OPEN",
        "vm_gates_closed": [],
    }


def _finding(exc: Exception) -> dict[str, str]:
    return {
        "code": str(getattr(exc, "code", type(exc).__name__)),
        "detail": str(getattr(exc, "detail", str(exc))),
        "path": str(getattr(exc, "path", "O007B_V3")),
    }


def _require_current_applicability(
    root: Path,
    head: HeadBindingV3,
    subject: HistoricalSubjectV3,
) -> str:
    if not _git_is_ancestor_v1(root, subject.stage_b, head.commit):
        _reject("STAGE_B_ANCESTRY", subject.stage_b, "Stage B is outside current ancestry")
    for pin in subject.snapshot.stage_a_source_pins + subject.snapshot.evidence_source_pins:
        _require_current_pin(root, head.commit, pin)
    stage_blob, _stage_raw = _committed_blob(
        root, subject.stage_b, c.ARTIFACT_PATH_V3, MAX_ARTIFACT_BYTES_V3
    )
    current_blob, _current_raw = _committed_blob(
        root, head.commit, c.ARTIFACT_PATH_V3, MAX_ARTIFACT_BYTES_V3
    )
    if stage_blob != current_blob:
        _reject("CURRENT_ARTIFACT_DRIFT", c.ARTIFACT_PATH_V3, "blob differs from Stage B")
    working = _read_bounded_regular_file_v1(
        root / JSON_OUTPUT, MAX_ARTIFACT_BYTES_V3, "O007B V3 working artifact"
    )
    if working != subject.artifact:
        _reject("CURRENT_ARTIFACT_WORKTREE_DRIFT", c.ARTIFACT_PATH_V3, "working bytes drift")
    o007a, o006 = _require_dependency_checks(root)
    inventory = collect_inventory_evidence_v3(root)
    certificate = validate_artifact_v3(
        subject.artifact,
        subject.snapshot,
        inventory=inventory,
        o007a_check=o007a,
        o006_check=o006,
    )
    if _git_head_v1(root) != head.commit or _git_tree_v1(root, head.commit) != head.tree:
        _reject("HEAD_CHANGED_DURING_CHECK", "HEAD", "head or tree changed")
    return certificate


def _load_historical_subject(root: Path, head: str) -> HistoricalSubjectV3:
    stage_b = _artifact_touch(root, head)
    stage_a = _sole_parent(root, stage_b)
    if _delta(root, stage_b) != (("A", c.ARTIFACT_PATH_V3),):
        _reject("STAGE_B_DELTA", stage_b, "Stage B must add only the V3 artifact")
    snapshot = load_stage_a_snapshot_v3(
        root, stage_a, source_binding=SourceBindingModeV3.GIT_ONLY
    )
    _artifact_blob, artifact = _committed_blob(
        root, stage_b, c.ARTIFACT_PATH_V3, MAX_ARTIFACT_BYTES_V3
    )
    artifact_sha256 = hashlib.sha256(artifact).hexdigest()
    certificate_root = validate_artifact_v3(artifact, snapshot)
    return HistoricalSubjectV3(
        state=CheckStateV3(
            artifact_sha256=artifact_sha256,
            certificate_root=certificate_root,
            historical_valid=True,
            stage_a_commit=stage_a,
            stage_b_commit=stage_b,
        ),
        stage_b=stage_b,
        snapshot=snapshot,
        artifact=artifact,
    )


def check_o007b_cross_language_sink_closure_v3(
    root: Path | str = REPO_ROOT,
) -> dict[str, object]:
    state = CheckStateV3()
    try:
        inert_root = _require_inert_path_v1(root, "O007B V3 checker root")
        _non_promisor(inert_root)
        initial_head = _require_git_id(_git_head_v1(inert_root), "HEAD")
        initial_tree = _require_git_id(_git_tree_v1(inert_root, initial_head), "HEAD tree")
        head = HeadBindingV3(commit=initial_head, tree=initial_tree)
        subject = _load_historical_subject(inert_root, head.commit)
        state = subject.state
        certificate_root = _require_current_applicability(
            inert_root, head, subject
        )
        return _report(
            CheckStateV3(
                artifact_sha256=state.artifact_sha256,
                certificate_root=certificate_root,
                current_applicable=True,
                historical_valid=True,
                stage_a_commit=state.stage_a_commit,
                stage_b_commit=state.stage_b_commit,
            )
        )
    except (
        O007BClosureRejectV3,
        O007AClosureRejectV2,
        ShellRejectV1,
        CommandLaneCompletionRejectV2,
    ) as exc:
        return _report(
            CheckStateV3(
                artifact_sha256=state.artifact_sha256,
                certificate_root=state.certificate_root,
                finding=_finding(exc),
                historical_valid=state.historical_valid,
                stage_a_commit=state.stage_a_commit,
                stage_b_commit=state.stage_b_commit,
            )
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(argv)
    report = check_o007b_cross_language_sink_closure_v3(args.root)
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
