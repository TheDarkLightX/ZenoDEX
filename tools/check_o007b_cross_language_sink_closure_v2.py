#!/usr/bin/env python3
"""Verify O-007B history, artifact-only Stage B, and current applicability."""

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
from tools.build_o007b_cross_language_sink_closure_v2 import (  # noqa: E402
    JSON_OUTPUT,
    MAX_ARTIFACT_BYTES_V2,
    MAX_SOURCE_BYTES_V2,
    REPO_ROOT,
    SourceBindingModeV2,
    _delta,
    _require_dependency_checks,
    _require_git_id,
    _sole_parent,
    collect_inventory_evidence_v2,
    load_stage_a_snapshot_v2,
)
from tools.o007a_deployed_sink_closure_v2 import O007AClosureRejectV2  # noqa: E402
from tools.o007b_cross_language_sink_closure_v2 import (  # noqa: E402
    ARTIFACT_PATH_V2,
    O007BClosureRejectV2,
    SourcePinV2,
    StageASnapshotV2,
    validate_artifact_v2,
)

CHECK_SCHEMA_V2 = "zenodex/o007b-cross-language-sink-closure-check/v2"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise O007BClosureRejectV2(code, path, detail)


def _artifact_touch(root: Path, head: str) -> str:
    _status, stdout, stderr = _run_git_v1(
        root, ("rev-list", "--full-history", head, "--", ARTIFACT_PATH_V2)
    )
    rows = stdout.splitlines()
    if stderr or len(rows) != 1:
        _reject("ARTIFACT_HISTORY_COUNT", ARTIFACT_PATH_V2, "expected one path touch")
    return _require_git_id(rows[0], ARTIFACT_PATH_V2)


def _committed_blob(root: Path, commit: str, path: str, maximum: int) -> tuple[str, bytes]:
    recorded, mode, kind, blob = _git_tree_entry_v1(root, commit, path)
    if recorded != path or mode != "100644" or kind != "blob":
        _reject("ARTIFACT_GIT_ENTRY", path, "must be an exact regular Git blob")
    return blob, _read_git_blob(root, blob, maximum, path)


def _require_current_pin(root: Path, head: str, pin: SourcePinV2) -> None:
    try:
        recorded, mode, kind, blob = _git_tree_entry_v1(root, head, pin.path)
    except ShellRejectV1:
        _reject("CURRENT_SOURCE_DRIFT", pin.path, "source absent from current tree")
    if recorded != pin.path or mode != pin.git_mode or kind != "blob" or blob != pin.git_blob_sha:
        _reject("CURRENT_SOURCE_DRIFT", pin.path, "current Git blob differs from Stage A")
    current = _read_bounded_regular_file_v1(
        root / pin.path, MAX_SOURCE_BYTES_V2, f"O007B current source {pin.path}"
    )
    if hashlib.sha256(current).hexdigest() != pin.sha256:
        _reject("CURRENT_SOURCE_WORKTREE_DRIFT", pin.path, "working bytes differ from Stage A")


@dataclass(frozen=True, slots=True)
class CheckStateV2:
    artifact_sha256: str = ""
    certificate_root: str | None = None
    current_applicable: bool = False
    finding: dict[str, str] | None = None
    historical_valid: bool = False
    stage_a_commit: str | None = None
    stage_b_commit: str | None = None


def _report(state: CheckStateV2) -> dict[str, object]:
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
        "schema": CHECK_SCHEMA_V2,
        "settlement_authority": "NONE",
        "stage_a_commit": state.stage_a_commit,
        "stage_b_commit": state.stage_b_commit,
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm01_status": "OPEN",
        "vm_gates_closed": [],
    }


def _finding(exc: Exception) -> dict[str, str]:
    code = getattr(exc, "code", type(exc).__name__)
    path = getattr(exc, "path", "O007B")
    detail = getattr(exc, "detail", str(exc))
    return {"code": str(code), "detail": str(detail), "path": str(path)}


def _require_current_applicability(
    root: Path,
    initial_head: str,
    initial_tree: str,
    stage_b: str,
    snapshot: StageASnapshotV2,
    committed_artifact: bytes,
) -> str:
    if not _git_is_ancestor_v1(root, stage_b, initial_head):
        _reject("STAGE_B_ANCESTRY", stage_b, "Stage B is outside current ancestry")
    for pin in snapshot.stage_a_source_pins + snapshot.evidence_source_pins:
        _require_current_pin(root, initial_head, pin)
    stage_blob, _stage_raw = _committed_blob(root, stage_b, ARTIFACT_PATH_V2, MAX_ARTIFACT_BYTES_V2)
    current_blob, _current_raw = _committed_blob(
        root, initial_head, ARTIFACT_PATH_V2, MAX_ARTIFACT_BYTES_V2
    )
    if stage_blob != current_blob:
        _reject("CURRENT_ARTIFACT_DRIFT", ARTIFACT_PATH_V2, "current blob differs from Stage B")
    working = _read_bounded_regular_file_v1(
        root / JSON_OUTPUT, MAX_ARTIFACT_BYTES_V2, "O007B working artifact"
    )
    if working != committed_artifact:
        _reject("CURRENT_ARTIFACT_WORKTREE_DRIFT", ARTIFACT_PATH_V2, "working bytes drift")
    o007a, o006 = _require_dependency_checks(root)
    inventory = collect_inventory_evidence_v2(root)
    certificate = validate_artifact_v2(
        committed_artifact,
        snapshot,
        inventory=inventory,
        o007a_check=o007a,
        o006_check=o006,
    )
    if _git_head_v1(root) != initial_head or _git_tree_v1(root, initial_head) != initial_tree:
        _reject("HEAD_CHANGED_DURING_CHECK", "HEAD", "head or tree changed")
    return certificate


def check_o007b_cross_language_sink_closure_v2(
    root: Path | str = REPO_ROOT,
) -> dict[str, object]:
    historical_valid = False
    artifact_sha256 = ""
    certificate_root: str | None = None
    stage_a: str | None = None
    stage_b: str | None = None
    try:
        inert_root = _require_inert_path_v1(root, "O007B checker root")
        _non_promisor(inert_root)
        initial_head = _require_git_id(_git_head_v1(inert_root), "HEAD")
        initial_tree = _require_git_id(_git_tree_v1(inert_root, initial_head), "HEAD tree")
        stage_b = _artifact_touch(inert_root, initial_head)
        stage_a = _sole_parent(inert_root, stage_b)
        if _delta(inert_root, stage_b) != (("A", ARTIFACT_PATH_V2),):
            _reject("STAGE_B_DELTA", stage_b, "Stage B must add only the V2 artifact")
        snapshot = load_stage_a_snapshot_v2(
            inert_root, stage_a, source_binding=SourceBindingModeV2.GIT_ONLY
        )
        _artifact_blob, committed_artifact = _committed_blob(
            inert_root, stage_b, ARTIFACT_PATH_V2, MAX_ARTIFACT_BYTES_V2
        )
        artifact_sha256 = hashlib.sha256(committed_artifact).hexdigest()
        certificate_root = validate_artifact_v2(committed_artifact, snapshot)
        historical_valid = True
        certificate_root = _require_current_applicability(
            inert_root,
            initial_head,
            initial_tree,
            stage_b,
            snapshot,
            committed_artifact,
        )
        return _report(
            CheckStateV2(
                artifact_sha256=artifact_sha256,
                certificate_root=certificate_root,
                current_applicable=True,
                historical_valid=True,
                stage_a_commit=stage_a,
                stage_b_commit=stage_b,
            )
        )
    except (
        O007BClosureRejectV2,
        O007AClosureRejectV2,
        ShellRejectV1,
        CommandLaneCompletionRejectV2,
    ) as exc:
        return _report(
            CheckStateV2(
                artifact_sha256=artifact_sha256,
                certificate_root=certificate_root,
                finding=_finding(exc),
                historical_valid=historical_valid,
                stage_a_commit=stage_a,
                stage_b_commit=stage_b,
            )
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(argv)
    report = check_o007b_cross_language_sink_closure_v2(args.root)
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
