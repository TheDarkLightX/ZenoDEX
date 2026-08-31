#!/usr/bin/env python3
"""Build the source-bound O-007B artifact from an exact Stage-A commit."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from enum import Enum
from pathlib import Path
from typing import NoReturn

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import o007b_cross_language_sink_closure_v2 as c  # noqa: E402
from tools.build_m6_normative_requirements_v1 import (  # noqa: E402
    ShellRejectV1,
    _atomic_replace_regular_file_v1,
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
from tools.check_m6_o006_command_lane_completion_v2 import (  # noqa: E402
    check_m6_o006_command_lane_completion_v2,
)
from tools.check_o007a_deployed_sink_closure_v2 import (  # noqa: E402
    check_o007a_deployed_sink_closure_v2,
)
from tools.m6_cross_language_sinks.report import (  # noqa: E402
    MANIFEST_NAME,
    build_cross_language_report,
)
from tools.o007a_deployed_sink_closure_v2 import O007AClosureRejectV2  # noqa: E402
from tools.o007b_cross_language_sink_closure_v2 import (  # noqa: E402
    O007BClosureRejectV2,
    SourcePinV2,
    StageASnapshotV2,
    build_artifact_v2,
    canonical_json_bytes_v2,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
JSON_OUTPUT = Path(c.ARTIFACT_PATH_V2)
MAX_SOURCE_BYTES_V2 = 16 * 1024 * 1024
MAX_ARTIFACT_BYTES_V2 = 1024 * 1024
_GIT_ID_RE = re.compile(r"[0-9a-f]{40}\Z")


class SourceBindingModeV2(Enum):
    GIT_AND_WORKTREE = "GIT_AND_WORKTREE"
    GIT_ONLY = "GIT_ONLY"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise O007BClosureRejectV2(code, path, detail)


def _require_git_id(value: str, path: str) -> str:
    if _GIT_ID_RE.fullmatch(value) is None:
        _reject("GIT_ID", path, "must be lowercase forty-hex")
    return value


def _sole_parent(root: Path, commit: str) -> str:
    _status, stdout, stderr = _run_git_v1(root, ("rev-list", "--parents", "-n", "1", commit))
    fields = stdout.strip().split()
    if stderr or len(fields) != 2 or fields[0] != commit:
        _reject("COMMIT_PARENT", commit, "expected exactly one parent")
    return _require_git_id(fields[1], commit)


def _delta(root: Path, commit: str) -> tuple[tuple[str, str], ...]:
    _status, stdout, stderr = _run_git_v1(
        root,
        (
            "diff-tree",
            "--no-commit-id",
            "--name-status",
            "--no-renames",
            "-r",
            "-z",
            commit,
        ),
    )
    if stderr:
        _reject("COMMIT_DELTA", commit, "unexpected Git stderr")
    fields = stdout.split("\0")
    if fields and fields[-1] == "":
        fields.pop()
    if len(fields) % 2:
        _reject("COMMIT_DELTA", commit, "malformed name-status output")
    return tuple(
        sorted(
            ((fields[index], fields[index + 1]) for index in range(0, len(fields), 2)),
            key=lambda row: (row[1], row[0]),
        )
    )


def _require_absent(root: Path, commit: str, path: str, code: str) -> None:
    _status, stdout, stderr = _run_git_v1(
        root, ("ls-tree", "-z", "--full-tree", commit, "--", path)
    )
    if stdout or stderr:
        _reject(code, path, "path must be absent")


def _pin(root: Path, commit: str, path: str) -> tuple[SourcePinV2, bytes]:
    recorded, mode, kind, blob = _git_tree_entry_v1(root, commit, path)
    if recorded != path or mode not in {"100644", "100755"} or kind != "blob":
        _reject("SOURCE_GIT_ENTRY", path, "must be an exact regular Git blob")
    raw = _read_git_blob(root, blob, MAX_SOURCE_BYTES_V2, path)
    return (
        SourcePinV2(
            path=path,
            git_blob_sha=blob,
            git_mode=mode,
            sha256=hashlib.sha256(raw).hexdigest(),
            size_bytes=len(raw),
        ),
        raw,
    )


def _verify_provenance(root: Path) -> None:
    if _sole_parent(root, c.SELECTED_DONOR_COMMIT_V2) != c.SELECTED_DONOR_PARENT_V2:
        _reject("DONOR_PARENT", c.SELECTED_DONOR_COMMIT_V2, "parent mismatch")
    if _git_tree_v1(root, c.SELECTED_DONOR_COMMIT_V2) != c.SELECTED_DONOR_TREE_V2:
        _reject("DONOR_TREE", c.SELECTED_DONOR_COMMIT_V2, "tree mismatch")
    if _delta(root, c.SELECTED_DONOR_COMMIT_V2) != tuple(
        ("A", path) for path in c.DONOR_WRITE_SET_V2
    ):
        _reject("DONOR_WRITE_SET", c.SELECTED_DONOR_COMMIT_V2, "write set mismatch")
    if _sole_parent(root, c.REJECTED_RECEIPT_COMMIT_V1) != c.SELECTED_DONOR_COMMIT_V2:
        _reject("REJECTED_RECEIPT_PARENT", c.REJECTED_RECEIPT_COMMIT_V1, "parent mismatch")
    if _git_tree_v1(root, c.REJECTED_RECEIPT_COMMIT_V1) != c.REJECTED_RECEIPT_TREE_V1:
        _reject("REJECTED_RECEIPT_TREE", c.REJECTED_RECEIPT_COMMIT_V1, "tree mismatch")
    rejected_pin, _raw = _pin(root, c.REJECTED_RECEIPT_COMMIT_V1, c.REJECTED_RECEIPT_PATH_V1)
    if rejected_pin.sha256 != c.REJECTED_RECEIPT_SHA256_V1:
        _reject("REJECTED_RECEIPT_SHA", c.REJECTED_RECEIPT_PATH_V1, "SHA mismatch")


def _validate_stage_topology(root: Path, stage_a: str) -> str:
    if _git_tree_v1(root, c.BASE_COMMIT_V2) != c.BASE_TREE_V2:
        _reject("BASE_TREE", c.BASE_COMMIT_V2, "canonical base tree drift")
    if _sole_parent(root, stage_a) != c.BASE_COMMIT_V2:
        _reject("BASE_NOT_DIRECT_PARENT", stage_a, "Stage A must directly follow base")
    stage_tree = _require_git_id(_git_tree_v1(root, stage_a), "stage_a_tree")
    if _delta(root, stage_a) != tuple(("A", path) for path in c.STAGE_A_SOURCE_PATHS_V2):
        _reject("STAGE_A_DELTA", stage_a, "Stage A must add only declared source paths")
    _require_absent(root, stage_a, c.ARTIFACT_PATH_V2, "STAGE_A_ARTIFACT")
    _require_absent(root, stage_a, c.REJECTED_RECEIPT_PATH_V1, "REJECTED_V1_PRESENT")
    for path in c.STAGE_A_SOURCE_PATHS_V2:
        _require_absent(root, c.BASE_COMMIT_V2, path, "BASE_STAGE_A_SOURCE_PRESENT")
    if not _git_is_ancestor_v1(root, c.PLAN_COMMIT_V2, stage_a):
        _reject("PLAN_ANCESTRY", c.PLAN_COMMIT_V2, "plan is not an ancestor")
    if not _git_is_ancestor_v1(root, c.ADMISSION_COMMIT_V2, stage_a):
        _reject("ADMISSION_ANCESTRY", c.ADMISSION_COMMIT_V2, "admission is not an ancestor")
    return stage_tree


def load_stage_a_snapshot_v2(
    root: Path | str = REPO_ROOT,
    stage_a_commit: str | None = None,
    *,
    source_binding: SourceBindingModeV2 = SourceBindingModeV2.GIT_AND_WORKTREE,
) -> StageASnapshotV2:
    if type(source_binding) is not SourceBindingModeV2:
        _reject("SOURCE_BINDING_MODE", "source_binding", "invalid mode")
    inert_root = _require_inert_path_v1(root, "O007B Stage-A root")
    _non_promisor(inert_root)
    captured_head = _require_git_id(_git_head_v1(inert_root), "HEAD")
    stage_a = (
        captured_head if stage_a_commit is None else _require_git_id(stage_a_commit, "stage_a")
    )
    stage_tree = _validate_stage_topology(inert_root, stage_a)
    _verify_provenance(inert_root)
    stage_rows = tuple(_pin(inert_root, stage_a, path) for path in c.STAGE_A_SOURCE_PATHS_V2)
    evidence_rows = tuple(_pin(inert_root, stage_a, path) for path in c.EVIDENCE_SOURCE_PATHS_V2)
    if source_binding is SourceBindingModeV2.GIT_AND_WORKTREE:
        if captured_head != stage_a:
            _reject("STAGE_A_NOT_HEAD", stage_a, "worktree binding requires Stage A at HEAD")
        for pin, expected in stage_rows + evidence_rows:
            current = _read_bounded_regular_file_v1(
                inert_root / pin.path, MAX_SOURCE_BYTES_V2, f"O007B source {pin.path}"
            )
            if current != expected:
                _reject("STAGE_A_WORKTREE_BINDING", pin.path, "working bytes differ from Git")
    if _git_head_v1(inert_root) != captured_head:
        _reject("HEAD_CHANGED_DURING_CHECK", "HEAD", "head changed")
    return StageASnapshotV2(
        stage_a_commit=stage_a,
        stage_a_tree=stage_tree,
        stage_a_source_pins=tuple(row[0] for row in stage_rows),
        evidence_source_pins=tuple(row[0] for row in evidence_rows),
    )


def _require_dependency_checks(root: Path) -> tuple[dict[str, object], dict[str, object]]:
    o007a = check_o007a_deployed_sink_closure_v2(root)
    o006 = check_m6_o006_command_lane_completion_v2(root)
    if o007a.get("ok") is not True or o007a.get("current_applicable") is not True:
        _reject("O007A_CHECK", c.O007A_ARTIFACT_PATH_V2, "dependency is not current")
    expected_o007a = {
        "artifact_sha256": c.O007A_ARTIFACT_SHA256_V2,
        "certificate_root": c.O007A_CERTIFICATE_ROOT_V2,
        "stage_a_commit": c.O007A_STAGE_A_V2,
        "stage_b_commit": c.O007A_STAGE_B_V2,
    }
    for key, value in expected_o007a.items():
        if o007a.get(key) != value:
            _reject("O007A_BINDING", key, "exact dependency binding mismatch")
    if o006.get("ok") is not True or o006.get("current_applicable") is not True:
        _reject("O006_CHECK", c.O006_ARTIFACT_PATH_V2, "dependency is not current")
    if (
        o006.get("artifact_sha256") != c.O006_ARTIFACT_SHA256_V2
        or o006.get("certificate_root") != c.O006_CERTIFICATE_ROOT_V2
    ):
        _reject("O006_BINDING", c.O006_ARTIFACT_PATH_V2, "exact dependency binding mismatch")
    return o007a, o006


def collect_inventory_evidence_v2(root: Path) -> dict[str, object]:
    report = build_cross_language_report(root)
    if report.get("ok") is not True:
        _reject("INVENTORY_CHECK", "cross_language_report", json.dumps(report.get("findings")))
    if report.get("release_ready") is not False or report.get("vm01_status") != "OPEN":
        _reject("CLAIM_CEILING", "cross_language_report", "release or VM status drift")
    try:
        manifest = json.loads((root / "tools" / MANIFEST_NAME).read_bytes())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject("MANIFEST_READ", str(MANIFEST_NAME), type(exc).__name__)
    if not isinstance(manifest, dict) or not isinstance(manifest.get("projection"), dict):
        _reject("MANIFEST_SHAPE", str(MANIFEST_NAME), "projection is missing")
    projection = manifest["projection"]
    keys = (
        "command_lane_consistency",
        "dynamic_import_declarations_root",
        "generated_include_owners_root",
        "generated_python_owners_root",
        "generated_replay_ownership_complete",
        "language_operation_definitions",
        "operation_occurrence_counts",
        "operation_roots",
        "operation_row_counts",
        "projection_root",
        "source_counts",
        "source_provenance_counts",
        "source_roots",
        "tracked_candidate_count",
        "unmediated_operation_count",
        "unmediated_operation_root",
    )
    evidence = {key: projection[key] for key in keys}
    evidence.update(
        {
            "dynamic_import_declaration_count": report["dynamic_import_declaration_count"],
            "generated_include_owner_count": report["generated_include_owner_count"],
            "generated_python_owner_count": report["generated_python_owner_count"],
            "manifest_sha256": report["manifest_sha256"],
            "report_findings": report["findings"],
            "report_ok": report["ok"],
            "release_ready": report["release_ready"],
            "unresolved_dynamic_import_count": report["unresolved_dynamic_import_count"],
            "vm01_status": report["vm01_status"],
        }
    )
    return evidence


def build_bytes_v2(root: Path, stage_a_commit: str | None = None) -> bytes:
    snapshot = load_stage_a_snapshot_v2(root, stage_a_commit)
    o007a, o006 = _require_dependency_checks(root)
    inventory = collect_inventory_evidence_v2(root)
    return canonical_json_bytes_v2(
        build_artifact_v2(
            snapshot,
            inventory=inventory,
            o007a_check=o007a,
            o006_check=o006,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--stage-a-commit")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    root = _require_inert_path_v1(args.root, "O007B builder root")
    payload = build_bytes_v2(root, args.stage_a_commit)
    destination = root / JSON_OUTPUT
    if args.check:
        current = _read_bounded_regular_file_v1(
            destination, MAX_ARTIFACT_BYTES_V2, "O007B artifact"
        )
        if current != payload:
            _reject("ARTIFACT_STALE", c.ARTIFACT_PATH_V2, "working bytes differ")
    else:
        _atomic_replace_regular_file_v1(destination, payload)
    print(hashlib.sha256(payload).hexdigest())
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        O007BClosureRejectV2,
        O007AClosureRejectV2,
        ShellRejectV1,
        CommandLaneCompletionRejectV2,
    ) as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1) from exc
