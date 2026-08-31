#!/usr/bin/env python3
"""Build the source-bound O-007C indirect sink closure artifact."""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from enum import Enum
from pathlib import Path
from typing import NoReturn

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import o007c_indirect_sink_closure_v1 as c  # noqa: E402
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
    _non_promisor,
    _read_git_blob,
)
from tools.build_o007b_cross_language_sink_closure_v2 import (  # noqa: E402
    _delta,
    _require_git_id,
    _sole_parent,
)
from tools.check_o007b_cross_language_sink_closure_v3 import (  # noqa: E402
    check_o007b_cross_language_sink_closure_v3,
)
from tools.m6_indirect_value_sinks.inventory import (  # noqa: E402
    REGISTRY_PATH,
    build_projection,
    decode_registry,
)
from tools.m6_indirect_value_sinks.model import IndirectSinkRejectV1  # noqa: E402
from tools.m6_indirect_value_sinks.report import (  # noqa: E402
    _build_indirect_value_sink_report,
)
from tools.o007c_indirect_sink_closure_v1 import (  # noqa: E402
    O007CClosureRejectV1,
    SourcePinV1,
    StageASnapshotV1,
    build_artifact_v1,
    canonical_json_bytes_v1,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
JSON_OUTPUT = Path(c.ARTIFACT_PATH_V1)
MAX_SOURCE_BYTES_V1 = 16 * 1024 * 1024
MAX_ARTIFACT_BYTES_V1 = 1024 * 1024
_GIT_ID_RE = re.compile(r"[0-9a-f]{40}\Z")


class SourceBindingModeV1(Enum):
    GIT_AND_WORKTREE = "GIT_AND_WORKTREE"
    GIT_ONLY = "GIT_ONLY"


def reject(code: str, path: str, detail: str) -> NoReturn:
    raise O007CClosureRejectV1(code, path, detail)


def _require_absent(root: Path, commit: str, path: str, code: str) -> None:
    _status, stdout, stderr = _run_git_v1(
        root, ("ls-tree", "-z", "--full-tree", commit, "--", path)
    )
    if stdout or stderr:
        reject(code, path, "path must be absent")


def _pin(root: Path, commit: str, path: str) -> tuple[SourcePinV1, bytes]:
    recorded, mode, kind, blob = _git_tree_entry_v1(root, commit, path)
    if recorded != path or mode not in {"100644", "100755"} or kind != "blob":
        reject("SOURCE_GIT_ENTRY", path, "must be an exact regular Git blob")
    raw = _read_git_blob(root, blob, MAX_SOURCE_BYTES_V1, path)
    return (
        SourcePinV1(
            path=path,
            git_blob_sha=blob,
            git_mode=mode,
            sha256=hashlib.sha256(raw).hexdigest(),
            size_bytes=len(raw),
        ),
        raw,
    )


def _require_preserved(root: Path, stage_a: str) -> None:
    for path in c.PRESERVED_PATHS_V1:
        if _git_tree_entry_v1(root, c.BASE_COMMIT_V1, path) != _git_tree_entry_v1(
            root, stage_a, path
        ):
            reject("PREDECESSOR_BYTE_DRIFT", path, "Git entry differs from exact base")


def _validate_stage_topology(root: Path, stage_a: str) -> str:
    if _git_tree_v1(root, c.BASE_COMMIT_V1) != c.BASE_TREE_V1:
        reject("BASE_TREE", c.BASE_COMMIT_V1, "canonical base tree drift")
    if _sole_parent(root, stage_a) != c.BASE_COMMIT_V1:
        reject("BASE_NOT_DIRECT_PARENT", stage_a, "Stage A must directly follow base")
    stage_tree = _require_git_id(_git_tree_v1(root, stage_a), "stage_a_tree")
    expected_delta = tuple(("A", path) for path in c.STAGE_A_SOURCE_PATHS_V1)
    if _delta(root, stage_a) != expected_delta:
        reject("STAGE_A_DELTA", stage_a, "Stage A must add only declared paths")
    _require_absent(root, stage_a, c.ARTIFACT_PATH_V1, "STAGE_A_ARTIFACT")
    for path in c.STAGE_A_SOURCE_PATHS_V1:
        _require_absent(root, c.BASE_COMMIT_V1, path, "BASE_STAGE_A_SOURCE_PRESENT")
    _require_preserved(root, stage_a)
    if not _git_is_ancestor_v1(root, c.PLAN_COMMIT_V1, stage_a):
        reject("PLAN_ANCESTRY", c.PLAN_COMMIT_V1, "plan is not an ancestor")
    if not _git_is_ancestor_v1(root, c.ADMISSION_COMMIT_V1, stage_a):
        reject("ADMISSION_ANCESTRY", c.ADMISSION_COMMIT_V1, "admission is not an ancestor")
    return stage_tree


def load_stage_a_snapshot_v1(
    root: Path | str = REPO_ROOT,
    stage_a_commit: str | None = None,
    *,
    source_binding: SourceBindingModeV1 = SourceBindingModeV1.GIT_AND_WORKTREE,
) -> StageASnapshotV1:
    if type(source_binding) is not SourceBindingModeV1:
        reject("SOURCE_BINDING_MODE", "source_binding", "invalid mode")
    inert_root = _require_inert_path_v1(root, "O007C Stage-A root")
    _non_promisor(inert_root)
    captured_head = _require_git_id(_git_head_v1(inert_root), "HEAD")
    stage_a = captured_head if stage_a_commit is None else _require_git_id(
        stage_a_commit, "stage_a"
    )
    stage_tree = _validate_stage_topology(inert_root, stage_a)
    rows = tuple(_pin(inert_root, stage_a, path) for path in c.STAGE_A_SOURCE_PATHS_V1)
    by_path = {pin.path: raw for pin, raw in rows}
    registry_raw = by_path[REGISTRY_PATH]
    registry = decode_registry(registry_raw)
    if registry.get("review_status") != "REVIEWED_CURRENT_SUBJECT":
        reject("REGISTRY_REVIEW", REGISTRY_PATH, "Stage A registry is not reviewed")
    summary = registry.get("inventory_summary")
    if not isinstance(summary, dict):
        reject("REGISTRY_SUMMARY", REGISTRY_PATH, "inventory summary is absent")
    lifecycle = registry.get("lifecycle_dispositions")
    if not isinstance(lifecycle, list) or any(not isinstance(row, dict) for row in lifecycle):
        reject("REGISTRY_LIFECYCLE", REGISTRY_PATH, "lifecycle rows are absent")
    projection = build_projection(inert_root, {"summary": summary}, registry)
    if source_binding is SourceBindingModeV1.GIT_AND_WORKTREE:
        if captured_head != stage_a:
            reject("STAGE_A_NOT_HEAD", stage_a, "worktree binding requires Stage A at HEAD")
        for pin, expected in rows:
            current = _read_bounded_regular_file_v1(
                inert_root / pin.path, MAX_SOURCE_BYTES_V1, f"O007C source {pin.path}"
            )
            if current != expected:
                reject("STAGE_A_WORKTREE_BINDING", pin.path, "working bytes differ from Git")
    if _git_head_v1(inert_root) != captured_head:
        reject("HEAD_CHANGED_DURING_CHECK", "HEAD", "head changed")
    return StageASnapshotV1(
        stage_a_commit=stage_a,
        stage_a_tree=stage_tree,
        stage_a_source_pins=tuple(pin for pin, _raw in rows),
        registry_sha256=hashlib.sha256(registry_raw).hexdigest(),
        registry_inventory_summary=summary,
        registry_lifecycle_dispositions=tuple(lifecycle),
        registry_projection_root=str(projection["projection_root"]),
    )


def collect_current_evidence_v1(
    root: Path,
) -> tuple[dict[str, object], dict[str, object]]:
    o007b = check_o007b_cross_language_sink_closure_v3(root)
    c.require_o007b_v3(o007b)
    inventory = _build_indirect_value_sink_report(root, o007b_report=o007b)
    if inventory.get("ok") is not True:
        finding = inventory.get("finding")
        reject("INVENTORY_REPORT", "O-007C", str(finding))
    return inventory, o007b


def build_bytes_v1(root: Path, stage_a_commit: str | None = None) -> bytes:
    source_binding = (
        SourceBindingModeV1.GIT_AND_WORKTREE
        if stage_a_commit is None
        else SourceBindingModeV1.GIT_ONLY
    )
    snapshot = load_stage_a_snapshot_v1(
        root,
        stage_a_commit,
        source_binding=source_binding,
    )
    inventory, o007b = collect_current_evidence_v1(root)
    return canonical_json_bytes_v1(
        build_artifact_v1(
            snapshot,
            inventory_report=inventory,
            o007b_report=o007b,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--stage-a-commit")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    root = _require_inert_path_v1(args.root, "O007C builder root")
    payload = build_bytes_v1(root, args.stage_a_commit)
    destination = root / JSON_OUTPUT
    if args.check:
        current = _read_bounded_regular_file_v1(
            destination, MAX_ARTIFACT_BYTES_V1, "O007C artifact"
        )
        if current != payload:
            reject("ARTIFACT_STALE", c.ARTIFACT_PATH_V1, "working bytes differ")
    else:
        _atomic_replace_regular_file_v1(destination, payload)
    print(hashlib.sha256(payload).hexdigest())
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (O007CClosureRejectV1, IndirectSinkRejectV1, ShellRejectV1) as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1) from exc
