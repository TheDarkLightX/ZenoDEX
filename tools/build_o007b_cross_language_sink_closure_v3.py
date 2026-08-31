#!/usr/bin/env python3
"""Build the source-bound O-007B V3 artifact or its review manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from enum import Enum
from pathlib import Path
from typing import Any, NoReturn

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import o007b_cross_language_sink_closure_v3 as c  # noqa: E402
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
from tools.build_o007b_cross_language_sink_closure_v2 import (  # noqa: E402
    _delta,
    _require_git_id,
    _sole_parent,
)
from tools.check_m6_o006_command_lane_completion_v2 import (  # noqa: E402
    check_m6_o006_command_lane_completion_v2,
)
from tools.check_o007a_deployed_sink_closure_v2 import (  # noqa: E402
    check_o007a_deployed_sink_closure_v2,
)
from tools.m6_cross_language_sinks.inventory import (  # noqa: E402
    MANIFEST_SCHEMA,
    build_cross_language_projection,
    compare_projection_to_manifest,
)
from tools.o007a_deployed_sink_closure_v2 import O007AClosureRejectV2  # noqa: E402
from tools.o007b_cross_language_sink_closure_v3 import (  # noqa: E402
    O007BClosureRejectV3,
    SourcePinV3,
    StageASnapshotV3,
    build_artifact_v3,
    canonical_json_bytes_v3,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
JSON_OUTPUT = Path(c.ARTIFACT_PATH_V3)
MANIFEST_OUTPUT = Path(c.MANIFEST_PATH_V3)
MAX_SOURCE_BYTES_V3 = 16 * 1024 * 1024
MAX_ARTIFACT_BYTES_V3 = 1024 * 1024
MAX_MANIFEST_BYTES_V3 = 2 * 1024 * 1024
_GIT_ID_RE = re.compile(r"[0-9a-f]{40}\Z")


class SourceBindingModeV3(Enum):
    GIT_AND_WORKTREE = "GIT_AND_WORKTREE"
    GIT_ONLY = "GIT_ONLY"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise O007BClosureRejectV3(code, path, detail)


def _require_absent(root: Path, commit: str, path: str, code: str) -> None:
    _status, stdout, stderr = _run_git_v1(
        root, ("ls-tree", "-z", "--full-tree", commit, "--", path)
    )
    if stdout or stderr:
        _reject(code, path, "path must be absent")


def _pin(root: Path, commit: str, path: str) -> tuple[SourcePinV3, bytes]:
    recorded, mode, kind, blob = _git_tree_entry_v1(root, commit, path)
    if recorded != path or mode not in {"100644", "100755"} or kind != "blob":
        _reject("SOURCE_GIT_ENTRY", path, "must be an exact regular Git blob")
    raw = _read_git_blob(root, blob, MAX_SOURCE_BYTES_V3, path)
    return (
        SourcePinV3(
            path=path,
            git_blob_sha=blob,
            git_mode=mode,
            sha256=hashlib.sha256(raw).hexdigest(),
            size_bytes=len(raw),
        ),
        raw,
    )


def _require_v2_preserved(root: Path, stage_a: str) -> None:
    for path in c.V2_PRESERVED_PATHS:
        base_entry = _git_tree_entry_v1(root, c.BASE_COMMIT_V3, path)
        stage_entry = _git_tree_entry_v1(root, stage_a, path)
        if base_entry != stage_entry:
            _reject("V2_BYTE_DRIFT", path, "V2 Git entry differs from the exact base")


def _validate_stage_topology(root: Path, stage_a: str) -> str:
    if _git_tree_v1(root, c.BASE_COMMIT_V3) != c.BASE_TREE_V3:
        _reject("BASE_TREE", c.BASE_COMMIT_V3, "canonical base tree drift")
    if _sole_parent(root, stage_a) != c.BASE_COMMIT_V3:
        _reject("BASE_NOT_DIRECT_PARENT", stage_a, "Stage A must directly follow base")
    stage_tree = _require_git_id(_git_tree_v1(root, stage_a), "stage_a_tree")
    expected_delta = tuple(("A", path) for path in c.STAGE_A_SOURCE_PATHS_V3)
    if _delta(root, stage_a) != expected_delta:
        _reject("STAGE_A_DELTA", stage_a, "Stage A must add only declared V3 paths")
    _require_absent(root, stage_a, c.ARTIFACT_PATH_V3, "STAGE_A_ARTIFACT")
    for path in c.STAGE_A_SOURCE_PATHS_V3:
        _require_absent(root, c.BASE_COMMIT_V3, path, "BASE_STAGE_A_SOURCE_PRESENT")
    _require_v2_preserved(root, stage_a)
    if not _git_is_ancestor_v1(root, c.PLAN_COMMIT_V3, stage_a):
        _reject("PLAN_ANCESTRY", c.PLAN_COMMIT_V3, "plan is not an ancestor")
    if not _git_is_ancestor_v1(root, c.ADMISSION_COMMIT_V3, stage_a):
        _reject("ADMISSION_ANCESTRY", c.ADMISSION_COMMIT_V3, "admission is not an ancestor")
    return stage_tree


def load_stage_a_snapshot_v3(
    root: Path | str = REPO_ROOT,
    stage_a_commit: str | None = None,
    *,
    source_binding: SourceBindingModeV3 = SourceBindingModeV3.GIT_AND_WORKTREE,
) -> StageASnapshotV3:
    if type(source_binding) is not SourceBindingModeV3:
        _reject("SOURCE_BINDING_MODE", "source_binding", "invalid mode")
    inert_root = _require_inert_path_v1(root, "O007B V3 Stage-A root")
    _non_promisor(inert_root)
    captured_head = _require_git_id(_git_head_v1(inert_root), "HEAD")
    stage_a = (
        captured_head if stage_a_commit is None else _require_git_id(stage_a_commit, "stage_a")
    )
    stage_tree = _validate_stage_topology(inert_root, stage_a)
    stage_rows = tuple(_pin(inert_root, stage_a, path) for path in c.STAGE_A_SOURCE_PATHS_V3)
    evidence_rows = tuple(
        _pin(inert_root, stage_a, path) for path in c.EVIDENCE_SOURCE_PATHS_V3
    )
    if source_binding is SourceBindingModeV3.GIT_AND_WORKTREE:
        if captured_head != stage_a:
            _reject("STAGE_A_NOT_HEAD", stage_a, "worktree binding requires Stage A at HEAD")
        for pin, expected in stage_rows + evidence_rows:
            current = _read_bounded_regular_file_v1(
                inert_root / pin.path, MAX_SOURCE_BYTES_V3, f"O007B V3 source {pin.path}"
            )
            if current != expected:
                _reject("STAGE_A_WORKTREE_BINDING", pin.path, "working bytes differ from Git")
    if _git_head_v1(inert_root) != captured_head:
        _reject("HEAD_CHANGED_DURING_CHECK", "HEAD", "head changed")
    return StageASnapshotV3(
        stage_a_commit=stage_a,
        stage_a_tree=stage_tree,
        stage_a_source_pins=tuple(row[0] for row in stage_rows),
        evidence_source_pins=tuple(row[0] for row in evidence_rows),
    )


def _require_dependency_checks(root: Path) -> tuple[dict[str, object], dict[str, object]]:
    o007a = check_o007a_deployed_sink_closure_v2(root)
    o006 = check_m6_o006_command_lane_completion_v2(root)
    c._require_dependency_reports(o007a, o006)
    return o007a, o006


def _manifest_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def render_review_manifest_v3(root: Path) -> dict[str, object]:
    return {
        "nonclaims": list(c.NONCLAIMS_V3),
        "projection": build_cross_language_projection(root),
        "review_status": "UNREVIEWED",
        "schema": MANIFEST_SCHEMA,
        "scope": (
            "O-007B V3 exact current subject at base "
            f"{c.BASE_COMMIT_V3}: every tracked Rust and Tau source; shell, Dockerfile, "
            "and generated Python sources; O-007A deployment-closure dynamic imports."
        ),
    }


def _load_reviewed_manifest_v3(root: Path) -> tuple[dict[str, Any], bytes]:
    raw = _read_bounded_regular_file_v1(
        root / MANIFEST_OUTPUT, MAX_MANIFEST_BYTES_V3, "O007B V3 review manifest"
    )

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                _reject("MANIFEST_DUPLICATE_KEY", c.MANIFEST_PATH_V3, key)
            result[key] = value
        return result

    try:
        value = json.loads(raw, object_pairs_hook=reject_duplicates)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject("MANIFEST_JSON", c.MANIFEST_PATH_V3, type(exc).__name__)
    if not isinstance(value, dict) or _manifest_bytes(value) != raw:
        _reject("MANIFEST_CANONICAL", c.MANIFEST_PATH_V3, "bytes must be canonical")
    return value, raw


def collect_inventory_evidence_v3(root: Path) -> dict[str, object]:
    projection = build_cross_language_projection(root)
    manifest, manifest_raw = _load_reviewed_manifest_v3(root)
    discovery = projection.get("discovery_findings")
    if not isinstance(discovery, list):
        _reject("PROJECTION_SHAPE", "discovery_findings", "must be a list")
    findings = sorted(set(str(item) for item in discovery))
    findings.extend(compare_projection_to_manifest(projection, manifest))
    findings = sorted(set(findings))
    dynamic = projection.get("dynamic_import_declarations")
    includes = projection.get("generated_include_owners")
    generated = projection.get("generated_python_owners")
    if not isinstance(dynamic, list) or not isinstance(includes, list) or not isinstance(
        generated, list
    ):
        _reject("PROJECTION_SHAPE", "inventory", "required row collection is absent")
    unresolved = sum(
        1 for row in dynamic if isinstance(row, dict) and row.get("target_status") == "UNRESOLVED"
    )
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
            "dynamic_import_declaration_count": len(dynamic),
            "generated_include_owner_count": len(includes),
            "generated_python_owner_count": len(generated),
            "manifest_sha256": hashlib.sha256(manifest_raw).hexdigest(),
            "report_findings": findings,
            "report_ok": not findings,
            "release_ready": False,
            "unresolved_dynamic_import_count": unresolved,
            "vm01_status": "OPEN",
        }
    )
    c._require_inventory(evidence)
    return evidence


def build_bytes_v3(root: Path, stage_a_commit: str | None = None) -> bytes:
    snapshot = load_stage_a_snapshot_v3(root, stage_a_commit)
    o007a, o006 = _require_dependency_checks(root)
    inventory = collect_inventory_evidence_v3(root)
    return canonical_json_bytes_v3(
        build_artifact_v3(
            snapshot,
            inventory=inventory,
            o007a_check=o007a,
            o006_check=o006,
        )
    )


def _write_unreviewed_manifest(root: Path) -> str:
    destination = root / MANIFEST_OUTPUT
    if destination.exists():
        _reject("MANIFEST_EXISTS", c.MANIFEST_PATH_V3, "refusing to overwrite")
    payload = _manifest_bytes(render_review_manifest_v3(root))
    _atomic_replace_regular_file_v1(destination, payload)
    return hashlib.sha256(payload).hexdigest()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--stage-a-commit")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write-review-manifest", action="store_true")
    args = parser.parse_args(argv)
    root = _require_inert_path_v1(args.root, "O007B V3 builder root")
    if args.write_review_manifest:
        if args.check or args.stage_a_commit is not None:
            parser.error("manifest generation cannot be combined with artifact options")
        print(_write_unreviewed_manifest(root))
        return 0
    payload = build_bytes_v3(root, args.stage_a_commit)
    destination = root / JSON_OUTPUT
    if args.check:
        current = _read_bounded_regular_file_v1(
            destination, MAX_ARTIFACT_BYTES_V3, "O007B V3 artifact"
        )
        if current != payload:
            _reject("ARTIFACT_STALE", c.ARTIFACT_PATH_V3, "working bytes differ")
    else:
        _atomic_replace_regular_file_v1(destination, payload)
    print(hashlib.sha256(payload).hexdigest())
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        O007BClosureRejectV3,
        O007AClosureRejectV2,
        ShellRejectV1,
        CommandLaneCompletionRejectV2,
    ) as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1) from exc
