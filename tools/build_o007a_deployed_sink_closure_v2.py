#!/usr/bin/env python3
"""Build the source-bound O-007A Stage-B artifact from an exact Stage A."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import NoReturn

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import o007a_deployed_sink_closure_v2 as c  # noqa: E402
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
from tools.check_deployment_profiles import validate_profile_dir  # noqa: E402
from tools.check_m6_o006_command_lane_completion_v2 import (  # noqa: E402
    check_m6_o006_command_lane_completion_v2,
)
from tools.check_m6_value_sinks_v2 import check_m6_value_sinks_v2  # noqa: E402
from tools.check_value_movement_closure_ledger_v2 import (  # noqa: E402
    check_value_movement_closure_ledger_v2,
)
from tools.m6_value_sinks.launchers import _container_shell_scripts  # noqa: E402
from tools.o007a_deployed_sink_closure_v2 import (  # noqa: E402
    CurrentEvidenceV2,
    O007AClosureRejectV2,
    SourcePinV2,
    StageASnapshotV2,
    build_o007a_artifact_v2,
    canonical_root_v2,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
JSON_OUTPUT = Path(c.ARTIFACT_PATH_V2)
BUILD_SCHEMA_V2 = "zenodex/o007a-deployed-sink-closure-build/v2"
MAX_SOURCE_BYTES_V2 = 8 * 1024 * 1024
MAX_ARTIFACT_BYTES_V2 = 512 * 1024
_GIT_ID_RE = re.compile(r"[0-9a-f]{40}\Z")


class SourceBindingModeV2(Enum):
    GIT_AND_WORKTREE = "GIT_AND_WORKTREE"
    GIT_ONLY = "GIT_ONLY"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise O007AClosureRejectV2(code, path, detail)


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


@dataclass(frozen=True, slots=True)
class CommitExpectationV2:
    commit: str
    parent: str
    tree: str
    write_set: tuple[str, ...] | None = None


def _verify_commit(root: Path, expected_commit: CommitExpectationV2) -> None:
    if _sole_parent(root, expected_commit.commit) != expected_commit.parent:
        _reject("DONOR_PARENT", expected_commit.commit, "parent mismatch")
    if _git_tree_v1(root, expected_commit.commit) != expected_commit.tree:
        _reject("DONOR_TREE", expected_commit.commit, "tree mismatch")
    if expected_commit.write_set is not None:
        actual = _delta(root, expected_commit.commit)
        expected = tuple(("A", path) for path in expected_commit.write_set)
        if actual != expected:
            _reject("DONOR_WRITE_SET", expected_commit.commit, "exact write set mismatch")


def _verify_provenance_commits(root: Path) -> None:
    expectations = (
        CommitExpectationV2(
            c.SELECTED_DONOR_COMMIT_V2,
            c.SELECTED_DONOR_PARENT_V2,
            c.SELECTED_DONOR_TREE_V2,
            c.SELECTED_DONOR_WRITE_SET_V2,
        ),
        CommitExpectationV2(
            c.REJECTED_DONOR_COMMIT_V2,
            c.SELECTED_DONOR_PARENT_V2,
            c.REJECTED_DONOR_TREE_V2,
            c.REJECTED_DONOR_WRITE_SET_V2,
        ),
        CommitExpectationV2(
            c.REPAIR_DONOR_COMMIT_V2,
            c.REPAIR_DONOR_PARENT_V2,
            c.REPAIR_DONOR_TREE_V2,
            c.SELECTED_DONOR_WRITE_SET_V2,
        ),
        CommitExpectationV2(
            c.REJECTED_RECEIPT_COMMIT_V1,
            c.REPAIR_DONOR_COMMIT_V2,
            c.REJECTED_RECEIPT_TREE_V1,
        ),
    )
    for expectation in expectations:
        _verify_commit(root, expectation)


def _require_exact_repair_paths(root: Path, stage_a: str) -> None:
    for path in c.REPAIR_EXACT_PATHS_V2:
        stage_entry = _git_tree_entry_v1(root, stage_a, path)
        donor_entry = _git_tree_entry_v1(root, c.REPAIR_DONOR_COMMIT_V2, path)
        if stage_entry[1:] != donor_entry[1:]:
            _reject("REPAIR_DONOR_SOURCE_DRIFT", path, "Stage A differs from repair donor")


def _validate_stage_topology(root: Path, stage_a: str) -> str:
    if _git_tree_v1(root, c.BASE_COMMIT_V2) != c.BASE_TREE_V2:
        _reject("BASE_TREE", c.BASE_COMMIT_V2, "exact canonical base tree drift")
    if _sole_parent(root, stage_a) != c.BASE_COMMIT_V2:
        _reject("BASE_NOT_DIRECT_PARENT", stage_a, "Stage A must directly follow canonical base")
    stage_tree = _require_git_id(_git_tree_v1(root, stage_a), "stage_a_tree")
    expected_delta = tuple(("A", path) for path in c.STAGE_A_SOURCE_PATHS_V2)
    if _delta(root, stage_a) != expected_delta:
        _reject("STAGE_A_DELTA", stage_a, "Stage A must add only declared source paths")
    _require_absent(root, stage_a, c.ARTIFACT_PATH_V2, "STAGE_A_ARTIFACT")
    _require_absent(root, stage_a, c.REJECTED_ARTIFACT_PATH_V1, "REJECTED_V1_PRESENT")
    for path in c.STAGE_A_SOURCE_PATHS_V2:
        _require_absent(root, c.BASE_COMMIT_V2, path, "BASE_STAGE_A_SOURCE_PRESENT")
    if not _git_is_ancestor_v1(root, c.PLAN_COMMIT_V2, stage_a):
        _reject("PLAN_ANCESTRY", c.PLAN_COMMIT_V2, "active plan is not an ancestor")
    if not _git_is_ancestor_v1(root, c.ADMISSION_COMMIT_V2, stage_a):
        _reject(
            "ADMISSION_ANCESTRY",
            c.ADMISSION_COMMIT_V2,
            "admission is not an ancestor",
        )
    return stage_tree


def _require_worktree(root: Path, rows: tuple[tuple[SourcePinV2, bytes], ...]) -> None:
    for pin, expected in rows:
        actual = _read_bounded_regular_file_v1(
            root / pin.path, MAX_SOURCE_BYTES_V2, f"O007A source {pin.path}"
        )
        if actual != expected:
            _reject("STAGE_A_WORKTREE_BINDING", pin.path, "working bytes differ from Git")


def load_stage_a_snapshot_v2(
    root: Path | str = REPO_ROOT,
    stage_a_commit: str | None = None,
    *,
    source_binding: SourceBindingModeV2 = SourceBindingModeV2.GIT_AND_WORKTREE,
) -> StageASnapshotV2:
    if type(source_binding) is not SourceBindingModeV2:
        _reject("SOURCE_BINDING_MODE", "source_binding", "invalid mode")
    inert_root = _require_inert_path_v1(root, "O007A Stage-A root")
    _non_promisor(inert_root)
    captured_head = _require_git_id(_git_head_v1(inert_root), "HEAD")
    stage_a = (
        captured_head if stage_a_commit is None else _require_git_id(stage_a_commit, "stage_a")
    )
    stage_tree = _validate_stage_topology(inert_root, stage_a)
    _verify_provenance_commits(inert_root)
    _require_exact_repair_paths(inert_root, stage_a)
    stage_rows = tuple(_pin(inert_root, stage_a, path) for path in c.STAGE_A_SOURCE_PATHS_V2)
    evidence_rows = tuple(_pin(inert_root, stage_a, path) for path in c.EVIDENCE_SOURCE_PATHS_V2)
    all_rows = stage_rows + evidence_rows
    if source_binding is SourceBindingModeV2.GIT_AND_WORKTREE:
        if captured_head != stage_a:
            _reject("STAGE_A_NOT_HEAD", stage_a, "worktree binding requires Stage A at HEAD")
        _require_worktree(inert_root, all_rows)
        if (inert_root / c.REJECTED_ARTIFACT_PATH_V1).exists():
            _reject(
                "REJECTED_V1_WORKTREE_PRESENT",
                c.REJECTED_ARTIFACT_PATH_V1,
                "must be absent",
            )
    if _git_head_v1(inert_root) != captured_head:
        _reject("HEAD_CHANGED_DURING_CHECK", "HEAD", "head changed")
    return StageASnapshotV2(
        stage_a_commit=stage_a,
        stage_a_tree=stage_tree,
        stage_a_source_pins=tuple(pin for pin, _ in stage_rows),
        evidence_source_pins=tuple(pin for pin, _ in evidence_rows),
    )


def _launcher_source_paths(root: Path) -> tuple[str, ...]:
    paths: set[str] = set()
    install = root / "scripts/install_zenodex.sh"
    if install.is_file():
        paths.add("scripts/install_zenodex.sh")
    directory = root / "bin"
    if directory.is_dir():
        paths.update(
            path.relative_to(root).as_posix()
            for path in sorted(directory.iterdir())
            if path.is_file()
        )
    paths.update(
        path.relative_to(root).as_posix()
        for path in sorted(root.glob("Dockerfile*"))
        if path.is_file()
    )
    scripts, findings = _container_shell_scripts(root)
    if findings:
        _reject("LAUNCHER_SOURCE_FINDING", "container", str(findings[0]))
    paths.update(scripts)
    return tuple(sorted(paths))


def _closure_projection(root: Path) -> dict[str, object]:
    report = check_m6_value_sinks_v2(root)

    def root_of(key: str) -> str:
        return canonical_root_v2(report[key])

    def list_at(key: str) -> list[object]:
        value = report.get(key)
        if not isinstance(value, list):
            _reject("REPORT_SHAPE", f"report.{key}", "must be a list")
        return value

    return {
        "classified_identity_count": report["classified_identity_count"],
        "declared_closure_gap_count": len(list_at("declared_closure_gaps")),
        "declared_closure_gaps_root": root_of("declared_closure_gaps"),
        "decoded_launcher_count": len(list_at("decoded_launchers")),
        "decoded_launchers_root": root_of("decoded_launchers"),
        "findings_root": root_of("findings"),
        "manifest_sha256": hashlib.sha256(
            (root / "tools/m6_value_sink_manifest_v2.json").read_bytes()
        ).hexdigest(),
        "observed_occurrence_count": report["observed_occurrence_count"],
        "production_authority": report["production_authority"],
        "release_gap_count": len(list_at("release_gaps")),
        "release_gaps_root": root_of("release_gaps"),
        "release_ready": report["release_ready"],
        "report_ok": report["ok"],
        "report_sha256": canonical_root_v2(report),
        "sink_root": root_of("sinks"),
        "static_reachable_unscanned_module_count": len(
            list_at("static_reachable_unscanned_modules")
        ),
        "static_reachable_unscanned_modules_root": root_of("static_reachable_unscanned_modules"),
        "static_scanned_module_count": report["static_scanned_module_count"],
        "static_scanned_module_digests_root": root_of("static_scanned_module_digests"),
        "unmediated_static_writer_count": len(list_at("unmediated_static_writers")),
        "unmediated_static_writers_root": root_of("unmediated_static_writers"),
        "vm01_status": report["vm01_status"],
    }


def collect_current_evidence_v2(root: Path, snapshot: StageASnapshotV2) -> CurrentEvidenceV2:
    root = root.resolve(strict=True)
    paths = _launcher_source_paths(root)
    if paths != c.LAUNCHER_SOURCE_PATHS_V2:
        _reject("LAUNCHER_SOURCE_SET", "launcher_sources", "exact launcher set drift")
    pins = {pin.path: pin for pin in snapshot.evidence_source_pins}
    launcher_rows = tuple({"path": path, "sha256": pins[path].sha256} for path in paths)
    profiles = validate_profile_dir(root / "config/deploy")
    selected = [
        row for row in profiles["profiles"] if row["profile_id"] == c.SELECTED_PROFILE_ID_V2
    ]
    expected_profile_path = str((root / c.SELECTED_PROFILE_PATH_V2).resolve())
    if (
        profiles["ok"] is not True
        or len(selected) != 1
        or selected[0]["ok"] is not True
        or selected[0]["path"] != expected_profile_path
    ):
        _reject(
            "DEPLOYMENT_PROFILE",
            c.SELECTED_PROFILE_PATH_V2,
            "profile validation failed",
        )
    zenoctl = _read_bounded_regular_file_v1(
        root / "tools/zenoctl.py", MAX_SOURCE_BYTES_V2, "zenoctl profile selector"
    )
    if b'--deployment-profile", default="public-testnet"' not in zenoctl:
        _reject("PROFILE_SELECTOR", "tools/zenoctl.py", "default profile selector drift")
    o005b = check_value_movement_closure_ledger_v2(root)
    if not (
        o005b["ok"] is True
        and o005b["historical_valid"] is True
        and o005b["current_applicable"] is True
        and o005b["artifact_sha256"] == c.O005B_ARTIFACT_SHA256_V2
        and o005b["implementation_subject"] == c.O005B_SUBJECT_COMMIT_V2
        and o005b["closed_value_movement_gate_count"] == 0
    ):
        _reject("O005B_POINT_OF_USE", "O-005B", "current exact checker failed")
    o006 = check_m6_o006_command_lane_completion_v2(root)
    if not (
        o006["ok"] is True
        and o006["historical_valid"] is True
        and o006["current_applicable"] is True
        and o006["artifact_sha256"] == c.O006_ARTIFACT_SHA256_V2
        and o006["certificate_root"] == c.O006_CERTIFICATE_ROOT_V2
        and o006["vm_gates_closed"] == []
    ):
        _reject("O006_POINT_OF_USE", "O-006", "current exact checker failed")
    closure = _closure_projection(root)
    if closure != c.EXPECTED_CLOSURE_V2:
        _reject("CLOSURE_EVIDENCE_DRIFT", "deployment_closure", "current census drift")
    return CurrentEvidenceV2(closure=closure, launcher_sources=launcher_rows)


def build_artifact_v2(root: Path | str = REPO_ROOT, stage_a_commit: str | None = None) -> bytes:
    inert_root = _require_inert_path_v1(root, "O007A build root")
    snapshot = load_stage_a_snapshot_v2(inert_root, stage_a_commit)
    evidence = collect_current_evidence_v2(inert_root, snapshot)
    return build_o007a_artifact_v2(snapshot, evidence)


def _failure(
    exc: O007AClosureRejectV2 | ShellRejectV1 | CommandLaneCompletionRejectV2,
) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "current_applicable": False,
        "finding": {"code": exc.code, "detail": exc.detail, "path": exc.path},
        "historical_valid": False,
        "migration_authority": "NONE",
        "ok": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": BUILD_SCHEMA_V2,
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
            actual = _read_bounded_regular_file_v1(output, MAX_ARTIFACT_BYTES_V2, "O007A artifact")
            if actual != expected:
                _reject(
                    "ARTIFACT_DRIFT",
                    c.ARTIFACT_PATH_V2,
                    "artifact differs from Stage A",
                )
        else:
            _atomic_replace_regular_file_v1(output, expected)
        artifact = json.loads(expected)
        print(
            json.dumps(
                {
                    "artifact_sha256": hashlib.sha256(expected).hexdigest(),
                    "certificate_root": artifact["certificate_root"],
                    "ok": True,
                },
                sort_keys=True,
            )
        )
        return 0
    except (O007AClosureRejectV2, ShellRejectV1, CommandLaneCompletionRejectV2, OSError) as exc:
        if isinstance(exc, OSError):
            exc = O007AClosureRejectV2("FILESYSTEM_IO", str(args.root), type(exc).__name__)
        print(json.dumps(_failure(exc), sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
