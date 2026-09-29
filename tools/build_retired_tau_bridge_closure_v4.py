#!/usr/bin/env python3
"""Build a source-pinned O-003B successor; stdout JSON, failures exit nonzero.

The predecessor is replayed from its immutable Git subject. Current sources
must already be committed as Stage A. This tool never commits or promotes them.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools import build_retired_tau_bridge_closure_v3 as acquisition  # noqa: E402
from tools import retired_tau_bridge_closure_v3 as legacy  # noqa: E402
from tools import retired_tau_bridge_closure_v4 as current  # noqa: E402
from tools.build_m6_normative_requirements_v1 import (  # noqa: E402
    ShellRejectV1,
    _atomic_replace_regular_file_v1,
    _git_head_v1,
    _git_is_ancestor_v1,
    _git_tree_v1,
    _read_bounded_regular_file_v1,
    _require_inert_path_v1,
    _run_git_v1,
)
from tools.check_retired_tau_bridge_closure_v3 import _require_stage_b_topology  # noqa: E402

OUTPUT_PATH = Path(current.OUTPUT_PATH_V4)


def _historical_predecessor(root: Path) -> tuple[legacy.SubjectSnapshotV3, bytes]:
    """Replay a Git-only historical subject, never label it current qualification."""
    raw = _read_bounded_regular_file_v1(
        root / legacy.OUTPUT_PATH_V3, legacy.MAX_ARTIFACT_BYTES_V3, "preserved V3 receipt"
    )
    _require_stage_b_topology(
        root, raw=raw, evidence_commit=current.PREDECESSOR_SUBJECT_V4,
        evidence_tree=_git_tree_v1(root, current.PREDECESSOR_SUBJECT_V4),
    )
    predecessor_file = acquisition._tree_source_file_v3(
        root, current.PREDECESSOR_COMMIT_V4, legacy.OUTPUT_PATH_V3
    )
    if raw != predecessor_file.data:
        raise legacy.ClosureRejectV3("PREDECESSOR_DRIFT", legacy.OUTPUT_PATH_V3, "preserved receipt changed")
    baseline_discovery = acquisition._git_python_discovery_v3(root, legacy.BASELINE_COMMIT_V3)
    subject_discovery = acquisition._git_python_discovery_v3(root, current.PREDECESSOR_SUBJECT_V4)
    baseline = legacy.SourceSnapshotV3(
        commit=legacy.BASELINE_COMMIT_V3, tree=_git_tree_v1(root, legacy.BASELINE_COMMIT_V3),
        files=tuple(acquisition._tree_source_file_v3(root, legacy.BASELINE_COMMIT_V3, p)
                    for p in legacy.BASELINE_PIN_PATHS_V3), discovery=baseline_discovery,
    )
    subject = legacy.SourceSnapshotV3(
        commit=current.PREDECESSOR_SUBJECT_V4,
        tree=_git_tree_v1(root, current.PREDECESSOR_SUBJECT_V4),
        files=tuple(acquisition._tree_source_file_v3(root, current.PREDECESSOR_SUBJECT_V4, p)
                    for p in legacy.SUBJECT_PIN_PATHS_V3), discovery=subject_discovery,
    )
    return legacy.SubjectSnapshotV3(
        captured_head=subject.commit, rechecked_head=subject.commit,
        baseline=baseline, subject=subject,
        baseline_is_subject_ancestor=_git_is_ancestor_v1(root, baseline.commit, subject.commit),
        subject_is_current_ancestor=True, current_discovery=subject_discovery,
    ), raw


def load_subject_snapshot_v4(
    root: Path | str, *, evidence_commit: str | None = None,
) -> current.QualificationSnapshotV4:
    """Acquire exact Git/worktree bytes using the unchanged bounded V3 readers."""
    inert_root = _require_inert_path_v1(root, "O-003B V4 root")
    captured = acquisition.load_subject_snapshot_v3(inert_root, evidence_commit=evidence_commit)
    predecessor, raw = _historical_predecessor(inert_root)
    extras = tuple(acquisition._subject_source_file_v3(
        inert_root, captured_head=captured.captured_head,
        subject_commit=captured.subject.commit, path=path,
    ) for path in current.EXTRA_PIN_PATHS_V4)
    if not _git_is_ancestor_v1(inert_root, current.PREDECESSOR_COMMIT_V4, captured.subject.commit):
        raise legacy.ClosureRejectV3("PREDECESSOR_ANCESTRY", "Git", "successor must descend from V3 receipt")
    if _git_head_v1(inert_root) != captured.captured_head:
        raise legacy.ClosureRejectV3("HEAD_CHANGED", "Git", "HEAD changed during successor acquisition")
    return current.QualificationSnapshotV4(
        current=captured, predecessor=predecessor, predecessor_artifact=raw, extra_sources=extras,
    )


def require_terminal_snapshot_match_v4(
    initial: current.QualificationSnapshotV4, terminal: current.QualificationSnapshotV4,
) -> None:
    legacy.require_terminal_snapshot_match_v3(
        initial.current, terminal.current, expected_head=initial.current.captured_head,
    )
    if initial != terminal:
        raise legacy.ClosureRejectV3("SUCCESSOR_INPUT_CHANGED", "terminal replay", "successor inputs changed")


def require_receipt_absent_at_stage_a(root: Path, commit: str) -> None:
    code, output, error = _run_git_v1(root, ("ls-tree", commit, "--", OUTPUT_PATH.as_posix()))
    if code != 0 or error or output:
        raise legacy.ClosureRejectV3("STAGE_A_RECEIPT_PRESENT", OUTPUT_PATH.as_posix(), "receipt must be absent at Stage A")


def build_certificate_v4(root: Path | str) -> bytes:
    inert_root = _require_inert_path_v1(root, "O-003B V4 build root")
    identity = acquisition._repository_root_identity_v3(inert_root)
    snapshot = load_subject_snapshot_v4(inert_root)
    require_receipt_absent_at_stage_a(inert_root, snapshot.current.subject.commit)
    raw = current.build_artifact_v4(snapshot)
    terminal = load_subject_snapshot_v4(inert_root, evidence_commit=snapshot.current.subject.commit)
    require_terminal_snapshot_match_v4(snapshot, terminal)
    if acquisition._repository_root_identity_v3(inert_root) != identity:
        raise legacy.ClosureRejectV3("ROOT_CHANGED", "repository root", "root changed during generation")
    if _git_head_v1(inert_root) != snapshot.current.captured_head:
        raise legacy.ClosureRejectV3("HEAD_CHANGED", "Git", "HEAD changed before generation return")
    return raw


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    if args.check:
        from tools.check_retired_tau_bridge_closure_v4 import check_retired_tau_bridge_closure_v4

        report = check_retired_tau_bridge_closure_v4(args.root)
        print(json.dumps(report, sort_keys=True))
        return 0 if report["ok"] is True else 1
    try:
        root = _require_inert_path_v1(args.root, "O-003B V4 output root")
        raw = build_certificate_v4(root)
        _atomic_replace_regular_file_v1(root / OUTPUT_PATH, raw)
        print(json.dumps({
            "ok": True, "artifact": OUTPUT_PATH.as_posix(),
            "artifact_sha256": hashlib.sha256(raw).hexdigest(),
            "schema": "zenodex/retired-tau-bridge-closure-build/v4",
            "production_authority": "NONE", "release_authority": "NONE",
            "settlement_authority": "NONE", "value_movement_authority": "NONE",
            "closed_value_movement_gates": 0,
        }, sort_keys=True))
        return 0
    except (legacy.ClosureRejectV3, ShellRejectV1) as exc:
        report = current.failure_report_v4(legacy.ClosureRejectV3(exc.code, exc.path, exc.detail))
        print(json.dumps(report, sort_keys=True))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
