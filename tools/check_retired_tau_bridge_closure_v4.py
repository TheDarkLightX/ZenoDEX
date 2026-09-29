#!/usr/bin/env python3
"""Check exact-subject successor evidence; JSON stdout, 0 pass and 1 refusal."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools import retired_tau_bridge_closure_v3 as legacy  # noqa: E402
from tools import retired_tau_bridge_closure_v4 as current  # noqa: E402
from tools.build_m6_normative_requirements_v1 import (  # noqa: E402
    ShellRejectV1,
    _git_head_v1,
    _git_is_ancestor_v1,
    _git_scalar_v1,
    _git_tree_entry_v1,
    _git_tree_v1,
    _read_bounded_regular_file_v1,
    _require_inert_path_v1,
    _run_git_v1,
)
from tools.build_retired_tau_bridge_closure_v3 import _repository_root_identity_v3  # noqa: E402
from tools.build_retired_tau_bridge_closure_v4 import (  # noqa: E402
    OUTPUT_PATH,
    load_subject_snapshot_v4,
    require_receipt_absent_at_stage_a,
    require_terminal_snapshot_match_v4,
)


def _artifact_subject(raw: bytes) -> tuple[str, str]:
    try:
        artifact = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise legacy.ClosureRejectV3("ARTIFACT_JSON", "artifact", type(exc).__name__) from exc
    subject = artifact.get("evidence_subject") if type(artifact) is dict else None
    if type(subject) is not dict or set(subject) != {"commit", "tree"}:
        raise legacy.ClosureRejectV3("ARTIFACT_SUBJECT", "artifact", "exact commit/tree subject required")
    commit, tree = subject["commit"], subject["tree"]
    if any(type(value) is not str or re.fullmatch(r"[0-9a-f]{40}", value) is None for value in (commit, tree)):
        raise legacy.ClosureRejectV3("ARTIFACT_SUBJECT", "artifact", "exact Git object identities required")
    return commit, tree


def require_stage_b_topology_v4(
    root: Path, *, raw: bytes, evidence_commit: str, evidence_tree: str,
) -> str:
    """Bind one new receipt to the immediately preceding committed source."""
    head = _git_head_v1(root)
    artifact_commit = _git_scalar_v1(
        root, ("log", "-1", "--format=%H", "--", OUTPUT_PATH.as_posix()), "V4 receipt commit",
    )
    if not _git_is_ancestor_v1(root, artifact_commit, head):
        raise legacy.ClosureRejectV3("STAGE_B_ANCESTRY", artifact_commit, "receipt is off current lineage")
    parents = _git_scalar_v1(
        root, ("rev-list", "--parents", "-n", "1", artifact_commit), "V4 receipt parents",
    ).split()[1:]
    if parents != [evidence_commit]:
        raise legacy.ClosureRejectV3("STAGE_B_PARENT_MISMATCH", artifact_commit, "Stage A must be sole parent")
    if _git_tree_v1(root, evidence_commit) != evidence_tree:
        raise legacy.ClosureRejectV3("EVIDENCE_TREE", evidence_commit, "Stage A tree changed")
    require_receipt_absent_at_stage_a(root, evidence_commit)
    code, changed, error = _run_git_v1(
        root, ("diff-tree", "--no-commit-id", "--name-status", "-r", evidence_commit, artifact_commit),
    )
    if code != 0 or error or changed.splitlines() != [f"A\t{OUTPUT_PATH.as_posix()}"]:
        raise legacy.ClosureRejectV3("STAGE_B_TREE_DELTA", artifact_commit, "Stage B must only add V4 receipt")
    receipt_entry = _git_tree_entry_v1(root, artifact_commit, OUTPUT_PATH.as_posix())
    if receipt_entry != _git_tree_entry_v1(root, head, OUTPUT_PATH.as_posix()):
        raise legacy.ClosureRejectV3("STAGE_B_ARTIFACT_ENTRY", OUTPUT_PATH.as_posix(), "receipt entry changed")
    path, mode, kind, blob = receipt_entry
    if path != OUTPUT_PATH.as_posix() or mode != "100644" or kind != "blob":
        raise legacy.ClosureRejectV3("STAGE_B_ARTIFACT_ENTRY", path, "regular non-executable receipt required")
    if legacy._git_blob_sha(raw) != blob:
        raise legacy.ClosureRejectV3("STAGE_B_ARTIFACT_BLOB", path, "working receipt differs from commit")
    return head


def check_retired_tau_bridge_closure_v4(root: Path | str = REPO_ROOT) -> dict[str, object]:
    try:
        inert_root = _require_inert_path_v1(root, "O-003B V4 checker root")
        identity = _repository_root_identity_v3(inert_root)
        raw = _read_bounded_regular_file_v1(
            inert_root / OUTPUT_PATH, legacy.MAX_ARTIFACT_BYTES_V3, "V4 receipt",
        )
        commit, tree = _artifact_subject(raw)
        head = require_stage_b_topology_v4(inert_root, raw=raw, evidence_commit=commit, evidence_tree=tree)
        snapshot = load_subject_snapshot_v4(inert_root, evidence_commit=commit)
        if snapshot.current.captured_head != head:
            raise legacy.ClosureRejectV3("HEAD_CHANGED", head, "HEAD changed after topology check")
        report = current.check_artifact_v4(raw, snapshot)
        terminal = load_subject_snapshot_v4(inert_root, evidence_commit=commit)
        require_terminal_snapshot_match_v4(snapshot, terminal)
        terminal_raw = _read_bounded_regular_file_v1(
            inert_root / OUTPUT_PATH, legacy.MAX_ARTIFACT_BYTES_V3, "V4 terminal receipt",
        )
        if terminal_raw != raw:
            raise legacy.ClosureRejectV3("STAGE_B_ARTIFACT_CHANGED", OUTPUT_PATH.as_posix(), "receipt changed")
        if _repository_root_identity_v3(inert_root) != identity:
            raise legacy.ClosureRejectV3("ROOT_CHANGED", "repository root", "root changed before acceptance")
        if _git_head_v1(inert_root) != head:
            raise legacy.ClosureRejectV3("HEAD_CHANGED", head, "HEAD changed before acceptance")
        return {**report, "observed_head": head, "observed_tree": _git_tree_v1(inert_root, head)}
    except (legacy.ClosureRejectV3, ShellRejectV1) as exc:
        return current.failure_report_v4(legacy.ClosureRejectV3(exc.code, exc.path, exc.detail))
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        return current.failure_report_v4(legacy.ClosureRejectV3("CHECKER_INPUT_ERROR", type(exc).__name__, "fail closed"))
    except Exception:
        # This is a release checker; an unexpected internal failure grants nothing.
        return current.failure_report_v4(legacy.ClosureRejectV3("CHECKER_INTERNAL_ERROR", "internal", "fail closed"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    report = check_retired_tau_bridge_closure_v4(parser.parse_args(argv).root)
    print(json.dumps(report, sort_keys=True))
    return 0 if report.get("schema") == current.CHECK_SCHEMA_V4 and report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
