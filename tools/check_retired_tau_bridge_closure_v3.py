#!/usr/bin/env python3
"""Fail closed when the exact-subject O-003B V3 certificate drifts."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

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
from tools.build_retired_tau_bridge_closure_v3 import (  # noqa: E402
    OUTPUT_PATH,
    load_subject_snapshot_v3,
)
from tools.retired_tau_bridge_closure_v3 import (  # noqa: E402
    CHECK_SCHEMA_V3,
    MAX_ARTIFACT_BYTES_V3,
    ClosureRejectV3,
    _git_blob_sha,
    check_artifact_v3,
    failure_report_v3,
)


def _artifact_subject(raw: bytes) -> tuple[str, str]:
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ClosureRejectV3("ARTIFACT_JSON", "artifact", type(exc).__name__) from exc
    if type(value) is not dict or type(value.get("evidence_subject")) is not dict:
        raise ClosureRejectV3("ARTIFACT_SUBJECT", "artifact", "evidence subject missing")
    commit = value["evidence_subject"].get("commit")
    tree = value["evidence_subject"].get("tree")
    if type(commit) is not str or type(tree) is not str:
        raise ClosureRejectV3("ARTIFACT_SUBJECT", "artifact", "commit/tree missing")
    return commit, tree


def _require_stage_b_topology(
    root: Path,
    *,
    raw: bytes,
    evidence_commit: str,
    evidence_tree: str,
) -> tuple[str, str]:
    captured_head = _git_head_v1(root)
    artifact_commit = _git_scalar_v1(
        root,
        ("log", "-1", "--format=%H", "--", OUTPUT_PATH.as_posix()),
        "O-003B artifact commit",
    )
    if not _git_is_ancestor_v1(root, artifact_commit, captured_head):
        raise ClosureRejectV3(
            "STAGE_B_ANCESTRY",
            artifact_commit,
            "artifact commit is off current lineage",
        )
    parent_line = _git_scalar_v1(
        root,
        ("rev-list", "--parents", "-n", "1", artifact_commit),
        "O-003B artifact parents",
    )
    parents = parent_line.split()[1:]
    if len(parents) != 1:
        raise ClosureRejectV3(
            "STAGE_B_PARENT_CARDINALITY",
            artifact_commit,
            f"expected one parent, observed {len(parents)}",
        )
    if parents[0] != evidence_commit:
        raise ClosureRejectV3(
            "STAGE_B_PARENT_MISMATCH",
            artifact_commit,
            "artifact commit parent differs from Stage-A evidence subject",
        )
    if _git_tree_v1(root, evidence_commit) != evidence_tree:
        raise ClosureRejectV3("EVIDENCE_TREE", evidence_commit, "Stage-A tree drift")
    _, changed, stderr = _run_git_v1(
        root,
        (
            "diff-tree",
            "--no-commit-id",
            "--name-status",
            "-r",
            evidence_commit,
            artifact_commit,
        ),
    )
    changed_rows = tuple(line for line in changed.splitlines() if line)
    expected_change = (f"A\t{OUTPUT_PATH.as_posix()}",)
    if stderr or changed_rows != expected_change:
        raise ClosureRejectV3(
            "STAGE_B_TREE_DELTA",
            artifact_commit,
            f"expected {expected_change!r}, observed {changed_rows!r}",
        )
    artifact_entry = _git_tree_entry_v1(root, artifact_commit, OUTPUT_PATH.as_posix())
    current_entry = _git_tree_entry_v1(root, captured_head, OUTPUT_PATH.as_posix())
    if artifact_entry != current_entry:
        raise ClosureRejectV3(
            "STAGE_B_ARTIFACT_ENTRY",
            OUTPUT_PATH.as_posix(),
            "current artifact entry differs from the Stage-B receipt commit",
        )
    entry_path, mode, object_type, blob_sha = artifact_entry
    if entry_path != OUTPUT_PATH.as_posix() or mode != "100644" or object_type != "blob":
        raise ClosureRejectV3(
            "STAGE_B_ARTIFACT_ENTRY",
            OUTPUT_PATH.as_posix(),
            "artifact must be one regular non-executable Git blob",
        )
    if _git_blob_sha(raw) != blob_sha:
        raise ClosureRejectV3(
            "STAGE_B_ARTIFACT_BLOB",
            OUTPUT_PATH.as_posix(),
            "working artifact bytes differ from the committed Stage-B blob",
        )
    return captured_head, _git_tree_v1(root, captured_head)


def check_retired_tau_bridge_closure_v3(
    root: Path | str = REPO_ROOT,
) -> dict[str, object]:
    try:
        inert_root = _require_inert_path_v1(root, "O-003B V3 checker root")
        raw = _read_bounded_regular_file_v1(
            inert_root / OUTPUT_PATH,
            MAX_ARTIFACT_BYTES_V3,
            "O-003B V3 certificate",
        )
        evidence_commit, evidence_tree = _artifact_subject(raw)
        observed_head, observed_tree = _require_stage_b_topology(
            inert_root,
            raw=raw,
            evidence_commit=evidence_commit,
            evidence_tree=evidence_tree,
        )
        snapshot = load_subject_snapshot_v3(
            inert_root,
            evidence_commit=evidence_commit,
        )
        if (
            snapshot.captured_head != observed_head
            or snapshot.rechecked_head != observed_head
        ):
            raise ClosureRejectV3(
                "HEAD_CHANGED",
                observed_head,
                "HEAD changed between Stage-B topology and source capture",
            )
        report = check_artifact_v3(raw, snapshot)
        if _git_head_v1(inert_root) != observed_head:
            raise ClosureRejectV3(
                "HEAD_CHANGED",
                observed_head,
                "HEAD changed before terminal checker acceptance",
            )
        return {
            **report,
            "observed_head": observed_head,
            "observed_tree": observed_tree,
        }
    except ClosureRejectV3 as exc:
        return failure_report_v3(exc)
    except ShellRejectV1 as exc:
        return failure_report_v3(ClosureRejectV3(exc.code, exc.path, exc.detail))
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        return failure_report_v3(
            ClosureRejectV3("CHECKER_INPUT_ERROR", type(exc).__name__, "fail-closed input")
        )
    except Exception:
        return failure_report_v3(
            ClosureRejectV3("CHECKER_INTERNAL_ERROR", "internal", "unexpected failure")
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    report = check_retired_tau_bridge_closure_v3(parser.parse_args(argv).root)
    if report.get("schema") != CHECK_SCHEMA_V3:
        report = {**report, "ok": False}
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
