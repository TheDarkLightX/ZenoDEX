"""Ordinary source/receipt topology conformance; synthetic commits grant no authority."""

from __future__ import annotations

import json
import subprocess
from dataclasses import replace
from pathlib import Path

import pytest

from tools import build_retired_tau_bridge_closure_v4 as builder
from tools import check_retired_tau_bridge_closure_v4 as checker
from tools import retired_tau_bridge_closure_v3 as legacy
from tools import retired_tau_bridge_closure_v4 as current


def _git(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-c", "core.hooksPath=/dev/null", *args], cwd=root, text=True,
        stderr=subprocess.PIPE,
    ).strip()


def _stage_a(root: Path) -> tuple[str, str]:
    _git(root, "init", "--quiet")
    _git(root, "config", "user.name", "Evidence fixture")
    _git(root, "config", "user.email", "fixture@example.invalid")
    (root / "source.txt").write_text("source fixture\n", encoding="utf-8")
    _git(root, "add", "source.txt")
    _git(root, "commit", "--quiet", "-m", "fixture source")
    return _git(root, "rev-parse", "HEAD"), _git(root, "rev-parse", "HEAD^{tree}")


def _stage_b(root: Path, *, extra: bool = False) -> tuple[str, str, bytes, str]:
    commit, tree = _stage_a(root)
    raw = legacy.canonical_json_bytes_v3({"evidence_subject": {"commit": commit, "tree": tree}})
    receipt = root / builder.OUTPUT_PATH
    receipt.parent.mkdir(parents=True)
    receipt.write_bytes(raw)
    _git(root, "add", builder.OUTPUT_PATH.as_posix())
    if extra:
        (root / "unrelated.txt").write_text("unrelated\n", encoding="utf-8")
        _git(root, "add", "unrelated.txt")
    _git(root, "commit", "--quiet", "-m", "fixture receipt")
    return commit, tree, raw, _git(root, "rev-parse", "HEAD")


def test_given_exact_added_receipt_then_topology_binds_sole_parent(tmp_path: Path) -> None:
    commit, tree, raw, head = _stage_b(tmp_path)
    assert checker.require_stage_b_topology_v4(
        tmp_path, raw=raw, evidence_commit=commit, evidence_tree=tree,
    ) == head
    assert checker._artifact_subject(raw) == (commit, tree)


def test_given_extra_stage_b_file_then_reject_exact_tree_delta(tmp_path: Path) -> None:
    commit, tree, raw, _ = _stage_b(tmp_path, extra=True)
    with pytest.raises(legacy.ClosureRejectV3) as failure:
        checker.require_stage_b_topology_v4(tmp_path, raw=raw, evidence_commit=commit, evidence_tree=tree)
    assert failure.value.code == "STAGE_B_TREE_DELTA"


def test_given_uncommitted_receipt_bytes_then_reject_binding(tmp_path: Path) -> None:
    commit, tree, raw, _ = _stage_b(tmp_path)
    with pytest.raises(legacy.ClosureRejectV3) as failure:
        checker.require_stage_b_topology_v4(tmp_path, raw=raw + b"\n", evidence_commit=commit, evidence_tree=tree)
    assert failure.value.code == "STAGE_B_ARTIFACT_BLOB"


def test_given_receipt_already_at_source_commit_then_generation_rejects(tmp_path: Path) -> None:
    _, _, _, head = _stage_b(tmp_path)
    with pytest.raises(legacy.ClosureRejectV3) as failure:
        builder.require_receipt_absent_at_stage_a(tmp_path, head)
    assert failure.value.code == "STAGE_A_RECEIPT_PRESENT"


@pytest.mark.parametrize("subject", [
    None,
    {"commit": "main", "tree": "1" * 40},
    {"commit": "0" * 40, "tree": "1" * 40, "extra": True},
    {"commit": 0, "tree": "1" * 40},
])
def test_subject_parser_requires_exact_git_identities(subject: object) -> None:
    raw = json.dumps({"evidence_subject": subject}).encode()
    with pytest.raises(legacy.ClosureRejectV3) as failure:
        checker._artifact_subject(raw)
    assert failure.value.code == "ARTIFACT_SUBJECT"


def _empty_qualification_snapshot() -> current.QualificationSnapshotV4:
    source = legacy.SourceSnapshotV3(commit="1" * 40, tree="2" * 40, files=(), discovery=None)
    snapshot = legacy.SubjectSnapshotV3(
        captured_head="1" * 40, rechecked_head="1" * 40, baseline=source, subject=source,
        baseline_is_subject_ancestor=True, subject_is_current_ancestor=True, current_discovery=None,
    )
    return current.QualificationSnapshotV4(
        current=snapshot, predecessor=snapshot, predecessor_artifact=b"fixture", extra_sources=(),
    )


def test_terminal_check_compares_current_and_extra_evidence() -> None:
    initial = _empty_qualification_snapshot()
    builder.require_terminal_snapshot_match_v4(initial, initial)
    with pytest.raises(legacy.ClosureRejectV3) as failure:
        builder.require_terminal_snapshot_match_v4(initial, replace(initial, predecessor_artifact=b"changed"))
    assert failure.value.code == "SUCCESSOR_INPUT_CHANGED"
    changed = replace(initial.current, captured_head="3" * 40)
    with pytest.raises(legacy.ClosureRejectV3) as failure:
        builder.require_terminal_snapshot_match_v4(initial, replace(initial, current=changed))
    assert failure.value.code == "HEAD_CHANGED"


def test_missing_real_receipt_is_a_non_authorizing_failure(tmp_path: Path) -> None:
    report = checker.check_retired_tau_bridge_closure_v4(tmp_path)
    assert report["ok"] is False
    assert report["closed_value_movement_gates"] == 0
    for field in ("production_authority", "release_authority", "settlement_authority", "value_movement_authority"):
        assert report[field] == "NONE"
