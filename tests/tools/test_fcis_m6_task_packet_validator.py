from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from docs.research.m6_tasks import validate_task_packet as validator

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / "docs" / "research" / "m6_tasks"
J07_EVIDENCE = PACKET / "TASK_J07_EVIDENCE.json"
J07_MANIFEST = PACKET / "TASK_J07_SOURCE_MANIFEST.sha256"

REQUIRED_J07_AUTHORITY_PATHS = frozenset(
    {
        "experiments/fcis_m6_j07_authority_switch_check.py",
        "experiments/fcis_m6_tau_j07_writer_authority_check.py",
        "formal/tau/m6_tau_placement_frontier_v1.json",
        "docs/research/FCIS_M6_TAU_PLACEMENT_FRONTIER_20260803.md",
        "docs/research/m6_tasks/TASK_J07_TAU_WRITER_AUTHORITY_V2.json",
        "src/core/fcis_m6_j07_authority_switch.py",
        "src/core/fcis_m6_j07_writer_admission_v2.py",
        "src/core/fcis_m6_j07_writer_token_v3.py",
        "src/core/fcis_m6_writer_profile_eligibility_v1.py",
        "src/integration/fcis_m6_tau_j07_writer_eligibility_v1.py",
        "tests/core/test_fcis_m6_j07_authority_switch.py",
        "tests/core/test_fcis_m6_j07_authority_switch_properties.py",
        "tests/core/test_fcis_m6_j07_writer_admission_v2.py",
        "tests/integration/test_fcis_m6_tau_j07_writer_eligibility_v1.py",
        "tests/tools/test_fcis_m6_task_packet_validator.py",
        "tools/build_fcis_m6_j07_authority_switch.py",
    }
)


def _git(*arguments: str) -> str:
    return subprocess.check_output(
        ["git", *arguments],
        cwd=ROOT,
        text=True,
    ).strip()


def test_j07_packet_covers_the_live_writer_admission_authority_surface() -> None:
    evidence = json.loads(J07_EVIDENCE.read_text(encoding="utf-8"))
    manifest_paths = {
        line.split()[1]
        for line in J07_MANIFEST.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    assert REQUIRED_J07_AUTHORITY_PATHS <= set(evidence["evidence_files"])
    assert REQUIRED_J07_AUTHORITY_PATHS <= set(evidence["source_hashes"])
    assert REQUIRED_J07_AUTHORITY_PATHS <= manifest_paths


def test_zero_commit_and_foreign_tree_mutants_fail_closed() -> None:
    head = _git("rev-parse", "HEAD")
    head_tree = _git("show", "-s", "--format=%T", head)
    parent = _git("rev-parse", "HEAD^")
    parent_tree = _git("show", "-s", "--format=%T", parent)
    assert head_tree != parent_tree

    with pytest.raises(SystemExit, match="Git identity resolution failed"):
        validator._validate_commit_tree(
            ROOT,
            "0" * 40,
            head_tree,
            "source_head",
        )

    with pytest.raises(SystemExit, match="commit/tree mismatch"):
        validator._validate_commit_tree(ROOT, head, parent_tree, "source_head")


def test_report_and_evidence_identity_mismatch_is_rejected() -> None:
    evidence = json.loads(J07_EVIDENCE.read_text(encoding="utf-8"))
    report = (PACKET / "TASK_J07_REPORT.md").read_text(encoding="utf-8")
    report_identities = validator._validate_report(report, "J07")
    foreign_identity = report_identities["BASE_SHA"]
    evidence["source_head_sha"] = foreign_identity

    with pytest.raises(SystemExit, match="report/evidence identity mismatch"):
        validator._validate_report_bindings(report_identities, evidence)

    evidence["source_head_sha"] = report_identities["SOURCE_HEAD_SHA"]
    evidence["results"]["implementation_commit"] = foreign_identity
    with pytest.raises(SystemExit, match="report/evidence identity mismatch"):
        validator._validate_report_bindings(report_identities, evidence)


def test_expected_packet_head_requires_declared_commit_ancestry() -> None:
    head = _git("rev-parse", "HEAD")
    validator._validate_packet(
        PACKET,
        ROOT,
        J07_EVIDENCE,
        expected_head=head,
    )

    implementation_parent = json.loads(J07_EVIDENCE.read_text(encoding="utf-8"))["results"][
        "implementation_parent"
    ]
    with pytest.raises(SystemExit, match="not an ancestor"):
        validator._validate_packet(
            PACKET,
            ROOT,
            J07_EVIDENCE,
            expected_head=implementation_parent,
        )
