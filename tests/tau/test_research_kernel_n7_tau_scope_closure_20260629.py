from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_research_kernel_n7_tau_scope_closure_20260629 import (
    REPORT_JSON,
    SOURCE_DOC,
    SOURCE_REPORT,
    TARGET_RISK_ATOM,
    ClosureError,
    _read_json,
    _read_text,
    build_report,
    validate_n7_tau_scope_state,
)


ROOT = Path(__file__).resolve().parents[2]


def test_n7_tau_scope_closure_report() -> None:
    report = build_report()
    closure = report["closure"]

    assert report["ok"] is True
    assert report["schema"] == "zenodex.research_kernel_n7_tau_scope_closure_20260629.v1"
    assert closure["target_atom_id"] == TARGET_RISK_ATOM
    assert closure["closure_kind"] == "resolves"
    assert closure["edge_type"] == "SUPERSEDES"
    assert all(closure["checks"].values())

    edge = report["research_kernel_edges_to_add"][0]
    assert edge["target_atom_id"] == TARGET_RISK_ATOM
    assert edge["edge_type"] == "SUPERSEDES"
    assert edge["closure_kind"] == "resolves"


def test_n7_tau_scope_non_claims_and_residual_frontier() -> None:
    report = build_report()
    non_claims = "\n".join(report["non_claims"]).lower()
    residual = "\n".join(report["residual_open_frontier"]).lower()

    assert "bounded n7 tau scope certificate" in non_claims
    assert "does not replace the host merkle verifier" in non_claims
    assert "does not prove python-to-lean refinement" in non_claims
    assert "does not prove child-frontier generation in lean" in non_claims
    assert "does not cover nonzero min_amount_out" in non_claims
    assert "no settlement" in non_claims
    assert "n7 bidirectional transition" in residual
    assert "reserve-state observed-summary" in residual
    assert "full subset-mask dp" in residual


def test_n7_tau_scope_closure_rejects_missing_tau_case() -> None:
    source_report = _read_json(SOURCE_REPORT)
    mutated = copy.deepcopy(source_report)
    mutated["tau"]["case_results"] = [
        case
        for case in source_report["tau"]["case_results"]
        if case["case_id"] != "linked_child_coverage_reject"
    ]

    with pytest.raises(ClosureError, match="linked_child_coverage_reject_case_present"):
        validate_n7_tau_scope_state(
            report=mutated,
            doc_text=_read_text(SOURCE_DOC),
        )


def test_n7_tau_scope_closure_rejects_missing_required_fact() -> None:
    source_report = _read_json(SOURCE_REPORT)
    mutated = copy.deepcopy(source_report)
    mutated["facts"]["transition_counts_complete"] = 0

    with pytest.raises(ClosureError, match="transition_counts_complete_present"):
        validate_n7_tau_scope_state(
            report=mutated,
            doc_text=_read_text(SOURCE_DOC),
        )


def test_n7_tau_scope_closure_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_research_kernel_n7_tau_scope_closure_20260629.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["closure"]["target_atom_id"] == TARGET_RISK_ATOM
