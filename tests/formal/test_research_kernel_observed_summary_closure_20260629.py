from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_research_kernel_observed_summary_closure_20260629 import (
    OBSERVED_DOC,
    OBSERVED_REPORT,
    REPORT_JSON,
    TARGET_RISK_ATOM,
    ClosureError,
    _read_json,
    _read_text,
    build_report,
    validate_observed_summary_state,
)


ROOT = Path(__file__).resolve().parents[2]


def test_observed_summary_closure_report() -> None:
    report = build_report()
    closure = report["closure"]

    assert report["ok"] is True
    assert report["schema"] == "zenodex.research_kernel_observed_summary_closure_20260629.v1"
    assert closure["target_atom_id"] == TARGET_RISK_ATOM
    assert closure["closure_kind"] == "resolves"
    assert closure["edge_type"] == "SUPERSEDES"
    assert all(closure["checks"].values())

    edge = report["research_kernel_edges_to_add"][0]
    assert edge["target_atom_id"] == TARGET_RISK_ATOM
    assert edge["edge_type"] == "SUPERSEDES"
    assert edge["closure_kind"] == "resolves"


def test_observed_summary_non_claims_and_residual_frontier() -> None:
    report = build_report()
    non_claims = "\n".join(report["non_claims"]).lower()
    residual = "\n".join(report["residual_open_frontier"]).lower()

    assert "scoped ab observed-summary lean checker boundary" in non_claims
    assert "does not prove host/python emitter construction" in non_claims
    assert "does not prove python-to-lean refinement" in non_claims
    assert "json-canonicalization risks" in non_claims
    assert "no settlement" in non_claims
    assert "reserve-state observed-summary" in residual
    assert "n7 tau scope certificate" in residual
    assert "host/python emitter construction" in residual


def test_observed_summary_closure_rejects_missing_theorem_listing() -> None:
    source_report = _read_json(OBSERVED_REPORT)
    mutated = copy.deepcopy(source_report)
    mutated["new_lean_theorems"] = [
        theorem
        for theorem in source_report["new_lean_theorems"]
        if theorem != "strictSubsetInductionObservedSummary_validates"
    ]

    with pytest.raises(ClosureError, match="strictSubsetInductionObservedSummary_validates_listed"):
        validate_observed_summary_state(
            lean_text=_read_text("lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean"),
            doc_text=_read_text(OBSERVED_DOC),
            report=mutated,
        )


def test_observed_summary_closure_rejects_missing_observed_field_binding() -> None:
    lean_text = _read_text("lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean")
    mutated_lean = lean_text.replace(
        "summary.observedMaskCount = summary.table.masks.length",
        "summary.observedMaskCount = 0",
        1,
    )

    with pytest.raises(ClosureError, match="observed_mask_count_bound"):
        validate_observed_summary_state(
            lean_text=mutated_lean,
            doc_text=_read_text(OBSERVED_DOC),
            report=_read_json(OBSERVED_REPORT),
        )


def test_observed_summary_closure_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_research_kernel_observed_summary_closure_20260629.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["closure"]["target_atom_id"] == TARGET_RISK_ATOM
