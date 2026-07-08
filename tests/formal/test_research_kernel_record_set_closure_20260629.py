from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_research_kernel_record_set_closure_20260629 import (
    EXPECTED_REPLAY_HASH,
    REPORT_JSON,
    TARGET_RISK_ATOM,
    ClosureError,
    _load_generated_audit_report,
    _validate_audit_report,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


def test_record_set_closure_report() -> None:
    report = build_report()
    closure = report["closure"]

    assert report["ok"] is True
    assert report["schema"] == "zenodex.research_kernel_record_set_closure_20260629.v1"
    assert closure["target_atom_id"] == TARGET_RISK_ATOM
    assert closure["closure_kind"] == "resolves"
    assert closure["edge_type"] == "SUPERSEDES"
    assert closure["audit_deterministic_replay_hash"] == EXPECTED_REPLAY_HASH
    assert all(closure["checks"].values())

    edge = report["research_kernel_edges_to_add"][0]
    assert edge["target_atom_id"] == TARGET_RISK_ATOM
    assert edge["edge_type"] == "SUPERSEDES"
    assert edge["closure_kind"] == "resolves"


def test_record_set_closure_non_claims_and_residual_frontier() -> None:
    report = build_report()
    non_claims = "\n".join(report["non_claims"]).lower()
    residual = "\n".join(report["residual_open_frontier"]).lower()

    assert "closes only the rk tracking risk" in non_claims
    assert "does not prove python-to-lean refinement" in non_claims
    assert "does not construct a subset dp table" in non_claims
    assert "does not cover nonzero min_amount_out" in non_claims
    assert "no settlement" in non_claims
    assert "observed-summary" in residual
    assert "full subset-mask" in residual


def test_record_set_closure_rejects_stale_replay_hash() -> None:
    audit_report = _load_generated_audit_report()
    mutated = copy.deepcopy(audit_report)
    mutated["deterministic_replay"]["first_hash"] = "0" * 64

    with pytest.raises(ClosureError, match="first_replay_hash_ok"):
        _validate_audit_report(mutated)


def test_record_set_closure_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_research_kernel_record_set_closure_20260629.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["closure"]["target_atom_id"] == TARGET_RISK_ATOM
