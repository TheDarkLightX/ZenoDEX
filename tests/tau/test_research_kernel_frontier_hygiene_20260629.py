from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_research_kernel_frontier_hygiene_20260629 import (
    REPORT_JSON,
    build_report,
    closure_specs,
    open_frontier_specs,
)


ROOT = Path(__file__).resolve().parents[2]


def _require_generated_prerequisites() -> None:
    missing = [spec.report_path for spec in closure_specs() if not (ROOT / spec.report_path).exists()]
    if missing:
        pytest.skip(
            "generated prerequisite reports are absent; run "
            "`python3 tools/check_research_kernel_frontier_hygiene_20260629.py --refresh`"
        )


def test_research_kernel_frontier_hygiene_report() -> None:
    _require_generated_prerequisites()

    report = build_report()

    assert report["ok"] is True
    assert report["schema"] == "zenodex.research_kernel_frontier_hygiene_20260629.v1"
    assert report["closure_count"] == 4
    assert report["open_frontier_count"] == 5
    assert report["resolved_count"] == 2
    assert report["specialized_count"] == 2
    assert all(row["closed"] for row in report["closures"])

    by_atom = {row["frontier_atom_id"]: row for row in report["closures"]}
    assert by_atom["atom_ef1f5b6ebed246eb"]["closure_kind"] == "resolves"
    assert by_atom["atom_d64b2781e6604d77"]["closure_kind"] == "resolves"
    assert by_atom["atom_e4b9b11387894204"]["closure_kind"] == "specializes"
    assert by_atom["atom_41092f7feb7f4df8"]["closure_kind"] == "specializes"

    open_atoms = {row["frontier_atom_id"] for row in report["open_frontier"]}
    assert open_atoms == {spec.frontier_atom_id for spec in open_frontier_specs()}
    assert "atom_f16f64e92cd14d74" in open_atoms
    assert "atom_e867f667225442a4" in open_atoms
    assert "atom_c0f2558fe81046cf" in open_atoms
    assert "atom_5e7aa160e5604f79" in open_atoms
    assert "atom_0641a88159d6456b" in open_atoms

    edge_types = {
        edge["target_atom_id"]: edge["edge_type"]
        for edge in report["research_kernel_edges_to_add"]
    }
    assert edge_types["atom_ef1f5b6ebed246eb"] == "SUPERSEDES"
    assert edge_types["atom_d64b2781e6604d77"] == "SUPERSEDES"
    assert edge_types["atom_e4b9b11387894204"] == "SPECIALIZES"
    assert edge_types["atom_41092f7feb7f4df8"] == "SPECIALIZES"

    non_claims = "\n".join(report["non_claims"]).lower()
    assert "closes only the listed n8" in non_claims
    assert "leaves unrelated n7" in non_claims
    assert "no settlement, governance, state-root, or production authority" in non_claims


def test_research_kernel_frontier_hygiene_cli() -> None:
    _require_generated_prerequisites()

    proc = subprocess.run(
        [sys.executable, "tools/check_research_kernel_frontier_hygiene_20260629.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["closure_count"] == 4
    assert report["open_frontier_count"] == 5
