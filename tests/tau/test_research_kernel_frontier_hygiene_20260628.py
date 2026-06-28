from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_research_kernel_frontier_hygiene_20260628 import REPORT_JSON, build_report, closure_specs


ROOT = Path(__file__).resolve().parents[2]


def _require_generated_prerequisites() -> None:
    missing = [spec.report_path for spec in closure_specs() if not (ROOT / spec.report_path).exists()]
    if missing:
        pytest.skip(
            "generated prerequisite reports are absent; run "
            "`python3 tools/check_research_kernel_frontier_hygiene_20260628.py --refresh`"
        )


def test_research_kernel_frontier_hygiene_report() -> None:
    _require_generated_prerequisites()

    report = build_report()

    assert report["ok"] is True
    assert report["schema"] == "zenodex.research_kernel_frontier_hygiene.v1"
    assert report["closure_count"] == 5
    assert report["stale_risk_closure_count"] >= 3
    assert report["resolved_count"] >= 2
    assert report["bounded_count"] >= 2
    assert all(row["closed"] for row in report["closures"])

    by_atom = {row["frontier_atom_id"]: row for row in report["closures"]}
    assert by_atom["atom_db8d68413cd34328"]["closure_kind"] == "resolves"
    assert by_atom["atom_86d2810ce9ad4b50"]["closure_kind"] == "resolves"
    assert by_atom["atom_2d749c2ecd2e4c9a"]["closure_kind"] == "bounds"
    assert by_atom["atom_28ea53e1ebcc4f97"]["closure_kind"] == "bounds"

    edge_targets = {edge["target_atom_id"] for edge in report["research_kernel_edges_to_add"]}
    assert "atom_db8d68413cd34328" in edge_targets
    assert "atom_86d2810ce9ad4b50" in edge_targets
    assert "atom_2d749c2ecd2e4c9a" in edge_targets
    assert "atom_28ea53e1ebcc4f97" in edge_targets

    edge_types = {edge["target_atom_id"]: edge["edge_type"] for edge in report["research_kernel_edges_to_add"]}
    assert edge_types["atom_db8d68413cd34328"] == "SUPERSEDES"
    assert edge_types["atom_86d2810ce9ad4b50"] == "SUPERSEDES"
    assert edge_types["atom_2d749c2ecd2e4c9a"] == "SUPERSEDES"
    assert edge_types["atom_28ea53e1ebcc4f97"] == "SPECIALIZES"


def test_research_kernel_frontier_hygiene_cli() -> None:
    _require_generated_prerequisites()

    proc = subprocess.run(
        [sys.executable, "tools/check_research_kernel_frontier_hygiene_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["closure_count"] == 5
