from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tau_certificate_mutation_atlas_20260628" / "report.json"
REPORT_MD = ROOT / "docs" / "research" / "ZENODEX_TAU_CERTIFICATE_MUTATION_ATLAS_20260628.md"


def _surface(report: dict, surface_id: str) -> dict:
    for surface in report["surfaces"]:
        if surface["surface_id"] == surface_id:
            return surface
    raise AssertionError(f"missing surface {surface_id}")


def _case(surface: dict, case_id: str) -> dict:
    for row in surface["cases"]:
        if row["case_id"] == case_id:
            return row
    raise AssertionError(f"missing case {surface['surface_id']}.{case_id}")


def test_tau_certificate_mutation_atlas_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_certificate_mutation_atlas_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["breakthrough"]["name"] == "Tau certificate mutation atlas"
    assert report["totals"]["surface_count"] == 7
    assert report["totals"]["mutation_count"] >= 80
    assert report["totals"]["required_input_mutations"] >= 78
    assert report["totals"]["invalid_accepts"] == 0
    assert report["totals"]["false_rejects"] == 0
    assert REPORT_MD.exists()


def test_tau_certificate_mutation_atlas_required_surfaces() -> None:
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    surface_ids = {surface["surface_id"] for surface in report["surfaces"]}

    assert {
        "frontier_menu_route_mode",
        "ab_cow_exact_solver_ab_mode",
        "ab_cow_exact_solver_cow_mode",
        "route_split_window_certificate",
        "oracle_polytope_certificate",
        "solver_portfolio_upgrade_certificate",
        "tauspec_ebrm_frontier_selector",
    } <= surface_ids

    for surface in report["surfaces"]:
        assert surface["ok"] is True
        assert surface["invalid_accepts"] == 0
        assert _case(surface, "positive_accept")["got_primary"] == 1


def test_tau_certificate_mutation_atlas_mode_collisions_reject() -> None:
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    frontier = _surface(report, "frontier_menu_route_mode")
    assert _case(frontier, "oracle_mode_collision_reject")["got_primary"] == 0
    assert _case(frontier, "ab_cow_mode_collision_reject")["got_primary"] == 0

    ab = _surface(report, "ab_cow_exact_solver_ab_mode")
    cow = _surface(report, "ab_cow_exact_solver_cow_mode")
    assert _case(ab, "two_modes_reject")["got_primary"] == 0
    assert _case(cow, "two_modes_reject")["got_primary"] == 0


def test_tau_certificate_mutation_atlas_scoped_non_claims() -> None:
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    non_claims = "\n".join(report["non_claims"])

    assert "does not prove the host-computed facts are true" in non_claims
    assert "does not authorize settlement" in non_claims
    assert "not every Tau file" in non_claims
