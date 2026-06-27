from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
REPORT_JSON = REPO / "generated" / "zenodex_route_dominance_frontier_refuter_20260627" / "report.json"
sys.path.insert(0, str(REPO / "tools"))

from zenodex_route_dominance_frontier_refuter_20260627 import (  # noqa: E402
    ASSET_A,
    ASSET_B,
    _route_pools,
    enumerate_route_labels,
    run_refuter,
)


def _case(report: dict, case_id: str) -> dict:
    for row in report["cases"]:
        if row["case_id"] == case_id:
            return row
    raise AssertionError(f"missing case {case_id}")


def test_route_dominance_frontier_refuter_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_route_dominance_frontier_refuter_20260627.py"],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert result["ok"] is True
    assert result["case_count"] == 3
    assert result["false_declared_admit_count"] == 2
    assert result["computed_false_admit_count"] == 0

    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["false_declared_admit_count"] == 2
    assert report["computed_false_admit_count"] == 0


def test_route_label_domain_is_sorted_and_pins_best_witness() -> None:
    labels = enumerate_route_labels(_route_pools(), asset_in=ASSET_A, asset_out=ASSET_B, amount_out=42)

    assert len(labels) == 45
    assert [label.objective_key for label in labels] == sorted(label.objective_key for label in labels)
    assert labels[0].route_id == "twohop:p_ac>p_cb"
    assert labels[0].route.amount_in == 67
    assert labels[1].route_id == "twohop:p_ac_fee_heavy>p_cb"
    assert labels[1].route.amount_in == 88


def test_computed_flags_close_pruned_winner_and_projection_cover_forgeries() -> None:
    report = run_refuter()
    valid = _case(report, "valid_best_only_dominates")
    pruned_winner = _case(report, "forged_pruned_winner_without_dominator")
    projection_gap = _case(report, "forged_projection_cover_gap")

    assert valid["host_ok"] is True
    assert valid["declared_tau_accepts"] is True
    assert valid["computed_tau_accepts"] is True
    assert valid["host"]["failed_flags"] == []

    assert pruned_winner["host_ok"] is False
    assert pruned_winner["declared_tau_accepts"] is True
    assert pruned_winner["computed_tau_accepts"] is False
    assert pruned_winner["host"]["failed_flags"] == ["i4"]
    assert pruned_winner["host"]["selected_amount_in"] > pruned_winner["host"]["best_full_amount_in"]

    assert projection_gap["host_ok"] is False
    assert projection_gap["declared_tau_accepts"] is True
    assert projection_gap["computed_tau_accepts"] is False
    assert projection_gap["host"]["failed_flags"] == ["i6"]
    assert projection_gap["host"]["missing_route_ids"] == ["direct:p_ab_direct_deep"]


def test_refuter_preserves_tau_authority_boundary_in_non_claims() -> None:
    report = run_refuter()
    non_claims = "\n".join(report["non_claims"])

    assert "not an exhaustive all-route theorem" in non_claims
    assert "host verification must compute those flags" in non_claims
    assert "does not authorize settlement" in non_claims
