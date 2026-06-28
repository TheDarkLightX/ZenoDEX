from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
REPORT_JSON = REPO / "generated" / "zenodex_route_dominance_positive_certificate_20260628" / "report.json"


def test_route_dominance_positive_certificate_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_route_dominance_positive_certificate_20260628.py"],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=60,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert result["ok"] is True
    assert result["frontier_compression"] == "169:5"
    assert result["mutation_invalid_accepts"] == 0
    assert result["prior_false_declared_admits"] == 2

    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["metrics"]["case_count"] == 5
    assert report["metrics"]["frontier_compression"] == "169:5"
    assert report["metrics"]["total_route_label_count"] == 169
    assert report["prior_refuter"]["false_declared_admit_count"] == 2
    assert report["prior_refuter"]["computed_false_admit_count"] == 0
    assert report["mutation_cases"]["invalid_accepts"] == 0


def test_positive_cases_keep_one_best_label_and_prune_the_rest() -> None:
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert all(row["host_ok"] for row in report["positive_cases"])
    assert all(row["tau_accepts"] for row in report["positive_cases"])
    assert all(row["kept_count"] == 1 for row in report["positive_cases"])
    assert all(row["pruned_count"] == row["route_label_count"] - 1 for row in report["positive_cases"])
    assert all(row["selected_route_id"] == row["best_full_route_id"] for row in report["positive_cases"])
    assert all(row["selected_amount_in"] == row["best_full_amount_in"] for row in report["positive_cases"])


def test_mutations_reject_required_route_certificate_flags() -> None:
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    cases = {case["case_id"]: case for case in report["mutation_cases"]["cases"]}
    for case_id in (
        "drop_dominator_reject",
        "drop_projection_cover_reject",
        "drop_quote_replay_reject",
        "drop_rounding_bound_reject",
        "drop_no_authority_reject",
    ):
        assert cases[case_id]["ok"] is True
        assert cases[case_id]["got_o4"] == 0
    assert cases["inactive_safe"]["got_o4"] == 0
    assert cases["inactive_safe"]["got_o5"] == 1


def test_non_claims_preserve_route_authority_boundary() -> None:
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    non_claims = "\n".join(report["non_claims"])
    assert "not an all-route theorem" in non_claims
    assert "untrusted declared Tau flags are unsafe" in non_claims
    assert "does not claim to reduce route-label generation cost" in non_claims
    assert "Tau does not compute route quotes" in non_claims
