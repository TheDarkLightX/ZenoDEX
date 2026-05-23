#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "generated" / "report.json"
CAPS = ROOT.parent / "math_object_innovation_v190" / "build_fee_cap_recommendations.py"


def load_report() -> dict:
    subprocess.run([sys.executable, str(ROOT / "run_cycle.py")], check=True)
    return json.loads(REPORT.read_text(encoding="utf-8"))


def test_execution_receipts_are_positive_route_improvements() -> None:
    report = load_report()
    metrics = report["execution_metrics"]

    assert report["receipt_count"] == 20
    assert report["accepted_count"] == 18
    assert report["rejected_count"] == 2
    assert metrics["market_case_count"] == 3
    assert metrics["route_receipt_count"] == 9
    assert metrics["exact_out_receipt_count"] == 9
    assert metrics["route_improvement_min"] > 0
    assert metrics["exact_out_savings_min"] > 0
    assert metrics["route_improvement_max"] > metrics["route_improvement_min"]
    assert metrics["exact_out_savings_max"] > metrics["exact_out_savings_min"]


def test_execution_cap_builder_rejects_bad_rows_and_stays_review_only() -> None:
    report = load_report()

    assert report["candidate_review_cap_count"] == 2
    assert report["launch_parameter_claim_count"] == 0
    assert report["status_counts"] == {"candidate_review_cap": 2, "rejected_only": 2}
    assert report["actual_reject_reason_counts"] == report["expected_reject_reason_counts"]
    assert report["reject_reason_mismatches"] == {}
    assert report["unexpected_reject_reasons"] == {}
    assert report["model_audit"]["total_execution_receipt_invariant_failures"] == 0


def test_execution_retail_caps_are_clipped_to_hard_rails() -> None:
    report = load_report()
    caps = report["recommended_caps"]

    assert set(caps) == {"route_surplus_capture", "exact_out_savings_capture"}
    assert caps["route_surplus_capture"] <= 2500
    assert caps["exact_out_savings_capture"] <= 2500
    assert report["retail_cap_failures"] == 0


def test_execution_caps_fail_closed_when_sample_threshold_exceeds_corpus(tmp_path: Path) -> None:
    load_report()
    out = tmp_path / "strict_caps.json"
    subprocess.run(
        [
            sys.executable,
            str(CAPS),
            "--calibration-report",
            str(ROOT / "generated" / "calibration_report.json"),
            "--output",
            str(out),
            "--min-user-fee-samples",
            "10",
        ],
        check=True,
    )
    strict = json.loads(out.read_text(encoding="utf-8"))

    assert strict["candidate_review_cap_count"] == 0
    assert strict["status_counts"]["insufficient_user_fee_evidence"] == 2
    assert strict["launch_parameter_claim_count"] == 0
    assert strict["model_audit"]["total_recommendation_invariant_failures"] == 0


def test_generated_artifact_paths_are_repo_relative() -> None:
    report = load_report()
    for value in report["artifacts"].values():
        assert not Path(str(value)).is_absolute()
        assert str(value).startswith("generated/")
