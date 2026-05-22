#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "generated" / "report.json"
CAP_BUILDER = ROOT.parent / "math_object_innovation_v190" / "build_fee_cap_recommendations.py"


def load_report() -> dict:
    subprocess.run([sys.executable, str(ROOT / "run_cycle.py")], check=True)
    return json.loads(REPORT.read_text(encoding="utf-8"))


def test_stress_corpus_rejects_expected_bad_rows() -> None:
    report = load_report()

    assert report["receipt_count"] == 32
    assert report["accepted_count"] == 27
    assert report["rejected_count"] == 5
    assert report["model_audit"]["total_stress_invariant_failures"] == 0
    assert report["reject_reason_mismatches"] == {}
    assert report["actual_reject_reason_counts"] == report["expected_reject_reason_counts"]


def test_fee_cap_recommendations_survive_multi_sample_evidence() -> None:
    report = load_report()

    assert report["candidate_review_cap_count"] == 6
    assert report["launch_parameter_claim_count"] == 0
    assert report["status_counts"]["candidate_review_cap"] == 6
    assert report["status_counts"]["protocol_surplus_internal_capture"] == 2
    assert report["status_counts"]["penalty_not_primary_revenue"] == 1
    assert report["status_counts"]["rejected_only"] == 5
    assert report["retail_cap_failures"] == 0
    assert report["cap_clip_surfaces"] == ["cow_batch_solver_surplus", "lp_loss_cover_premium"]


def test_stricter_sample_threshold_fails_closed(tmp_path: Path) -> None:
    load_report()
    out = tmp_path / "strict_caps.json"
    subprocess.run(
        [
            sys.executable,
            str(CAP_BUILDER),
            "--calibration-report",
            str(ROOT / "generated" / "calibration_report.json"),
            "--output",
            str(out),
            "--min-user-fee-samples",
            "4",
        ],
        check=True,
    )
    strict = json.loads(out.read_text(encoding="utf-8"))

    assert strict["candidate_review_cap_count"] == 0
    assert strict["status_counts"]["insufficient_user_fee_evidence"] == 6
    assert strict["launch_parameter_claim_count"] == 0
    assert strict["model_audit"]["total_recommendation_invariant_failures"] == 0


def test_generated_artifact_paths_are_repo_relative() -> None:
    report = load_report()
    for value in report["artifacts"].values():
        assert not Path(str(value)).is_absolute()
        assert str(value).startswith("generated/")
