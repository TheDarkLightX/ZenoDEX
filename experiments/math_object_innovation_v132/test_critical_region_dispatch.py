from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "generated" / "critical_region_dispatch_report.json"


@pytest.fixture(scope="session")
def report() -> dict:
    subprocess.run(
        [sys.executable, str(ROOT / "run_critical_region_dispatch.py")],
        cwd=ROOT,
        check=True,
    )
    return json.loads(REPORT.read_text(encoding="utf-8"))


def test_exact_backend_matches_power_basis_reference(report: dict) -> None:
    assert report["arithmetic"] == "Rational{BigInt}"
    assert report["backend_parity_checks"] == 12
    assert report["authority"] == "none"


def test_all_methods_fail_closed_on_the_bounded_corpus(report: dict) -> None:
    for method in ("equal", "midpoint", "critical"):
        metrics = report["method_metrics"][method]
        assert metrics["positive_obligations"] == 772
        assert metrics["accepted_positive"] == 772
        assert metrics["unknown_positive"] == 0
        assert metrics["negative_controls"] == 7
        assert metrics["false_accepts"] == 0


def test_midpoint_adaptive_reduces_receipt_cost(report: dict) -> None:
    comparison = report["comparisons"]["midpoint_vs_equal"]

    assert report["selected_method"] == "midpoint_adaptive"
    assert comparison["piece_savings"] == 664
    assert comparison["piece_savings_bps"] == 1848
    assert comparison["byte_savings"] == 1_412_852
    assert comparison["byte_savings_bps"] == 3466
    assert comparison["piece_relation_counts"] == {"equal": 450, "lower": 322}
    assert comparison["byte_relation_counts"] == {"equal": 450, "lower": 322}


def test_adaptive_refinement_lowers_bounded_unknown_rate(report: dict) -> None:
    methods = report["method_metrics"]

    assert methods["equal"]["budget_curve"]["6"]["unknown"] == 240
    assert methods["midpoint"]["budget_curve"]["6"]["unknown"] == 5
    assert methods["equal"]["budget_curve"]["8"]["unknown"] == 5
    assert methods["midpoint"]["budget_curve"]["8"]["unknown"] == 0
    assert methods["midpoint"]["max_certificate_pieces"] == 8


def test_derivative_landmark_candidate_is_not_promoted(report: dict) -> None:
    versus_equal = report["comparisons"]["critical_vs_equal"]
    versus_midpoint = report["comparisons"]["critical_vs_midpoint"]

    assert versus_equal["piece_savings"] > 0
    assert versus_equal["byte_savings"] < 0
    assert versus_midpoint["piece_savings"] < 0
    assert versus_midpoint["byte_savings"] < 0


def test_every_family_preserves_acceptance(report: dict) -> None:
    for metrics in report["family_metrics"].values():
        for method in ("equal", "midpoint", "critical"):
            assert metrics[method]["accepted"] > 0
        assert metrics["midpoint"]["total_pieces"] <= metrics["equal"]["total_pieces"]
        assert metrics["midpoint"]["total_bytes"] <= metrics["equal"]["total_bytes"]
