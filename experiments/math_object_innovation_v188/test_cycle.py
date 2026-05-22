from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parent


@pytest.fixture(scope="session")
def report() -> dict:
    subprocess.run(["python3", "run_cycle.py"], cwd=ROOT, check=True)
    return json.loads((ROOT / "generated" / "report.json").read_text())


def test_cycle_runs_fail_closed(report: dict) -> None:
    summary = report["summary"]

    assert report["schema"] == "math-object-innovation/v188"
    assert report["tier"] == "symbolic_state_compiler"
    assert summary["negative_controls"] == 4
    assert summary["accepted_negative"] == 0


def test_positive_cone_claims_are_certified(report: dict) -> None:
    summary = report["summary"]

    assert summary["positive_claims"] > 0
    assert summary["positive_certified"] == summary["positive_claims"]
    assert summary["positive_unknown"] == 0
    assert summary["max_pieces_positive"] <= 128


def test_oriented_anchor_repairs_asymmetric_jacobi_turan(report: dict) -> None:
    summary = report["summary"]

    assert summary["oriented_cases"] > 0
    assert summary["oriented_certified"] == summary["oriented_cases"]
    assert summary["oriented_unknown"] == 0


def test_wrong_strict_endpoint_is_endpoint_falsified(report: dict) -> None:
    summary = report["summary"]

    assert summary["outside_cone_cases"] > 0
    assert summary["outside_endpoint_falsified"] == summary["outside_cone_cases"]
    assert summary["outside_accidentally_certified"] == 0
    assert summary["wrong_anchor_endpoint_falsified"] == summary["wrong_anchor_cases"]


def test_holdout_metrics_are_explicit(report: dict) -> None:
    assert report["split_metrics"]["discovery"]["positive_claim"] > 0
    assert report["split_metrics"]["holdout"]["positive_claim"] > 0
    assert (
        report["split_metrics"]["holdout"]["positive_certified"]
        == report["split_metrics"]["holdout"]["positive_claim"]
    )
