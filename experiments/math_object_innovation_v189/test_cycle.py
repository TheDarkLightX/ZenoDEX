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


def test_endpoint_formula_matches_direct_evaluation(report: dict) -> None:
    summary = report["summary"]

    assert report["schema"] == "math-object-innovation/v189"
    assert report["oracle_dependent"] is False
    assert summary["rows"] == 10368
    assert summary["formula_mismatches"] == 0


def test_wrong_endpoint_is_strictly_negative(report: dict) -> None:
    summary = report["summary"]

    assert summary["outside_cone_rows"] > 0
    assert summary["outside_negative"] == summary["outside_cone_rows"]
    assert summary["strict_wrong_negative"] == summary["strict_wrong_rows"]


def test_inside_endpoint_obstruction_is_nonnegative(report: dict) -> None:
    summary = report["summary"]

    assert summary["inside_cone_rows"] > 0
    assert summary["inside_nonnegative"] == summary["inside_cone_rows"]


def test_equal_parameter_boundary_is_zero(report: dict) -> None:
    assert report["summary"]["equal_parameter_zero"] == report["relation_metrics"]["alpha_eq_beta"]["count"]


def test_formulae_are_recorded(report: dict) -> None:
    assert "beta-alpha" in report["formulae"]["right_left_endpoint"]
    assert "alpha-beta" in report["formulae"]["left_right_endpoint"]
