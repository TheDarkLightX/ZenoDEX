from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
REPORT_JSON = REPO / "generated" / "zenodex_oracle_polytope_compiler_20260627" / "report.json"
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_polytope_compiler_20260627 import compile_polytope  # noqa: E402


def _interval(report: dict, field: str) -> dict:
    for row in report["intervals"]:
        if row["field"] == field:
            return row
    raise AssertionError(f"missing interval for {field}")


def _sample(report: dict, field: str, sample_id: str) -> dict:
    for row in report["boundary_samples"]:
        if row["interval_field"] == field and row["sample_id"] == sample_id:
            return row
    raise AssertionError(f"missing sample {field}.{sample_id}")


def test_oracle_polytope_compiler_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_polytope_compiler_20260627.py"],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert result["ok"] is True
    assert result["intervals"] == 17
    assert result["boundary_samples"] == 68

    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert all(row["ok"] for row in report["boundary_samples"])
    assert all(report["tau_oracle_polytope_facts"].values())


def test_oracle_polytope_attack_cost_interval_is_exact() -> None:
    report = compile_polytope()
    interval = _interval(report, "attack_cost_floor_e8")
    assert interval["lower"] == 60_000_000_000
    assert interval["upper"] == 10**30

    lower = _sample(report, "attack_cost_floor_e8", "lower_wall")
    below = _sample(report, "attack_cost_floor_e8", "below_lower")
    assert lower["expected_ok"] is True and lower["actual_ok"] is True
    assert below["expected_ok"] is False and below["actual_ok"] is False
    assert "attack_cost_floor_below_required_margin" in below["errors"]


def test_oracle_polytope_slash_fraction_interval_is_exact() -> None:
    report = compile_polytope()
    interval = _interval(report, "slash_fraction_bps")
    assert interval["lower"] == 2_400
    assert interval["upper"] == 10_000

    below = _sample(report, "slash_fraction_bps", "below_lower")
    above = _sample(report, "slash_fraction_bps", "above_upper")
    assert below["actual_ok"] is False
    assert "slash_deterrence_below_required_margin" in below["errors"]
    assert above["actual_ok"] is False
    assert "slash_fraction_bps_must_be_int_between_0_and_10000" in above["errors"]


def test_oracle_polytope_declares_scoped_non_claims() -> None:
    report = compile_polytope()
    non_claims = "\n".join(report["non_claims"])
    assert "does not estimate MEV" in non_claims
    assert "does not authorize oracle updates" in non_claims
    assert "one varied field at a time" in non_claims
