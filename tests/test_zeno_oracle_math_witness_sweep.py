from __future__ import annotations

import json
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_zeno_oracle_math_witness_sweep_accepts_expected_cases() -> None:
    result = subprocess.run(
        ["julia", "tools/zeno_oracle_math_witness_sweep.jl", "--json"],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    receipt = json.loads(result.stdout)
    assert receipt["schema"] == "zenodex.oracle.math_witness_sweep.v1"
    assert receipt["status"] == "accepted"
    assert receipt["case_count"] == 20
    assert receipt["failed_count"] == 0
    case_ids = {case["id"] for case in receipt["cases"]}
    assert "live_economics_escrow_floor_matches_replay" in case_ids
    assert "live_economics_escrow_shortfall_rejects" in case_ids
    assert "live_economics_governance_timelock_accepts" in case_ids
    assert "live_economics_governance_early_execution_rejects" in case_ids
    assert "live_economics_settlement_execution_totals_match_replay" in case_ids
    assert "live_economics_settlement_execution_total_drift_rejects" in case_ids


def test_zenoproof_julia_replay_profile_minimum_tracks_witness_sweep() -> None:
    import tools.zenoproof_verify as zenoproof_verify

    assert zenoproof_verify.MIN_JULIA_MATH_WITNESS_CASE_COUNT == 20
