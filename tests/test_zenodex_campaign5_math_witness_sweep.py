from __future__ import annotations

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "zenodex_campaign5_math_witness_sweep.jl"


def test_campaign5_julia_math_witness_sweep_is_accepted() -> None:
    proc = subprocess.run(
        ["julia", str(SCRIPT), "--json"],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.campaign5.math_witness_sweep.v1"
    assert receipt["status"] == "accepted"
    assert receipt["case_count"] == 8
    assert receipt["failed_count"] == 0

    cases = {case["id"]: case for case in receipt["cases"]}
    assert cases["standard_sybil_profit_equals_insurance_draw"]["ok"] is True
    assert cases["adl_haircut_blocks_sybil_profit"]["ok"] is True
    assert cases["twal_reward_matches_duration_exposure_witness"]["ok"] is True
    assert cases["same_asset_exact_out_ring_rejected"]["ok"] is True
    assert cases["two_hop_ring_paths_are_bounded_and_acyclic"]["ok"] is True


def test_campaign5_julia_math_witness_sweep_text_mode_is_stable() -> None:
    proc = subprocess.run(
        ["julia", str(SCRIPT)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0
    assert "schema = zenodex.campaign5.math_witness_sweep.v1" in proc.stdout
    assert "case_count = 8" in proc.stdout
    assert "failed_count = 0" in proc.stdout
    assert "status = accepted" in proc.stdout
