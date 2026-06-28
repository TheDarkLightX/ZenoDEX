from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[1]
REPORT_JSON = ROOT / "generated" / "zenodex_tokenomics_pol_sybil_threshold_20260628" / "report.json"


def test_tokenomics_pol_sybil_threshold_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tokenomics_pol_sybil_threshold_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["threshold_found_count"] == 5
    assert report["no_threshold_count"] == 1
    cases = {case["case_id"]: case for case in report["threshold_cases"]}
    assert cases["proto20_reward20"]["threshold_pol_share_bps"] == 3704
    assert cases["proto20_reward20"]["cost_below_threshold"] == "199981/10000"
    assert cases["proto20_reward20"]["cost_at_threshold"] == "25001/1250"
    assert cases["proto20_reward20"]["envelope_accepts_threshold"] is True
    assert cases["proto20_reward20"]["envelope_rejects_below"] is True
    assert cases["already_safe_proto50_reward10"]["threshold_pol_share_bps"] == 0
    assert cases["no_threshold_proto100_reward12"]["threshold_found"] is False
    assert cases["no_threshold_proto100_reward12"]["cost_at_pol_10000"] == "11/1"

    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    tau_cases = {case["case_id"]: case for case in report["tau"]["case_results"]}
    assert tau_cases["threshold_certificate_pass"]["got"]["o4"] == 1
    assert tau_cases["minimality_reject"]["got"]["o4"] == 0
    assert tau_cases["best_response_reject"]["got"]["o4"] == 0
    assert tau_cases["no_threshold_replay_reject"]["got"]["o4"] == 0
    assert tau_cases["authority_reject"]["got"]["o4"] == 0
    assert tau_cases["inactive_safe"]["got"]["o5"] == 1

    assert "bounded fee-gated identity reward model" in " ".join(report["non_claims"])
    assert "does not activate any reward program" in " ".join(report["non_claims"])
