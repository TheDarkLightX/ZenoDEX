from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
REPORT_JSON = REPO / "generated" / "zenodex_oracle_coupled_inequality_parity_fuzzer_20260627" / "report.json"
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_coupled_inequality_parity_fuzzer_20260627 import run_fuzzer  # noqa: E402


def test_coupled_inequality_parity_fuzzer_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_coupled_inequality_parity_fuzzer_20260627.py"],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert result["ok"] is True
    assert result["case_count"] == 594
    assert result["mismatch_count"] == 0

    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["by_family"]["metadata_domain"]["cases"] == 5
    assert report["by_family"]["metadata_domain"]["mismatches"] == 0
    assert report["mismatch_count"] == 0


def test_coupled_inequality_parity_fuzzer_covers_metadata_and_economic_errors() -> None:
    report = run_fuzzer(seed=20260627, random_cases=16)
    coverage = set(report["error_coverage"])

    assert report["ok"] is True
    assert "economic_security_schema_mismatch" in coverage
    assert "query_id_must_be_sha256" in coverage
    assert "unknown_economic_security_field:hidden_mint" in coverage
    assert "attack_cost_floor_below_required_margin" in coverage
    assert "reporter_reward_budget_exceeded" in coverage
    assert "slash_deterrence_below_required_margin" in coverage
    assert "fee_shares_exceed_fee_paid" in coverage
