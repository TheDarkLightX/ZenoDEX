from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPORT_JSON = ROOT / "generated" / "zenodex_ab_compressed_dp_refuter_20260628" / "report.json"


def test_ab_compressed_dp_refuter_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_ab_compressed_dp_refuter_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["witness"]["pool"] == {"fee_bps": 5, "reserve0": 85, "reserve1": 561}
    assert report["results"]["bruteforce"]["key"] == report["results"]["full_state_subset_dp"]["key"]
    assert report["results"]["bruteforce"]["order"] == ["03e8", "03ea", "03e9"]
    assert report["results"]["compressed_subset_only_dp"]["order"] == ["03ea", "03e9", "03e8"]
    assert report["results"]["bruteforce"]["key"][0] == 247
    assert report["results"]["compressed_subset_only_dp"]["key"][0] == 215
    assert report["results"]["objective_loss_amount_a"] == 32
    assert "one-record-per-subset Held-Karp DP is not sound" in report["claim"]["falsified"]
    assert "does not refute the existing full-state subset DP" in " ".join(report["non_claims"])
