from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_oracle_devnet_disaster_harness_rejects_promoted_bad_shapes(tmp_path: Path) -> None:
    output = tmp_path / "oracle-disaster-receipt.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_devnet_disaster_harness.py",
            "--store-root",
            str(tmp_path / "stores"),
            "--output",
            str(output),
            "--format",
            "text",
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "failed_count = 0" in proc.stdout

    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["schema"] == "zenodex.oracle.devnet_disaster_harness_receipt.v1"
    assert receipt["status"] == "accepted"
    assert receipt["selected_disaster_state_count"] == 17
    assert receipt["unreachable_count"] == 17
    assert receipt["failed_count"] == 0
    closed = {case["disaster_state"] for case in receipt["cases"] if case["ok"]}
    assert "missing_artifact_survives_replay" in closed
    assert "tampered_artifact_survives_replay" in closed
    assert "duplicate_event_changes_balance_or_reward" in closed
    assert "high_uncertainty_price_used_by_critical_action" in closed
