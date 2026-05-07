from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zeno_oracle_o3_receipt_flow_replay import build_o3_receipt_flow_replay  # noqa: E402


def test_o3_receipt_flow_replay_accepts_all_stages() -> None:
    receipt = build_o3_receipt_flow_replay()

    assert receipt["schema"] == "zenodex.oracle.o3_receipt_flow_replay.v1"
    assert receipt["status"] == "accepted"
    assert receipt["ok"] is True
    assert receipt["stage_count"] == 8
    assert receipt["accepted_stage_count"] == 8
    assert receipt["failed_stage_count"] == 0
    assert receipt["errors"] == []

    assert [stage["name"] for stage in receipt["stages"]] == [
        "feed_registry",
        "reporter_lifecycle",
        "signed_report",
        "report_admission",
        "admitted_median3",
        "accepted_read",
        "action_adapter",
        "terminal_dag_replay",
    ]
    assert all(stage["status"] == "accepted" and stage["ok"] for stage in receipt["stages"])
    assert receipt["query_id"].startswith("sha256:")
    assert receipt["aggregate_id"].startswith("sha256:")
    assert receipt["read_receipt_id"].startswith("sha256:")
    assert receipt["consumer_action_receipt_id"].startswith("sha256:")
    assert "does_not_claim_production_oracle_network_live" in receipt["not_claimed"]


def test_o3_receipt_flow_replay_cli_writes_receipt(tmp_path: Path) -> None:
    output = tmp_path / "o3-receipt-flow.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zeno_oracle_o3_receipt_flow_replay.py",
            "--format",
            "text",
            "--output",
            str(output),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "accepted_stage_count = 8" in proc.stdout
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["status"] == "accepted"
