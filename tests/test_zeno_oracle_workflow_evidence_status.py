from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools import zeno_oracle_workflow_evidence_status as workflow_status
from tools.zeno_oracle_workflow_evidence_status import build_status

ROOT = Path(__file__).resolve().parents[1]


def test_workflow_evidence_status_accepts_public_lanes() -> None:
    status = build_status()

    assert status["schema"] == "zenodex.oracle.workflow_evidence_status.v1"
    assert status["status"] == "accepted"
    assert status["lane_count"] == 4
    assert status["accepted_lane_count"] == 4

    lanes = {lane["lane_id"]: lane for lane in status["lanes"]}
    assert lanes["tla_oracle_recovery_lifecycle"]["evidence_class"] == "tla_public_replay"
    assert lanes["ltlf_oracle_recovery"]["evidence_class"] == "ltlf_public_replay"
    assert lanes["esso_zusd_oracle_recovery_lifecycle"]["evidence_class"] == "esso_public_replay"
    assert lanes["popperpad_append_only_smoke"]["summary"]["total_entries"] == 2
    external = {
        lane["lane_id"]: lane
        for lane in status["external_research_lanes"]
    }
    assert external["morph_oracle_clamp_envelope_smoke"]["status"] == (
        "external_not_required"
    )


def test_morph_lane_rejects_truthy_non_bool_ok(monkeypatch) -> None:
    monkeypatch.setattr(workflow_status, "_morph_case", lambda: {"ok": "true"})

    report = workflow_status.build_morph_oracle_clamp_envelope_status()

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["lane"]["ok"] == "true"


def test_workflow_evidence_status_cli_writes_receipt(tmp_path: Path) -> None:
    output = tmp_path / "workflow-evidence-status.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zeno_oracle_workflow_evidence_status.py",
            "--format",
            "text",
            "--output",
            str(output),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "accepted_lane_count = 4" in proc.stdout
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["status"] == "accepted"
