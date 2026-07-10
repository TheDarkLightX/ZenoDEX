from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

from tools.zeno_oracle_workflow_evidence_status import build_status


ROOT = Path(__file__).resolve().parents[1]


def test_workflow_evidence_status_accepts_public_lanes() -> None:
    status = build_status()

    assert status["schema"] == "zenodex.oracle.workflow_evidence_status.v1"
    assert status["lane_count"] == 4

    lanes = {lane["lane_id"]: lane for lane in status["lanes"]}
    assert lanes["tla_oracle_recovery_lifecycle"]["evidence_class"] == "tla_public_replay"
    assert lanes["ltlf_oracle_recovery"]["evidence_class"] == "ltlf_public_replay"
    assert lanes["esso_zusd_oracle_recovery_lifecycle"]["evidence_class"] == "esso_public_replay"
    morph_installed = importlib.util.find_spec("morph") is not None
    morph_lane = lanes["morph_oracle_clamp_envelope_smoke"]
    if morph_installed:
        assert morph_lane["status"] == "accepted"
        assert morph_lane["check"] == "CheckResult.PASS"
        assert morph_lane["check2"] == "CheckResult.PASS"
        assert status["status"] == "accepted"
        assert status["accepted_lane_count"] == 4
        return

    assert morph_lane["status"] == "rejected"
    assert any(error.startswith("morph_smoke_failed:ModuleNotFoundError") for error in morph_lane["errors"])
    assert status["status"] == "rejected"
    assert status["accepted_lane_count"] == 3


def test_workflow_evidence_status_can_skip_morph_for_devnet_shell() -> None:
    status = build_status(include_morph=False)

    assert status["schema"] == "zenodex.oracle.workflow_evidence_status.v1"
    assert status["status"] == "accepted"
    assert status["lane_count"] == 3
    assert status["accepted_lane_count"] == 3
    assert status["failed_lane_count"] == 0
    assert {lane["lane_id"] for lane in status["lanes"]} == {
        "tla_oracle_recovery_lifecycle",
        "ltlf_oracle_recovery",
        "esso_zusd_oracle_recovery_lifecycle",
    }


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

    morph_installed = importlib.util.find_spec("morph") is not None
    expected_code = 0 if morph_installed else 1
    expected_status = "accepted" if morph_installed else "rejected"
    expected_accepted = 4 if morph_installed else 3

    assert proc.returncode == expected_code, proc.stdout + proc.stderr
    assert f"accepted_lane_count = {expected_accepted}" in proc.stdout
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["status"] == expected_status


def test_workflow_evidence_status_cli_can_skip_morph(tmp_path: Path) -> None:
    output = tmp_path / "workflow-evidence-status-no-morph.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zeno_oracle_workflow_evidence_status.py",
            "--format",
            "text",
            "--skip-morph",
            "--output",
            str(output),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "lane_count = 3" in proc.stdout
    assert "accepted_lane_count = 3" in proc.stdout
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["status"] == "accepted"
    assert receipt["failed_lane_count"] == 0
