from __future__ import annotations

import json
import subprocess
from pathlib import Path

from tools.zenodex_autonomous_checks import _check_dgstr_eval_count, _check_dgstr_exact_match

ROOT = Path(__file__).resolve().parents[2]


def test_dgstr_exact_match_check_passes() -> None:
    res = _check_dgstr_exact_match("support", 30)
    assert res["status"] == "pass"
    assert res["signal"] is True
    assert int(res["metrics"]["case_count"]) >= 1


def test_dgstr_eval_count_check_passes() -> None:
    res = _check_dgstr_eval_count("support", 30)
    assert res["status"] == "pass"
    assert res["signal"] is True
    assert float(res["metrics"]["dgstr_calls_mean"]) < float(res["metrics"]["baseline_calls_mean"])


def test_metamuse_workflow_emits_epoch_artifacts(tmp_path: Path) -> None:
    out_dir = tmp_path / "metamuse_epoch"
    cmd = [
        "python3",
        "tools/zenodex_metamuse_workflow.py",
        "--lane",
        "split_routing_exact_in_dgstr",
        "--out-dir",
        str(out_dir),
    ]
    proc = subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True, check=True)
    payload = json.loads(proc.stdout.strip())
    assert payload["ok"] is True
    packet = json.loads((out_dir / "epoch_packet.json").read_text(encoding="utf-8"))
    assert packet["lane"]["lane_id"] == "split_routing_exact_in_dgstr"
    assert len(packet["hypotheses"]) >= 2
    assert len(packet["stimuli"]) >= 1


def test_metamuse_workflow_can_run_supervised_checks(tmp_path: Path) -> None:
    out_dir = tmp_path / "metamuse_epoch_checked"
    cmd = [
        "python3",
        "tools/zenodex_metamuse_workflow.py",
        "--lane",
        "split_routing_exact_in_dgstr",
        "--out-dir",
        str(out_dir),
        "--run-checks",
    ]
    subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True, check=True)
    result = json.loads((out_dir / "result.json").read_text(encoding="utf-8"))
    assert result["runner"]["rc"] == 0
    assert result["summary"]["count"] >= 2
