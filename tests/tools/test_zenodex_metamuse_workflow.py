from __future__ import annotations

import json
import subprocess
from pathlib import Path

from tools.zenodex_autonomous_checks import (
    _check_batch_mci_vs_bruteforce,
    _check_batch_mci_vs_greedy,
    _check_burn_receipt_accounting_model,
    _check_burn_receipt_replay_rejected,
    _check_dgstr_eval_count,
    _check_dgstr_exact_match,
)

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


def test_batch_mci_vs_bruteforce_check_passes() -> None:
    res = _check_batch_mci_vs_bruteforce("support", 30)
    assert res["status"] == "pass"
    assert res["signal"] is True
    assert int(res["metrics"]["case_count"]) >= 1


def test_batch_mci_vs_greedy_check_passes() -> None:
    res = _check_batch_mci_vs_greedy("support", 30)
    assert res["status"] == "pass"
    assert res["signal"] is True
    assert int(res["metrics"]["improvement_count"]) == int(res["metrics"]["case_count"])


def test_burn_receipt_checks_pass() -> None:
    replay = _check_burn_receipt_replay_rejected("support", 30)
    model = _check_burn_receipt_accounting_model("support", 30)
    assert replay["status"] == "pass"
    assert replay["signal"] is True
    assert model["status"] == "pass"
    assert model["signal"] is True


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


def test_metamuse_workflow_supports_batch_lane(tmp_path: Path) -> None:
    out_dir = tmp_path / "metamuse_batch_lane"
    cmd = [
        "python3",
        "tools/zenodex_metamuse_workflow.py",
        "--lane",
        "batch_ordering_mci_ab",
        "--out-dir",
        str(out_dir),
        "--run-checks",
    ]
    subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True, check=True)
    packet = json.loads((out_dir / "epoch_packet.json").read_text(encoding="utf-8"))
    result = json.loads((out_dir / "result.json").read_text(encoding="utf-8"))
    assert packet["lane"]["lane_id"] == "batch_ordering_mci_ab"
    assert len(packet["hypotheses"]) >= 1
    assert result["runner"]["rc"] == 0
    assert result["summary"]["count"] >= 1
    row = result["summary"]["rows"][0]
    assert row["refute_check"] == "batch_mci_vs_bruteforce"
    assert row["support_check"] == "batch_mci_vs_greedy"


def test_metamuse_workflow_supports_burn_lane(tmp_path: Path) -> None:
    out_dir = tmp_path / "metamuse_burn_lane"
    cmd = [
        "python3",
        "tools/zenodex_metamuse_workflow.py",
        "--lane",
        "burn_receipt_kernel_v1",
        "--out-dir",
        str(out_dir),
        "--run-checks",
    ]
    subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True, check=True)
    packet = json.loads((out_dir / "epoch_packet.json").read_text(encoding="utf-8"))
    result = json.loads((out_dir / "result.json").read_text(encoding="utf-8"))
    assert packet["lane"]["lane_id"] == "burn_receipt_kernel_v1"
    assert len(packet["hypotheses"]) == 1
    assert result["runner"]["rc"] == 0
    row = result["summary"]["rows"][0]
    assert row["refute_check"] == "burn_receipt_replay_rejected"
    assert row["support_check"] == "burn_receipt_accounting_model"


def test_metamuse_workflow_supports_exact_out_lane(tmp_path: Path) -> None:
    out_dir = tmp_path / "metamuse_exact_out_lane"
    cmd = [
        "python3",
        "tools/zenodex_metamuse_workflow.py",
        "--lane",
        "exact_out_multihop_value",
        "--out-dir",
        str(out_dir),
        "--run-checks",
    ]
    subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True, check=True)
    packet = json.loads((out_dir / "epoch_packet.json").read_text(encoding="utf-8"))
    result = json.loads((out_dir / "result.json").read_text(encoding="utf-8"))
    assert packet["lane"]["lane_id"] == "exact_out_multihop_value"
    assert len(packet["hypotheses"]) == 1
    assert result["runner"]["rc"] == 0
    row = result["summary"]["rows"][0]
    assert row["refute_check"] == "route_exact_out_2hop_value"
    assert row["support_check"] == "route_exact_out_2hop_value"
