from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from tools import zenoproof_reward_payout_replay as replay
from tools import zenoproof_verify as zv


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "tools" / "zenoproof_registry_manifest.json"


def _manifest() -> dict[str, Any]:
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def test_zenoproof_reward_payout_replay_accepts_bounded_claimability_path() -> None:
    status = replay.build_status(registry=_manifest())

    assert status["schema"] == replay.SCHEMA
    assert status["status"] == "accepted"
    assert status["ok"] is True
    assert status["reward_gate_result"]["status"] == "accepted"
    assert status["proof_mining"]["units"] == {
        "reward_pool_before": 100,
        "reward_amount": 25,
        "reward_pool_after": 75,
        "base_reward": 25,
        "epoch": 0,
    }
    assert status["proof_mining"]["manager_apply"]["ok"] is True
    assert status["proof_mining"]["manager_apply"]["effects"]["reward_amount"] == 25
    assert status["proof_mining"]["manager_apply"]["state_after"]["reward_pool_balance"] == 75
    assert status["proof_mining"]["claimability"]["claimable"] is True
    assert status["proof_mining"]["claimability"]["reward_amount"] == 25
    assert status["not_claimed"] == [
        "does_not_claim_live_proof_mining_payouts",
        "does_not_claim_token_settlement",
        "does_not_claim_live_proof_network",
    ]


def test_zenoproof_reward_payout_replay_rejects_bad_zenoproof_binding() -> None:
    gate = zv.sample_reward_gate()
    gate["expected_output_commitment_root"] = zv.sample_hash("wrong.reward.output")

    status = replay.build_status(reward_gate=gate, registry=_manifest())

    assert status["status"] == "rejected"
    assert status["stage"] == "zenoproof_reward_gate"
    assert status["proof_mining"] is None
    assert "proof:expected_output_commitment_root_mismatch" in status["errors"]


def test_zenoproof_reward_payout_replay_cli_text_accepts() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenoproof_reward_payout_replay.py",
            "--format",
            "text",
            "--registry",
            str(MANIFEST_PATH),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0
    assert "status = accepted" in proc.stdout
    assert "manager_ok = True" in proc.stdout
    assert "claimable = True" in proc.stdout
