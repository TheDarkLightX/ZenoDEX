from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest


def _round_obj() -> dict:
    return {
        "schema": "zenodex/improvement_bounty_round/v1",
        "ok": True,
        "job_digest": "job1",
        "winner": {
            "miner_id": "alice",
            "witness_sha256": "sha:a",
            "improvement_u64": 7,
        },
        "candidates": [],
        "argmax_certificate": None,
    }


def _snapshot() -> dict:
    return {
        "schema": "zenodex/proof_mining_manager_snapshot/v1",
        "epoch": 1,
        "base_reward": 8,
        "initial_pool": 20,
        "reward_pool_balance": 20,
        "total_paid": 0,
        "claimed_slots": {},
    }


def test_permissionless_proof_mining_manager_packet_cli_build_and_apply(tmp_path: Path) -> None:
    round_path = tmp_path / "round.json"
    claim_path = tmp_path / "claim.json"
    snapshot_path = tmp_path / "snapshot.json"
    packet_path = tmp_path / "packet.json"
    apply_path = tmp_path / "apply.json"

    round_path.write_text(json.dumps(_round_obj(), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    snapshot_path.write_text(json.dumps(_snapshot(), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    subprocess.check_call(
        [
            "python3",
            "tools/permissionless_solver_proof_mining_claim.py",
            "--round",
            str(round_path),
            "--output",
            str(claim_path),
            "--round-id",
            "cli-round-claim",
            "--reward-pool-before",
            "20",
            "--base-reward",
            "8",
            "--epoch",
            "1",
            "--proposal-slot",
            "0",
            "--prover-id",
            "2",
            "--chain-id",
            "tau-testnet-alpha",
            "--prev-state-hash",
            "sha256:prev",
            "--batch-hash",
            "sha256:batch",
            "--dex-hash-after",
            "sha256:after",
        ]
    )

    subprocess.check_call(
        [
            "python3",
            "tools/permissionless_proof_mining_manager_packet.py",
            "--claim",
            str(claim_path),
            "--snapshot",
            str(snapshot_path),
            "--output",
            str(packet_path),
        ]
    )
    packet = json.loads(packet_path.read_text(encoding="utf-8"))
    assert packet["schema"] == "zenodex/proof_mining_manager_packet/v1"
    assert packet["packet"]["command_tag"] == "submit_proof"

    subprocess.check_call(
        [
            "python3",
            "tools/permissionless_proof_mining_manager_packet.py",
            "--claim",
            str(claim_path),
            "--snapshot",
            str(snapshot_path),
            "--output",
            str(apply_path),
            "--apply",
        ]
    )
    applied = json.loads(apply_path.read_text(encoding="utf-8"))
    assert applied["schema"] == "zenodex/proof_mining_manager_apply_result/v1"
    assert applied["ok"] is True
    assert applied["effects"]["reward_amount"] == 4
    assert applied["state_after"]["reward_pool_balance"] == 16


def test_permissionless_proof_mining_manager_packet_cli_rejects_aliased_snapshot_keys(tmp_path: Path) -> None:
    round_path = tmp_path / "round.json"
    claim_path = tmp_path / "claim.json"
    snapshot_path = tmp_path / "snapshot.json"
    packet_path = tmp_path / "packet.json"

    round_path.write_text(json.dumps(_round_obj(), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    snapshot = _snapshot()
    snapshot["claimed_slots"] = {"1": "sha256:occupied1", "01": "sha256:occupied01"}
    snapshot_path.write_text(json.dumps(snapshot, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    subprocess.check_call(
        [
            "python3",
            "tools/permissionless_solver_proof_mining_claim.py",
            "--round",
            str(round_path),
            "--output",
            str(claim_path),
            "--round-id",
            "cli-round-claim-alias",
            "--reward-pool-before",
            "20",
            "--base-reward",
            "8",
            "--epoch",
            "1",
            "--proposal-slot",
            "0",
            "--prover-id",
            "2",
            "--chain-id",
            "tau-testnet-alpha",
            "--prev-state-hash",
            "sha256:prev",
            "--batch-hash",
            "sha256:batch",
            "--dex-hash-after",
            "sha256:after",
        ]
    )

    with pytest.raises(subprocess.CalledProcessError):
        subprocess.check_call(
            [
                "python3",
                "tools/permissionless_proof_mining_manager_packet.py",
                "--claim",
                str(claim_path),
                "--snapshot",
                str(snapshot_path),
                "--output",
                str(packet_path),
            ]
        )
