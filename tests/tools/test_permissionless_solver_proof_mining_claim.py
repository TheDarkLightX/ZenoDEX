from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from tools.permissionless_solver_proof_mining_claim import (
    build_proof_mining_claim,
    proof_mining_claim_hash,
    validate_proof_mining_claim_artifact,
    schedule_reward_amount,
)


SPEC_PATH = Path(__file__).resolve().parents[2] / "src" / "tau_specs" / "proof_mining_reward_32_v1.tau"


def _round_obj(*, miner_id: str = "alice", witness_sha256: str = "sha:a", improvement_u64: int = 7, job_digest: str = "job1") -> dict:
    return {
        "schema": "zenodex/improvement_bounty_round/v1",
        "ok": True,
        "job_digest": job_digest,
        "winner": {
            "miner_id": miner_id,
            "witness_sha256": witness_sha256,
            "improvement_u64": improvement_u64,
        },
        "candidates": [],
        "argmax_certificate": None,
    }


@pytest.mark.parametrize(
    ("base_reward", "epoch", "expected"),
    [
        (64, 0, 64),
        (64, 1, 32),
        (64, 6, 1),
        (1, 7, 1),
    ],
)
def test_schedule_reward_amount_bva(base_reward: int, epoch: int, expected: int) -> None:
    assert schedule_reward_amount(base_reward=base_reward, epoch=epoch) == expected


@pytest.mark.parametrize(
    ("base_reward", "epoch"),
    [
        (0, 0),
        (1, -1),
        (1, 8),
        (0x1_0000_0000, 0),
    ],
)
def test_schedule_reward_amount_rejects_invalid_inputs(base_reward: int, epoch: int) -> None:
    with pytest.raises((TypeError, ValueError)):
        schedule_reward_amount(base_reward=base_reward, epoch=epoch)


def test_build_proof_mining_claim_matches_tau_gate_inputs() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=9),
        round_id="round-proof-1",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=2,
        prover_id=1,
    )
    body = claim["body"]
    assert body["schema"] == "zenodex/permissionless_solver_proof_mining_claim/v1"
    assert body["budget"]["reward_pool_after"] == 16
    assert body["bounded_model"]["reward_amount"] == 4
    assert body["conditions"]["tau_gate_expected_ok"] is True
    assert claim["claim_hash"]

    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[dict(body["tau_inputs"])],
        timeout_s=30.0,
    )
    assert outputs[0]["o4"] == 1


def test_build_proof_mining_claim_detects_budget_failure() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=5),
        round_id="round-proof-2",
        reward_pool_before=3,
        base_reward=8,
        epoch=0,
        proposal_slot=0,
        prover_id=0,
        allow_rejected=True,
    )
    body = claim["body"]
    assert body["bounded_model"]["reward_amount"] == 8
    assert body["budget"]["reward_pool_after"] == -5
    assert body["conditions"]["budget_ok"] is False
    assert body["conditions"]["tau_gate_expected_ok"] is False
    with pytest.raises(ValueError, match="inadmissible"):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_build_proof_mining_claim_requires_positive_improvement() -> None:
    with pytest.raises(ValueError, match="winner improvement must be positive"):
        build_proof_mining_claim(
            round_obj=_round_obj(improvement_u64=0),
            round_id="round-proof-3",
            reward_pool_before=20,
            base_reward=8,
            epoch=0,
            proposal_slot=0,
            prover_id=0,
        )


def test_build_proof_mining_claim_fails_closed_by_default_on_budget_failure() -> None:
    with pytest.raises(ValueError, match="would fail Tau gate"):
        build_proof_mining_claim(
            round_obj=_round_obj(improvement_u64=5),
            round_id="round-proof-4",
            reward_pool_before=3,
            base_reward=8,
            epoch=0,
            proposal_slot=0,
            prover_id=0,
        )


def test_validate_proof_mining_claim_rejects_reward_schedule_mismatch() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(improvement_u64=9),
        round_id="round-proof-5",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
    )
    claim["body"]["bounded_model"]["reward_amount"] = 5
    claim["claim_hash"] = proof_mining_claim_hash(claim["body"])
    with pytest.raises(ValueError, match="reward schedule mismatch"):
        validate_proof_mining_claim_artifact(claim, require_admissible=True)


def test_claim_cli_emits_output(tmp_path: Path) -> None:
    round_path = tmp_path / "round.json"
    out_path = tmp_path / "claim.json"
    round_path.write_text(json.dumps(_round_obj(improvement_u64=6), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    subprocess.check_call(
        [
            "python3",
            "tools/permissionless_solver_proof_mining_claim.py",
            "--round",
            str(round_path),
            "--output",
            str(out_path),
            "--round-id",
            "cli-round-1",
            "--reward-pool-before",
            "12",
            "--base-reward",
            "8",
            "--epoch",
            "1",
            "--proposal-slot",
            "0",
            "--prover-id",
            "0",
        ]
    )

    claim = json.loads(out_path.read_text(encoding="utf-8"))
    assert claim["body"]["bounded_model"]["reward_amount"] == 4
    assert claim["body"]["conditions"]["tau_gate_expected_ok"] is True


def test_claim_cli_fails_closed_when_tau_gate_would_reject(tmp_path: Path) -> None:
    round_path = tmp_path / "round.json"
    out_path = tmp_path / "claim.json"
    round_path.write_text(json.dumps(_round_obj(improvement_u64=6), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(subprocess.CalledProcessError):
        subprocess.check_call(
            [
                "python3",
                "tools/permissionless_solver_proof_mining_claim.py",
                "--round",
                str(round_path),
                "--output",
                str(out_path),
                "--round-id",
                "cli-round-2",
                "--reward-pool-before",
                "3",
                "--base-reward",
                "8",
                "--epoch",
                "0",
                "--proposal-slot",
                "0",
                "--prover-id",
                "0",
            ]
        )
