from __future__ import annotations

import json

from src.core.dex import DexState
from src.core.proof_mining_claims import build_proof_mining_claim
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.proof_mining_claimability import evaluate_proof_mining_claimability
from src.integration.proof_mining_runtime import (
    apply_proof_mining_claim,
    initialize_proof_mining_runtime_state,
    proof_mining_runtime_state_to_obj,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def _claim(*, miner_id: str, reward_pool_before: int, slot: int = 0) -> dict:
    return build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": f"job-{slot}",
            "winner": {
                "miner_id": miner_id,
                "witness_sha256": f"witness-{slot}",
                "improvement_u64": 9,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id=f"round-{slot}",
        reward_pool_before=reward_pool_before,
        base_reward=8,
        epoch=1,
        proposal_slot=slot,
        prover_id=1,
    )


def _wrapped_app_state(proof_state) -> str:
    dex_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    payload = {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(dex_state).data,
        "proof_mining": proof_mining_runtime_state_to_obj(proof_state),
    }
    return json.dumps(payload, separators=(",", ":"), sort_keys=True)


def test_claimability_accepts_initial_claim_without_existing_runtime_state() -> None:
    sender = "0x" + "11" * 48
    reward_pool = "0x" + "99" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool: 20, sender: 0},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
    )

    assert status.enabled is True
    assert status.claimable is True
    assert status.error is None
    assert status.reward_amount == 4
    assert status.reward_pool_before == 20
    assert status.reward_pool_after == 16
    assert status.checks["runtime_state_present"] is False
    assert status.checks["runtime_apply_ok"] is True


def test_claimability_rejects_proposal_hash_mismatch() -> None:
    sender = "0x" + "22" * 48
    reward_pool = "0x" + "88" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool: 20, sender: 0},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash="sha256:not-the-same",
    )

    assert status.claimable is False
    assert status.error == "proof mining claim proposal_hash mismatch"
    assert status.checks["claim_valid"] is True
    assert status.checks["proposal_hash_matches_context"] is False


def test_claimability_rejects_reward_pool_balance_drift_with_runtime_state() -> None:
    sender = "0x" + "33" * 48
    reward_pool = "0x" + "77" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    runtime_state = initialize_proof_mining_runtime_state(
        reward_pool_pubkey=reward_pool,
        reward_pool_balance=20,
        claim_artifact=claim,
    )
    next_state, result = apply_proof_mining_claim(
        runtime_state=runtime_state,
        claim_artifact=claim,
        actual_reward_pool_balance=20,
    )
    assert result.ok is True

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json=_wrapped_app_state(next_state),
        chain_balances={reward_pool: 15, sender: 4},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
    )

    assert status.claimable is False
    assert status.error == "proof mining reward pool balance drift"
    assert status.checks["runtime_state_present"] is True
    assert status.checks["reward_pool_pubkey_matches_state"] is True
    assert status.checks["reward_pool_balance_matches_state"] is False
