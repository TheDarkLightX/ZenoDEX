from __future__ import annotations

import pytest

from src.core.proof_mining_claims import build_proof_mining_claim
from src.integration.proof_mining_runtime import (
    ProofMiningRuntimeState,
    apply_proof_mining_claim,
    initialize_proof_mining_runtime_state,
    proof_mining_runtime_state_from_obj,
    proof_mining_runtime_state_to_obj,
)
from src.integration.proof_mining_context import ProofMiningContext
from src.core.proof_mining_manager import ProofMiningManagerSnapshot


def _claim(*, miner_id: str, reward_pool_before: int, base_reward: int = 8, epoch: int = 1, slot: int = 0):
    return build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": f"job-{slot}",
            "winner": {
                "miner_id": miner_id,
                "witness_sha256": f"witness-{slot}",
                "improvement_u64": 7,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id=f"round-{slot}",
        reward_pool_before=reward_pool_before,
        base_reward=base_reward,
        epoch=epoch,
        proposal_slot=slot,
        prover_id=2,
        chain_id="tau-testnet-alpha",
        prev_state_hash=f"sha256:prev-{slot}",
        batch_hash=f"sha256:batch-{slot}",
        dex_hash_after=f"sha256:after-{slot}",
    )


def _context_from_claim(claim: dict) -> ProofMiningContext:
    binding = claim["body"]["proposal_binding"]
    return ProofMiningContext(
        chain_id=str(binding["chain_id"]),
        prev_state_hash=str(binding["prev_state_hash"]),
        batch_hash=str(binding["batch_hash"]),
        witness_hash=str(binding["witness_hash"]),
        dex_hash_after=str(binding["dex_hash_after"]),
        proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_scheme="dummy",
    )


def test_proof_mining_runtime_state_roundtrip_and_duplicate_slot_rejected():
    state = ProofMiningRuntimeState(
        reward_pool_pubkey="0x" + "99" * 48,
        snapshot=ProofMiningManagerSnapshot(
            epoch=1,
            base_reward=8,
            initial_pool=20,
            reward_pool_balance=16,
            total_paid=4,
            claimed_slots={0: "proposal-a"},
        ),
    )

    obj = proof_mining_runtime_state_to_obj(state)
    parsed = proof_mining_runtime_state_from_obj(obj)
    assert parsed == state

    dup_obj = dict(obj)
    dup_obj["claimed_slots"] = [
        {"slot": 0, "proposal_hash": "proposal-a"},
        {"slot": 0, "proposal_hash": "proposal-b"},
    ]
    with pytest.raises(ValueError, match="duplicate proof mining claimed slot"):
        proof_mining_runtime_state_from_obj(dup_obj)



def test_initialize_proof_mining_runtime_state_binds_claim_parameters_and_pool():
    claim = _claim(miner_id="0x" + "11" * 48, reward_pool_before=20)

    state = initialize_proof_mining_runtime_state(
        reward_pool_pubkey="0x" + "99" * 48,
        reward_pool_balance=20,
        claim_artifact=claim,
    )

    assert state.reward_pool_pubkey == "0x" + "99" * 48
    assert state.snapshot.epoch == 1
    assert state.snapshot.base_reward == 8
    assert state.snapshot.initial_pool == 20
    assert state.snapshot.reward_pool_balance == 20
    assert state.snapshot.total_paid == 0
    assert dict(state.snapshot.claimed_slots) == {}

    with pytest.raises(ValueError, match="reward_pool_balance must be non-negative"):
        initialize_proof_mining_runtime_state(
            reward_pool_pubkey="0x" + "99" * 48,
            reward_pool_balance=-1,
            claim_artifact=claim,
        )



def test_apply_proof_mining_claim_updates_snapshot_and_fails_closed_on_stale_claim_or_drift():
    claim = _claim(miner_id="0x" + "22" * 48, reward_pool_before=20)
    context = _context_from_claim(claim)
    state = initialize_proof_mining_runtime_state(
        reward_pool_pubkey="0x" + "88" * 48,
        reward_pool_balance=20,
        claim_artifact=claim,
    )

    next_state, result = apply_proof_mining_claim(
        runtime_state=state,
        claim_artifact=claim,
        actual_reward_pool_balance=20,
        proof_mining_context=context,
    )

    assert result.ok is True
    assert result.effects is not None
    assert int(result.effects["reward_amount"]) == 4
    assert next_state.snapshot.reward_pool_balance == 16
    assert next_state.snapshot.total_paid == 4
    assert len(dict(next_state.snapshot.claimed_slots)) == 1

    with pytest.raises(ValueError, match="claim reward_pool_before does not match snapshot"):
        apply_proof_mining_claim(
            runtime_state=next_state,
            claim_artifact=claim,
            actual_reward_pool_balance=16,
            proof_mining_context=context,
        )

    with pytest.raises(ValueError, match="reward pool balance does not match runtime snapshot"):
        apply_proof_mining_claim(
            runtime_state=next_state,
            claim_artifact=claim,
            actual_reward_pool_balance=15,
            proof_mining_context=context,
        )
