from __future__ import annotations

from types import SimpleNamespace

import pytest

import src.integration.proof_mining_runtime as runtime_module
from src.core.dex import DexState
from src.core.proof_mining_claims import build_proof_mining_claim
from src.core.proof_mining_manager import ProofMiningManagerSnapshot
from src.integration.proof_mining_context import ProofMiningContext, build_proof_mining_context, proof_payload_hash
from src.integration.proof_mining_runtime import (
    ProofMiningRuntimeState,
    apply_proof_mining_claim,
    initialize_proof_mining_runtime_state,
    proof_mining_runtime_state_from_obj,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable


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


def test_proof_payload_hash_rejects_non_mapping_and_context_coerces_scheme() -> None:
    with pytest.raises(TypeError, match="proof must be an object"):
        proof_payload_hash("not-an-object")  # type: ignore[arg-type]

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    ctx = build_proof_mining_context(
        chain_id=1,  # type: ignore[arg-type]
        prev_state_hash=2,  # type: ignore[arg-type]
        batch_hash=3,  # type: ignore[arg-type]
        proof={"proof": "ok"},
        next_state=state,
        proof_scheme=7,  # type: ignore[arg-type]
    )
    assert ctx.chain_id == "1"
    assert ctx.prev_state_hash == "2"
    assert ctx.batch_hash == "3"
    assert ctx.proof_scheme == "7"


def test_proof_mining_runtime_rejects_bad_shapes_and_handles_fail_closed_result(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with pytest.raises(TypeError, match="proof_mining must be an object"):
        proof_mining_runtime_state_from_obj("bad")  # type: ignore[arg-type]

    base_obj = {
        "schema": "zenodex/proof_mining_runtime_state/v1",
        "reward_pool_pubkey": "0x" + "99" * 48,
        "epoch": 1,
        "base_reward": 8,
        "initial_pool": 20,
        "reward_pool_balance": 16,
        "total_paid": 4,
        "claimed_slots": [],
    }

    bad_schema_obj = dict(base_obj)
    bad_schema_obj["schema"] = "zenodex/proof_mining_runtime_state/v0"
    with pytest.raises(ValueError, match="unsupported proof mining runtime schema"):
        proof_mining_runtime_state_from_obj(bad_schema_obj)

    none_claimed = dict(base_obj)
    none_claimed["claimed_slots"] = None
    parsed = proof_mining_runtime_state_from_obj(none_claimed)
    assert dict(parsed.snapshot.claimed_slots) == {}

    bad_claimed = dict(base_obj)
    bad_claimed["claimed_slots"] = "not-a-list"
    with pytest.raises(TypeError, match="proof_mining.claimed_slots must be a list"):
        proof_mining_runtime_state_from_obj(bad_claimed)

    claim = _claim(miner_id="0x" + "11" * 48, reward_pool_before=20)
    with pytest.raises(TypeError, match="reward_pool_pubkey must be a non-empty string"):
        initialize_proof_mining_runtime_state(
            reward_pool_pubkey="",
            reward_pool_balance=20,
            claim_artifact=claim,
        )
    with pytest.raises(TypeError, match="reward_pool_balance must be an int"):
        initialize_proof_mining_runtime_state(
            reward_pool_pubkey="0x" + "99" * 48,
            reward_pool_balance=True,  # type: ignore[arg-type]
            claim_artifact=claim,
        )

    runtime_state = ProofMiningRuntimeState(
        reward_pool_pubkey="0x" + "99" * 48,
        snapshot=ProofMiningManagerSnapshot(
            epoch=1,
            base_reward=8,
            initial_pool=20,
            reward_pool_balance=20,
            total_paid=0,
            claimed_slots={},
        ),
    )
    monkeypatch.setattr(
        runtime_module,
        "apply_submit_proof_packet",
        lambda **_kwargs: SimpleNamespace(ok=False, state_after=None, error_code="rejected"),
    )
    next_state, result = apply_proof_mining_claim(
        runtime_state=runtime_state,
        claim_artifact=claim,
        actual_reward_pool_balance=20,
        proof_mining_context=_context_from_claim(claim),
    )
    assert next_state == runtime_state
    assert result.ok is False
