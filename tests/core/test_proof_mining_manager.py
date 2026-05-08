from __future__ import annotations

import pytest

from src.core.proof_mining_manager import (
    ProofMiningManagerPacket,
    ProofMiningManagerSnapshot,
    apply_submit_proof_packet,
    assign_proposal_slot,
    build_submit_proof_packet,
    preferred_proposal_slot,
)
from tools.permissionless_solver_proof_mining_claim import build_proof_mining_claim


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


def _claim(
    *,
    round_id: str = "r1",
    witness_sha256: str = "sha:a",
    improvement_u64: int = 7,
    job_digest: str = "job1",
    reward_pool_before: int = 20,
) -> dict:
    return build_proof_mining_claim(
        round_obj=_round_obj(witness_sha256=witness_sha256, improvement_u64=improvement_u64, job_digest=job_digest),
        round_id=round_id,
        reward_pool_before=reward_pool_before,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=2,
        chain_id="tau-testnet-alpha",
        prev_state_hash="sha256:prev",
        batch_hash="sha256:batch",
        dex_hash_after="sha256:after",
    )


def _verification_flags() -> dict[str, bool]:
    return {
        "proof_ok": True,
        "binding_ok": True,
        "policy_ok": True,
        "nonce_ok": True,
    }


def _snapshot(*, reward_pool_balance: int = 20, total_paid: int = 0, claimed_slots: dict[int, str] | None = None) -> ProofMiningManagerSnapshot:
    return ProofMiningManagerSnapshot(
        epoch=1,
        base_reward=8,
        initial_pool=reward_pool_balance + total_paid,
        reward_pool_balance=reward_pool_balance,
        total_paid=total_paid,
        claimed_slots=dict(claimed_slots or {}),
    )


def test_apply_submit_proof_packet_updates_state_and_claim_registry() -> None:
    claim = _claim()
    snapshot = _snapshot()
    packet = build_submit_proof_packet(claim_artifact=claim, snapshot=snapshot, verification_flags=_verification_flags())
    result = apply_submit_proof_packet(packet=packet, snapshot=snapshot, verification_flags=_verification_flags())
    assert result.ok is True
    assert result.effects is not None
    assert int(result.effects["reward_amount"]) == 4
    assert bool(result.effects["paid"]) is True
    assert result.state_after is not None
    assert int(result.state_after["reward_pool_balance"]) == 16
    assert int(result.state_after["total_paid"]) == 4
    assert result.claimed_slots_after[packet.assigned_slot] == packet.proposal_hash


def test_build_submit_proof_packet_rejects_duplicate_proposal_hash() -> None:
    claim = _claim()
    proposal_hash = claim["body"]["proposal_hash"]
    snapshot = _snapshot(claimed_slots={3: proposal_hash})
    with pytest.raises(ValueError, match="already claimed"):
        build_submit_proof_packet(claim_artifact=claim, snapshot=snapshot, verification_flags=_verification_flags())


def test_copied_proof_cannot_earn_second_reward_after_first_payment() -> None:
    claim = _claim()
    snapshot = _snapshot()
    packet = build_submit_proof_packet(
        claim_artifact=claim,
        snapshot=snapshot,
        verification_flags=_verification_flags(),
    )
    first = apply_submit_proof_packet(
        packet=packet,
        snapshot=snapshot,
        verification_flags=_verification_flags(),
    )
    assert first.ok is True

    next_snapshot = _snapshot(
        reward_pool_balance=16,
        total_paid=4,
        claimed_slots=dict(first.claimed_slots_after),
    )
    copied_packet = build_submit_proof_packet(
        claim_artifact=_claim(round_id="r2", reward_pool_before=16),
        snapshot=_snapshot(reward_pool_balance=16, total_paid=0),
        verification_flags=_verification_flags(),
    )

    second = apply_submit_proof_packet(
        packet=copied_packet,
        snapshot=next_snapshot,
        verification_flags=_verification_flags(),
    )

    assert second.ok is False
    assert second.error_code == "InvalidPacket"
    assert second.error_message == "proposal_hash already claimed"


def test_build_submit_proof_packet_rejects_stale_snapshot_budget() -> None:
    claim = _claim()
    snapshot = _snapshot(reward_pool_balance=19, total_paid=1)
    with pytest.raises(ValueError, match="reward_pool_before does not match snapshot"):
        build_submit_proof_packet(claim_artifact=claim, snapshot=snapshot, verification_flags=_verification_flags())


def test_assign_proposal_slot_linear_probe() -> None:
    claim = _claim()
    proposal_hash = claim["body"]["proposal_hash"]
    preferred = preferred_proposal_slot(proposal_hash)
    occupied_hash = "sha256:occupied"
    assigned, already = assign_proposal_slot(proposal_hash=proposal_hash, claimed_slots={preferred: occupied_hash})
    assert already is False
    assert assigned == (preferred + 1) % 8


def test_assign_proposal_slot_rejects_full_registry() -> None:
    claim = _claim()
    occupied = {i: f"sha256:occupied{i}" for i in range(8)}
    with pytest.raises(ValueError, match="no free proposal slots"):
        assign_proposal_slot(proposal_hash=claim["body"]["proposal_hash"], claimed_slots=occupied)


def test_apply_submit_proof_packet_rejects_tampered_packet_fields() -> None:
    claim = _claim()
    snapshot = _snapshot()
    packet = build_submit_proof_packet(claim_artifact=claim, snapshot=snapshot, verification_flags=_verification_flags())
    tampered_packet = ProofMiningManagerPacket(
        claim=packet.claim,
        state_before=packet.state_before,
        command_tag=packet.command_tag,
        command_args={
            "proposal_slot": (packet.assigned_slot + 1) % 8,
            "prover_id": packet.command_args["prover_id"],
            "proof_ok": True,
            "binding_ok": True,
            "policy_ok": True,
            "nonce_ok": True,
        },
        assigned_slot=(packet.assigned_slot + 1) % 8,
        proposal_hash=packet.proposal_hash,
    )
    result = apply_submit_proof_packet(packet=tampered_packet, snapshot=snapshot, verification_flags=_verification_flags())
    assert result.ok is False
    assert result.error_code == "InvalidPacket"
    assert result.error_message == "packet fields do not match claim and snapshot"
