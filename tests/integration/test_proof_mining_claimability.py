from __future__ import annotations

import json
from types import SimpleNamespace

import pytest

from src.core.dex import DexState
from src.core.proof_mining_claims import build_proof_mining_claim
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.proof_mining_claimability import evaluate_proof_mining_claimability
from src.integration.proof_mining_context import ProofMiningContext, proof_mining_context_to_obj
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
    context = _context_from_claim(claim)

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool: 20, sender: 0},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )

    assert status.enabled is True
    assert status.claimable is True
    assert status.error is None
    assert status.reward_amount == 4
    assert status.reward_pool_before == 20
    assert status.reward_pool_after == 16
    assert status.checks["runtime_state_present"] is False
    assert status.checks["verified_context_present"] is True
    assert status.checks["runtime_apply_ok"] is True


def test_claimability_resolves_raw_tau_balance_keys() -> None:
    sender_raw = "11" * 48
    sender = "0x" + sender_raw
    reward_pool_raw = "99" * 48
    reward_pool = "0x" + reward_pool_raw
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool_raw: 20, sender_raw: 0},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )

    assert status.claimable is True
    assert status.reward_pool_before == 20
    assert status.checks["chain_balance_identity_unambiguous"] is True


def test_claimability_rejects_duplicate_tau_spellings_before_manager_apply(monkeypatch) -> None:
    sender = "0x" + "11" * 48
    reward_pool_raw = "99" * 48
    reward_pool = "0x" + reward_pool_raw
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)

    def fail_if_manager_called(**_kwargs):
        raise AssertionError("ambiguous Tau identities must reject before manager application")

    monkeypatch.setattr(
        "src.integration.proof_mining_claimability.apply_proof_mining_claim",
        fail_if_manager_called,
    )
    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool_raw: 20, reward_pool: 20},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )

    assert status.claimable is False
    assert status.error is not None
    assert "ambiguous identity spellings" in status.error
    assert status.checks["chain_balance_identity_unambiguous"] is False
    assert status.checks["runtime_apply_ok"] is False


def test_claimability_rejects_reward_pool_self_payment_before_manager_apply() -> None:
    reward_pool = "0x" + "99" * 48
    claim = _claim(miner_id=reward_pool, reward_pool_before=20)
    context = _context_from_claim(claim)

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool: 20},
        claim_artifact=claim,
        tx_sender_pubkey=reward_pool,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )

    assert status.enabled is True
    assert status.claimable is False
    assert status.error == "proof mining reward recipient must differ from reward pool"
    assert status.checks["winner_matches_sender"] is True
    assert status.checks["recipient_differs_from_reward_pool"] is False
    assert status.checks["runtime_apply_ok"] is False


def test_claimability_accepts_asset_scoped_reward_pool_balance() -> None:
    sender = "0x" + "11" * 48
    reward_pool = "0x" + "99" * 48
    reward_asset = "0x" + "aa" * 32
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        reward_asset_id=reward_asset,
        app_state_json="",
        chain_balances={reward_pool: {reward_asset: 20}},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )

    assert status.claimable is True
    assert status.reward_pool_before == 20
    assert status.reward_pool_after == 16


def test_claimability_requires_verified_context() -> None:
    sender = "0x" + "10" * 48
    reward_pool = "0x" + "98" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool: 20, sender: 0},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
    )

    assert status.claimable is False
    assert status.error == "proof mining claim requires verified DEX proof context"
    assert status.checks["verified_context_present"] is False


def test_claimability_rejects_inadmissible_claim_artifact() -> None:
    sender = "0x" + "10" * 48
    reward_pool = "0x" + "98" * 48
    claim = build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": "job-inadmissible",
            "winner": {
                "miner_id": sender,
                "witness_sha256": "witness-inadmissible",
                "improvement_u64": 9,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id="round-inadmissible",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=1,
        chain_id="tau-testnet-alpha",
        prev_state_hash="sha256:prev-inadmissible",
        batch_hash="sha256:batch-inadmissible",
        dex_hash_after="sha256:after-inadmissible",
        policy_ok=0,
        unclaimed_ok=0,
        allow_rejected=True,
    )

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool: 20, sender: 0},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(_context_from_claim(claim)),
    )

    assert status.claimable is False
    assert status.error == "proof-mining claim inadmissible"
    assert status.reward_amount is None
    assert status.checks["sender_valid"] is True
    assert status.checks["claim_valid"] is False
    assert status.checks["runtime_apply_ok"] is False


def test_claimability_rejects_proposal_hash_mismatch() -> None:
    sender = "0x" + "22" * 48
    reward_pool = "0x" + "88" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool: 20, sender: 0},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash="sha256:not-the-same",
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )

    assert status.claimable is False
    assert status.error == "proof mining claim proposal_hash mismatch"
    assert status.checks["claim_valid"] is True
    assert status.checks["proposal_hash_matches_context"] is False


def test_claimability_rejects_reward_pool_balance_drift_with_runtime_state() -> None:
    sender = "0x" + "33" * 48
    reward_pool = "0x" + "77" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)
    runtime_state = initialize_proof_mining_runtime_state(
        reward_pool_pubkey=reward_pool,
        reward_pool_balance=20,
        claim_artifact=claim,
    )
    next_state, result = apply_proof_mining_claim(
        runtime_state=runtime_state,
        claim_artifact=claim,
        actual_reward_pool_balance=20,
        proof_mining_context=context,
    )
    assert result.ok is True

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json=_wrapped_app_state(next_state),
        chain_balances={reward_pool: 15, sender: 4},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )

    assert status.claimable is False
    assert status.error == "proof mining reward pool balance drift"
    assert status.checks["runtime_state_present"] is True
    assert status.checks["reward_pool_pubkey_matches_state"] is True
    assert status.checks["reward_pool_balance_matches_state"] is False


def test_claimability_helpers_fail_closed_on_bad_inputs() -> None:
    from src.integration import proof_mining_claimability as mod

    with pytest.raises(TypeError, match="claim payload must be an object"):
        mod._require_mapping([], name="claim payload")

    with pytest.raises(TypeError, match="reward_pool_pubkey must be a string"):
        mod._canonical_pubkey(7, name="reward_pool_pubkey")

    with pytest.raises(
        ValueError, match="reward_pool_pubkey must be a canonical 48-byte hex pubkey"
    ):
        mod._canonical_pubkey("0x1234", name="reward_pool_pubkey")

    with pytest.raises(ValueError, match="invalid app_state_json"):
        mod._load_proof_mining_state_from_app_state("{")

    with pytest.raises(ValueError, match="app_state_json must decode to an object"):
        mod._load_proof_mining_state_from_app_state("[]")

    assert (
        mod._load_proof_mining_state_from_app_state(json.dumps({"schema": "wrong/schema"})) is None
    )
    assert (
        mod._load_proof_mining_state_from_app_state(
            json.dumps({"schema": "zenodex/tau_app_state/v1"})
        )
        is None
    )

    with pytest.raises(TypeError, match="app_state.proof_mining must be an object"):
        mod._load_proof_mining_state_from_app_state(
            json.dumps({"schema": "zenodex/tau_app_state/v1", "proof_mining": []})
        )


def test_claimability_rejects_disabled_pool_and_winner_mismatch() -> None:
    sender = "0x" + "44" * 48
    reward_pool = "0x" + "66" * 48
    claim = _claim(miner_id="0x" + "55" * 48, reward_pool_before=20)
    context = _context_from_claim(claim)

    disabled = evaluate_proof_mining_claimability(
        reward_pool_pubkey=None,
        app_state_json="",
        chain_balances={},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )
    assert disabled.enabled is False
    assert disabled.claimable is False
    assert disabled.error == "proof mining disabled (set TAU_DEX_PROOF_MINING_POOL_PUBKEY)"

    mismatch = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool: 20},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )
    assert mismatch.claimable is False
    assert mismatch.error == "proof mining winner.miner_id mismatch"
    assert mismatch.checks["claim_valid"] is True
    assert mismatch.checks["winner_matches_sender"] is False


def test_claimability_rejects_negative_pool_balance_and_state_pubkey_mismatch() -> None:
    sender = "0x" + "77" * 48
    reward_pool = "0x" + "88" * 48
    other_pool = "0x" + "99" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)

    negative = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool: -1},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )
    assert negative.claimable is False
    assert negative.error == "reward pool chain balance must be non-negative"
    assert negative.checks["reward_pool_balance_non_negative"] is False

    runtime_state = initialize_proof_mining_runtime_state(
        reward_pool_pubkey=other_pool,
        reward_pool_balance=20,
        claim_artifact=claim,
    )
    mismatch = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json=_wrapped_app_state(runtime_state),
        chain_balances={reward_pool: 20},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )
    assert mismatch.claimable is False
    assert mismatch.error == "proof mining reward pool pubkey mismatch"
    assert mismatch.checks["runtime_state_present"] is True
    assert mismatch.checks["reward_pool_pubkey_matches_state"] is False


def test_claimability_surfaces_runtime_rejection(monkeypatch) -> None:
    from src.integration import proof_mining_claimability as mod

    sender = "0x" + "aa" * 48
    reward_pool = "0x" + "bb" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)
    runtime_state = initialize_proof_mining_runtime_state(
        reward_pool_pubkey=reward_pool,
        reward_pool_balance=20,
        claim_artifact=claim,
    )

    monkeypatch.setattr(
        mod,
        "apply_proof_mining_claim",
        lambda **_kwargs: (
            runtime_state,
            SimpleNamespace(ok=False, effects=None, error_message=None),
        ),
    )

    status = mod.evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json="",
        chain_balances={reward_pool: 20},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )

    assert status.claimable is False
    assert status.error == "proof mining manager rejected"
    assert status.checks["runtime_apply_ok"] is False


def test_claimability_public_status_includes_runtime_backed_success() -> None:
    sender = "0x" + "cc" * 48
    reward_pool = "0x" + "dd" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)
    runtime_state = initialize_proof_mining_runtime_state(
        reward_pool_pubkey=reward_pool,
        reward_pool_balance=20,
        claim_artifact=claim,
    )

    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool,
        app_state_json=_wrapped_app_state(runtime_state),
        chain_balances={reward_pool: 20},
        claim_artifact=claim,
        tx_sender_pubkey=sender,
        expected_proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )
    public = status.to_public_dict()

    assert status.claimable is True
    assert status.checks["runtime_state_present"] is True
    assert status.checks["reward_pool_balance_matches_state"] is True
    assert public["claimable"] is True
    assert public["reward_pool_before"] == 20
    assert public["reward_pool_after"] == 16
