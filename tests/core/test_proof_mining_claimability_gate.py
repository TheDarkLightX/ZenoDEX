from __future__ import annotations

import pytest

from src.core.proof_mining_claimability_gate import (
    REJECT_DISABLED,
    REJECT_MANAGER_REJECTED,
    REJECT_NEGATIVE_POOL_BALANCE,
    REJECT_OK,
    REJECT_PROPOSAL_HASH_MISMATCH,
    REJECT_RUNTIME_POOL_BALANCE_DRIFT,
    REJECT_RUNTIME_POOL_PUBKEY_MISMATCH,
    REJECT_WINNER_MISMATCH,
    evaluate_proof_mining_claimability_gate,
)


def _valid_gate_kwargs() -> dict[str, object]:
    return {
        "reward_pool_configured": True,
        "winner_matches_sender": True,
        "proposal_hash_matches_context": True,
        "reward_pool_balance_non_negative": True,
        "runtime_state_present": True,
        "reward_pool_pubkey_matches_state": True,
        "reward_pool_balance_matches_state": True,
        "manager_ok": True,
        "reward_amount": 4,
        "reward_pool_before": 20,
        "reward_pool_after": 16,
    }


def test_claimability_gate_accepts_valid_runtime_backed_claim() -> None:
    outcome = evaluate_proof_mining_claimability_gate(**_valid_gate_kwargs())

    assert outcome.enabled is True
    assert outcome.claimable is True
    assert outcome.reject_code == REJECT_OK
    assert outcome.reward_amount == 4
    assert outcome.reward_pool_before == 20
    assert outcome.reward_pool_after == 16
    assert outcome.checks["runtime_state_present"] is True
    assert outcome.checks["reward_pool_balance_matches_state"] is True


@pytest.mark.parametrize(
    ("overrides", "expected_reject"),
    [
        ({"reward_pool_configured": False}, REJECT_DISABLED),
        ({"winner_matches_sender": False}, REJECT_WINNER_MISMATCH),
        ({"proposal_hash_matches_context": False}, REJECT_PROPOSAL_HASH_MISMATCH),
        ({"reward_pool_balance_non_negative": False}, REJECT_NEGATIVE_POOL_BALANCE),
        ({"reward_pool_pubkey_matches_state": False}, REJECT_RUNTIME_POOL_PUBKEY_MISMATCH),
        ({"reward_pool_balance_matches_state": False}, REJECT_RUNTIME_POOL_BALANCE_DRIFT),
        ({"manager_ok": False}, REJECT_MANAGER_REJECTED),
    ],
)
def test_claimability_gate_rejects_in_stable_priority_order(
    overrides: dict[str, object], expected_reject: str
) -> None:
    kwargs = _valid_gate_kwargs()
    kwargs.update(overrides)

    outcome = evaluate_proof_mining_claimability_gate(**kwargs)

    assert outcome.claimable is False
    assert outcome.reject_code == expected_reject


def test_claimability_gate_runtime_state_absence_keeps_runtime_checks_nonblocking() -> None:
    kwargs = _valid_gate_kwargs()
    kwargs.update(
        {
            "runtime_state_present": False,
            "reward_pool_pubkey_matches_state": False,
            "reward_pool_balance_matches_state": False,
        }
    )

    outcome = evaluate_proof_mining_claimability_gate(**kwargs)

    assert outcome.claimable is True
    assert outcome.reject_code == REJECT_OK
    assert outcome.checks["runtime_state_present"] is False
    assert outcome.checks["reward_pool_pubkey_matches_state"] is False
    assert outcome.checks["reward_pool_balance_matches_state"] is False


@pytest.mark.parametrize(
    ("overrides", "match"),
    [
        ({"reward_amount": -1}, "reward_amount must be non-negative"),
        ({"reward_pool_before": -1}, "reward_pool_before must be non-negative"),
        ({"reward_pool_after": -1}, "reward_pool_after must be non-negative"),
        ({"reward_pool_after": 21}, "reward_pool_after must not exceed reward_pool_before"),
        ({"reward_amount": 5}, "reward_amount must equal reward_pool_before - reward_pool_after"),
        ({"reward_amount": True}, "reward_amount must be an int"),
    ],
)
def test_claimability_gate_rejects_invalid_payout_arithmetic(
    overrides: dict[str, object], match: str
) -> None:
    kwargs = _valid_gate_kwargs()
    kwargs.update(overrides)

    with pytest.raises((TypeError, ValueError), match=match):
        evaluate_proof_mining_claimability_gate(**kwargs)
