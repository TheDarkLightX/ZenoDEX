from __future__ import annotations

from types import MappingProxyType

import pytest

from src.core.proof_mining_claimability_gate import (
    REJECT_OK,
    REJECT_RECIPIENT_IS_REWARD_POOL,
    evaluate_proof_mining_claimability_gate,
    evaluate_proof_mining_recipient_gate,
)


def _claimability(*, recipient_distinct: bool):
    return evaluate_proof_mining_claimability_gate(
        reward_pool_configured=True,
        winner_matches_sender=True,
        recipient_distinct_from_reward_pool=recipient_distinct,
        proposal_hash_matches_context=True,
        reward_pool_balance_non_negative=True,
        runtime_state_present=False,
        reward_pool_pubkey_matches_state=False,
        reward_pool_balance_matches_state=False,
        manager_ok=True,
        reward_amount=4,
        reward_pool_before=20,
        reward_pool_after=16,
    )


def test_recipient_gate_rejects_reward_pool_alias_and_full_gate_preserves_reject() -> None:
    recipient = evaluate_proof_mining_recipient_gate(
        recipient_distinct_from_reward_pool=False,
    )
    full = _claimability(recipient_distinct=False)

    assert recipient.admitted is False
    assert recipient.reject_code == REJECT_RECIPIENT_IS_REWARD_POOL
    assert full.claimable is False
    assert full.reject_code == REJECT_RECIPIENT_IS_REWARD_POOL
    assert full.checks["recipient_distinct_from_reward_pool"] is False


def test_recipient_gate_accepts_distinct_recipient_and_owns_immutable_checks() -> None:
    recipient = evaluate_proof_mining_recipient_gate(
        recipient_distinct_from_reward_pool=True,
    )
    full = _claimability(recipient_distinct=True)

    assert recipient.admitted is True
    assert recipient.reject_code == REJECT_OK
    assert full.claimable is True
    assert full.reject_code == REJECT_OK
    assert type(full.checks) is MappingProxyType
    with pytest.raises(TypeError):
        full.checks["recipient_distinct_from_reward_pool"] = False  # type: ignore[index]


@pytest.mark.parametrize("hostile", [0, 1, None, "true"])
def test_recipient_gate_rejects_truthy_and_falsy_non_bool_values(hostile: object) -> None:
    with pytest.raises(TypeError, match="recipient_distinct_from_reward_pool must be a bool"):
        evaluate_proof_mining_recipient_gate(
            recipient_distinct_from_reward_pool=hostile,  # type: ignore[arg-type]
        )
