from __future__ import annotations

from dataclasses import FrozenInstanceError

import pytest

from src.core.proof_mining_payout import (
    NativeBalanceEffect,
    ProofMiningPayoutPlan,
    ProofMiningPayoutRejectCode,
    ProofMiningPayoutRejected,
    plan_proof_mining_payout,
)

POOL = "0x" + "11" * 48
RECIPIENT = "0x" + "22" * 48


def test_payout_plan_conserves_native_value_over_bounded_domain() -> None:
    for pool_balance_before in range(1, 13):
        for recipient_balance_before in range(0, 13):
            for reward_amount in range(1, pool_balance_before + 1):
                decision = plan_proof_mining_payout(
                    reward_pool_pubkey=POOL,
                    recipient_pubkey=RECIPIENT,
                    reward_amount_base_units=reward_amount,
                    reward_pool_balance_base_units=pool_balance_before,
                    recipient_balance_base_units=recipient_balance_before,
                )

                assert isinstance(decision, ProofMiningPayoutPlan)
                total_before = pool_balance_before + recipient_balance_before
                total_after = (
                    decision.reward_pool_balance_after_base_units
                    + decision.recipient_balance_after_base_units
                )
                assert total_after == total_before
                assert sum(effect.delta_base_units for effect in decision.effects) == 0
                assert [effect.pubkey for effect in decision.effects] == sorted((POOL, RECIPIENT))


def test_payout_plan_canonicalizes_reversed_participant_order_without_rebinding_deltas() -> None:
    decision = plan_proof_mining_payout(
        reward_pool_pubkey=RECIPIENT,
        recipient_pubkey=POOL,
        reward_amount_base_units=4,
        reward_pool_balance_base_units=20,
        recipient_balance_base_units=7,
    )

    assert isinstance(decision, ProofMiningPayoutPlan)
    assert decision.effects == (
        # Canonical key order puts the recipient first in this case.
        NativeBalanceEffect(pubkey=POOL, delta_base_units=4),
        NativeBalanceEffect(pubkey=RECIPIENT, delta_base_units=-4),
    )
    assert decision.reward_pool_balance_after_base_units == 16
    assert decision.recipient_balance_after_base_units == 11
    assert sum(effect.delta_base_units for effect in decision.effects) == 0


def test_payout_plan_rejects_self_payment_as_unrepresentable_plan() -> None:
    decision = plan_proof_mining_payout(
        reward_pool_pubkey=POOL,
        recipient_pubkey=POOL,
        reward_amount_base_units=4,
        reward_pool_balance_base_units=20,
        recipient_balance_base_units=20,
    )

    assert decision == ProofMiningPayoutRejected(ProofMiningPayoutRejectCode.SELF_PAYMENT)
    assert decision.message == "proof mining reward recipient must differ from reward pool"


@pytest.mark.parametrize(
    ("overrides", "expected_code"),
    [
        ({"reward_pool_pubkey": ""}, ProofMiningPayoutRejectCode.INVALID_PARTICIPANT),
        ({"reward_pool_pubkey": "11" * 48}, ProofMiningPayoutRejectCode.INVALID_PARTICIPANT),
        ({"recipient_pubkey": "participant"}, ProofMiningPayoutRejectCode.INVALID_PARTICIPANT),
        ({"recipient_pubkey": None}, ProofMiningPayoutRejectCode.INVALID_PARTICIPANT),
        ({"reward_amount_base_units": 0}, ProofMiningPayoutRejectCode.INVALID_AMOUNT),
        ({"reward_amount_base_units": True}, ProofMiningPayoutRejectCode.INVALID_AMOUNT),
        ({"reward_amount_base_units": "4"}, ProofMiningPayoutRejectCode.INVALID_AMOUNT),
        ({"reward_pool_balance_base_units": -1}, ProofMiningPayoutRejectCode.INVALID_BALANCE),
        ({"reward_pool_balance_base_units": False}, ProofMiningPayoutRejectCode.INVALID_BALANCE),
        ({"recipient_balance_base_units": -1}, ProofMiningPayoutRejectCode.INVALID_BALANCE),
        ({"recipient_balance_base_units": 1.5}, ProofMiningPayoutRejectCode.INVALID_BALANCE),
        ({"reward_amount_base_units": 21}, ProofMiningPayoutRejectCode.INSUFFICIENT_POOL),
    ],
)
def test_payout_plan_rejects_invalid_or_unfunded_inputs(
    overrides: dict[str, object],
    expected_code: ProofMiningPayoutRejectCode,
) -> None:
    inputs: dict[str, object] = {
        "reward_pool_pubkey": POOL,
        "recipient_pubkey": RECIPIENT,
        "reward_amount_base_units": 4,
        "reward_pool_balance_base_units": 20,
        "recipient_balance_base_units": 7,
    }
    inputs.update(overrides)

    decision = plan_proof_mining_payout(**inputs)

    assert decision == ProofMiningPayoutRejected(expected_code)


def test_payout_plan_is_deeply_immutable_and_bound_to_participants() -> None:
    decision = plan_proof_mining_payout(
        reward_pool_pubkey=POOL,
        recipient_pubkey=RECIPIENT,
        reward_amount_base_units=4,
        reward_pool_balance_base_units=20,
        recipient_balance_base_units=7,
    )

    assert isinstance(decision, ProofMiningPayoutPlan)
    assert decision.reward_pool_pubkey == POOL
    assert decision.recipient_pubkey == RECIPIENT
    assert decision.reward_pool_balance_after_base_units == 16
    assert decision.recipient_balance_after_base_units == 11
    assert isinstance(decision.effects, tuple)
    with pytest.raises(FrozenInstanceError):
        decision.reward_amount_base_units = 5  # type: ignore[misc]
    with pytest.raises(FrozenInstanceError):
        decision.effects[0].delta_base_units = 0  # type: ignore[misc]
