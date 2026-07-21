from __future__ import annotations

from dataclasses import FrozenInstanceError

import pytest

from src.core.vault_claimant import (
    ACC_SCALE,
    ActivateStake,
    ClaimRewards,
    ClaimantVaultState,
    DepositRewards,
    DrainResidue,
    QueueStake,
    Unstake,
    VaultAccount,
    init_claimant_vault_state,
    step_claimant_vault,
)


def _apply(state: ClaimantVaultState, command):
    result = step_claimant_vault(state, command)
    assert result.ok, result.error
    assert result.state is not None
    assert result.effects is not None
    return result.state, result.effects


def _activate(
    state: ClaimantVaultState,
    claimant: str,
    shares: int,
    *,
    queue_nonce: int = 1,
    activation_nonce: int = 2,
) -> ClaimantVaultState:
    state, queue_effects = _apply(
        state,
        QueueStake(claimant=claimant, shares=shares, nonce=queue_nonce),
    )
    assert queue_effects.share_transfers[0].direction == "INTO_VAULT"
    state, activation_effects = _apply(
        state,
        ActivateStake(
            claimant=claimant,
            shares=shares,
            nonce=activation_nonce,
        ),
    )
    assert activation_effects.share_transfers == ()
    return state


def _assert_conservation(state: ClaimantVaultState) -> None:
    assert (
        state.reward_balance
        + state.cumulative_claimed
        + state.cumulative_drained
        == state.cumulative_deposited
    )
    assert state.aggregate_owned_rewards + state.explicit_residue == state.reward_balance
    assert state.total_active_shares == sum(
        account.active_shares for account in state.accounts
    )
    assert state.total_pending_shares == sum(
        account.pending_shares for account in state.accounts
    )


def test_two_stakers_claim_only_their_exact_entitlement() -> None:
    state = _activate(init_claimant_vault_state(), "alice", 100)
    state, _ = _apply(state, DepositRewards(amount=100, funding_nonce=1))
    state = _activate(state, "bob", 100)
    state, _ = _apply(state, DepositRewards(amount=100, funding_nonce=2))

    state, alice_effects = _apply(state, ClaimRewards(claimant="alice", nonce=3))
    state, bob_effects = _apply(state, ClaimRewards(claimant="bob", nonce=3))

    assert alice_effects.reward_transfers[0].amount == 150
    assert bob_effects.reward_transfers[0].amount == 50
    assert state.reward_balance == 0
    assert state.cumulative_claimed == 200
    _assert_conservation(state)


def test_three_stakers_joining_at_different_times_cannot_capture_history() -> None:
    state = _activate(init_claimant_vault_state(), "alice", 100)
    state, _ = _apply(state, DepositRewards(amount=90, funding_nonce=1))
    state = _activate(state, "bob", 100)
    state, _ = _apply(state, DepositRewards(amount=60, funding_nonce=2))
    state = _activate(state, "carol", 100)
    state, _ = _apply(state, DepositRewards(amount=90, funding_nonce=3))

    state, alice = _apply(state, ClaimRewards(claimant="alice", nonce=3))
    state, bob = _apply(state, ClaimRewards(claimant="bob", nonce=3))
    state, carol = _apply(state, ClaimRewards(claimant="carol", nonce=3))

    assert alice.reward_transfers[0].amount == 150
    assert bob.reward_transfers[0].amount == 60
    assert carol.reward_transfers[0].amount == 30
    assert state.cumulative_claimed == 240
    _assert_conservation(state)


def test_pending_and_late_activation_never_earn_prior_rewards() -> None:
    state = init_claimant_vault_state()
    state, _ = _apply(state, QueueStake(claimant="alice", shares=100, nonce=1))
    state, _ = _apply(state, DepositRewards(amount=70, funding_nonce=1))
    assert state.explicit_residue == 70
    assert state.aggregate_owned_rewards == 0

    state, _ = _apply(state, ActivateStake(claimant="alice", shares=100, nonce=2))
    state, _ = _apply(state, DepositRewards(amount=30, funding_nonce=2))
    state, effects = _apply(state, ClaimRewards(claimant="alice", nonce=3))

    assert effects.reward_transfers[0].amount == 30
    assert state.explicit_residue == 70
    _assert_conservation(state)


def test_unstake_settles_and_preserves_claimable_reward() -> None:
    state = _activate(init_claimant_vault_state(), "alice", 100)
    state, _ = _apply(state, DepositRewards(amount=100, funding_nonce=1))
    state, effects = _apply(state, Unstake(claimant="alice", shares=100, nonce=3))

    account = state.account("alice")
    assert account is not None
    assert account.active_shares == 0
    assert account.claimable == 100
    assert effects.share_transfers[0].direction == "OUT_OF_VAULT"

    state, claim_effects = _apply(state, ClaimRewards(claimant="alice", nonce=4))
    assert claim_effects.reward_transfers[0].amount == 100
    _assert_conservation(state)


def test_claim_replay_and_wrong_nonce_are_exact_no_ops() -> None:
    state = _activate(init_claimant_vault_state(), "alice", 100)
    state, _ = _apply(state, DepositRewards(amount=100, funding_nonce=1))
    claimed_state, _ = _apply(state, ClaimRewards(claimant="alice", nonce=3))

    replay = step_claimant_vault(
        claimed_state,
        ClaimRewards(claimant="alice", nonce=3),
    )
    skipped = step_claimant_vault(
        claimed_state,
        QueueStake(claimant="alice", shares=1, nonce=5),
    )

    assert replay.ok is False
    assert replay.state is None
    assert replay.effects is None
    assert skipped.ok is False
    assert skipped.state is None
    assert skipped.effects is None
    assert claimed_state.account("alice").last_nonce == 3  # type: ignore[union-attr]


def test_claim_order_does_not_change_final_state() -> None:
    initial = _activate(init_claimant_vault_state(), "alice", 100)
    initial = _activate(initial, "bob", 100)
    initial, _ = _apply(initial, DepositRewards(amount=200, funding_nonce=1))

    first, _ = _apply(initial, ClaimRewards(claimant="alice", nonce=3))
    first, _ = _apply(first, ClaimRewards(claimant="bob", nonce=3))

    second, _ = _apply(initial, ClaimRewards(claimant="bob", nonce=3))
    second, _ = _apply(second, ClaimRewards(claimant="alice", nonce=3))

    assert first == second
    _assert_conservation(first)


def test_tiny_reward_remains_explicit_until_enough_is_owned() -> None:
    state = _activate(init_claimant_vault_state(), "alice", 3)
    state, first = _apply(state, DepositRewards(amount=1, funding_nonce=1))
    assert first.accumulator_delta == ACC_SCALE // 3
    assert state.aggregate_owned_rewards == 0
    assert state.explicit_residue == 1

    state, _ = _apply(state, DepositRewards(amount=2, funding_nonce=2))
    assert state.aggregate_owned_rewards == 2
    assert state.explicit_residue == 1
    state, claim = _apply(state, ClaimRewards(claimant="alice", nonce=3))
    assert claim.reward_transfers[0].amount == 2
    _assert_conservation(state)


def test_no_staker_rewards_can_only_leave_through_terminal_drain() -> None:
    state, _ = _apply(
        init_claimant_vault_state(),
        DepositRewards(amount=77, funding_nonce=1),
    )
    assert state.explicit_residue == 77

    active = _activate(state, "alice", 1)
    rejected = step_claimant_vault(
        active,
        DrainResidue(recipient="treasury", funding_nonce=2),
    )
    assert rejected.ok is False
    assert rejected.state is None
    assert rejected.effects is None

    active, _ = _apply(active, Unstake(claimant="alice", shares=1, nonce=3))
    final, effects = _apply(
        active,
        DrainResidue(recipient="treasury", funding_nonce=2),
    )
    assert effects.reward_transfers[0].amount == 77
    assert effects.reward_transfers[0].reason == "RESIDUE_DRAIN"
    assert final.reward_balance == 0
    assert final.explicit_residue == 0
    assert final.cumulative_drained == 77
    _assert_conservation(final)


def test_forged_claimant_ownership_and_duplicate_claimants_reject() -> None:
    with pytest.raises(ValueError, match="reward_balance"):
        ClaimantVaultState(
            accounts=(VaultAccount(claimant="alice", claimable=2),),
            reward_balance=1,
            cumulative_deposited=1,
        )
    with pytest.raises(ValueError, match="duplicate"):
        ClaimantVaultState(
            accounts=(
                VaultAccount(claimant="alice"),
                VaultAccount(claimant="alice"),
            )
        )


def test_account_order_is_canonical_and_state_is_immutable() -> None:
    state = ClaimantVaultState(
        accounts=(
            VaultAccount(claimant="carol"),
            VaultAccount(claimant="alice"),
            VaultAccount(claimant="bob"),
        )
    )
    assert tuple(account.claimant for account in state.accounts) == (
        "alice",
        "bob",
        "carol",
    )
    with pytest.raises(FrozenInstanceError):
        state.reward_balance = 1  # type: ignore[misc]
