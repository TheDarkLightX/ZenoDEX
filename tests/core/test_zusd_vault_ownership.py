from __future__ import annotations

import pytest

from src.core.zusd_vault_ownership import (
    authorize_vault_owner_action,
    finalize_vault_owner_transition,
    vault_owner_invariant_error,
)

ALICE = "0x" + "11" * 48
BOB = "0x" + "22" * 48


def test_empty_vault_is_unowned_and_nonempty_vault_is_owned() -> None:
    assert (
        vault_owner_invariant_error(
            owner_pubkey=None,
            collateral_e8=0,
            debt_e8=0,
        )
        is None
    )
    assert (
        vault_owner_invariant_error(
            owner_pubkey=ALICE,
            collateral_e8=0,
            debt_e8=0,
        )
        == "empty vault must release vault_owner_pubkey"
    )
    assert (
        vault_owner_invariant_error(
            owner_pubkey=None,
            collateral_e8=1,
            debt_e8=0,
        )
        == "non-empty vault requires vault_owner_pubkey"
    )
    assert (
        vault_owner_invariant_error(
            owner_pubkey=ALICE,
            collateral_e8=1,
            debt_e8=0,
        )
        is None
    )


def test_first_authenticated_deposit_acquires_empty_vault() -> None:
    authorized = authorize_vault_owner_action(
        current_owner_pubkey=None,
        actor_pubkey=ALICE,
        action="deposit_collateral",
        collateral_e8=0,
        debt_e8=0,
    )
    transition = finalize_vault_owner_transition(
        previous_owner_pubkey=None,
        authorized_owner_pubkey=authorized,
        action="deposit_collateral",
        post_collateral_e8=10,
        post_debt_e8=0,
    )

    assert transition.next_owner_pubkey == ALICE
    assert transition.acquired_owner_pubkey == ALICE
    assert transition.released_owner_pubkey is None
    assert transition.effect_fields() == {"vault_owner_acquired_pubkey": ALICE}


@pytest.mark.parametrize(
    "action",
    ["withdraw_collateral", "mint_zusd", "repay_zusd"],
)
def test_non_deposit_owner_action_cannot_acquire_empty_vault(action: str) -> None:
    with pytest.raises(ValueError, match="vault owner not initialized"):
        authorize_vault_owner_action(
            current_owner_pubkey=None,
            actor_pubkey=ALICE,
            action=action,
            collateral_e8=0,
            debt_e8=0,
        )


def test_owner_controlled_mutation_rejects_different_actor() -> None:
    with pytest.raises(ValueError, match="vault owner mismatch"):
        authorize_vault_owner_action(
            current_owner_pubkey=ALICE,
            actor_pubkey=BOB,
            action="deposit_collateral",
            collateral_e8=10,
            debt_e8=0,
        )


def test_permissionless_redemption_preserves_nonempty_vault_owner() -> None:
    authorized = authorize_vault_owner_action(
        current_owner_pubkey=ALICE,
        actor_pubkey=BOB,
        action="redeem_zusd",
        collateral_e8=20,
        debt_e8=10,
    )
    transition = finalize_vault_owner_transition(
        previous_owner_pubkey=ALICE,
        authorized_owner_pubkey=authorized,
        action="redeem_zusd",
        post_collateral_e8=15,
        post_debt_e8=5,
    )

    assert transition.next_owner_pubkey == ALICE
    assert transition.effect_fields() == {}


@pytest.mark.parametrize("action", ["withdraw_collateral", "redeem_zusd", "liquidate"])
def test_empty_terminal_state_releases_owner_for_every_closing_path(action: str) -> None:
    authorized = authorize_vault_owner_action(
        current_owner_pubkey=ALICE,
        actor_pubkey=ALICE if action == "withdraw_collateral" else BOB,
        action=action,
        collateral_e8=10,
        debt_e8=0 if action == "withdraw_collateral" else 5,
    )
    transition = finalize_vault_owner_transition(
        previous_owner_pubkey=ALICE,
        authorized_owner_pubkey=authorized,
        action=action,
        post_collateral_e8=0,
        post_debt_e8=0,
    )

    assert transition.next_owner_pubkey is None
    assert transition.released_owner_pubkey == ALICE
    assert transition.effect_fields() == {"vault_owner_released_pubkey": ALICE}


def test_nonempty_successor_without_owner_rejects() -> None:
    with pytest.raises(ValueError, match="non-empty vault requires"):
        finalize_vault_owner_transition(
            previous_owner_pubkey=None,
            authorized_owner_pubkey=None,
            action="liquidate",
            post_collateral_e8=1,
            post_debt_e8=0,
        )


def test_non_vault_action_cannot_transfer_owner() -> None:
    with pytest.raises(ValueError, match="non-vault action cannot change"):
        finalize_vault_owner_transition(
            previous_owner_pubkey=ALICE,
            authorized_owner_pubkey=BOB,
            action="advance_epoch",
            post_collateral_e8=10,
            post_debt_e8=5,
        )
