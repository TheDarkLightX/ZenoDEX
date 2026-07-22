from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.zusd import E8, ZUSDCommand, step
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    _apply_one,
    init_monetary_state,
    stability_pool_pubkey,
)
from src.state.balances import NATIVE_ASSET, BalanceTable

ALICE = "0x" + "11" * 48
BOB = "0x" + "22" * 48
ORACLE = "0x" + "33" * 48
ASSET = "0x" + "aa" * 32


def _config() -> ZUSDMonetaryConfig:
    return ZUSDMonetaryConfig(
        chain_id="vault-owner-test",
        oracle_pubkey=ORACLE,
        asset_id=ASSET,
    )


def _core_ok(core, tag: str, **args):
    result = step(core, ZUSDCommand(tag=tag, args=args))
    assert result.ok, result.error
    assert result.state is not None
    return result.state


def _apply(
    *,
    balances: BalanceTable,
    monetary_state,
    action: str,
    sender: str,
    **op_fields: object,
):
    config = _config()
    return _apply_one(
        config=config,
        balances=balances,
        monetary_state=monetary_state,
        op=dict(op_fields),
        action=action,
        sender=sender,
        native_sender=sender,
        zusd_asset=config.zusd_asset,
        sp_pubkey=stability_pool_pubkey(chain_id=config.chain_id),
    )


def test_monetary_state_rejects_both_owner_shape_mismatches() -> None:
    monetary = init_monetary_state(_config())

    with pytest.raises(ValueError, match="empty vault must release"):
        replace(monetary, vault_owner_pubkey=ALICE)

    nonempty_core = _core_ok(
        monetary.core,
        "deposit_collateral",
        amount_e8=E8,
    )
    with pytest.raises(ValueError, match="non-empty vault requires"):
        replace(monetary, core=nonempty_core)


def test_deposit_acquires_withdraw_releases_and_new_actor_can_reacquire() -> None:
    monetary = init_monetary_state(_config())
    balances = BalanceTable()
    balances.set(ALICE, NATIVE_ASSET, 10 * E8)
    balances.set(BOB, NATIVE_ASSET, 10 * E8)

    alice_state, acquired = _apply(
        balances=balances,
        monetary_state=monetary,
        action="deposit_collateral",
        sender=ALICE,
        owner_pubkey=ALICE,
        amount_e8=5 * E8,
    )
    assert alice_state.vault_owner_pubkey == ALICE
    assert alice_state.core.collateral_e8 == 5 * E8
    assert acquired["vault_owner_acquired_pubkey"] == ALICE

    alice_balance_before = balances.get(ALICE, NATIVE_ASSET)
    bob_balance_before = balances.get(BOB, NATIVE_ASSET)
    with pytest.raises(ValueError, match="vault owner mismatch"):
        _apply(
            balances=balances,
            monetary_state=alice_state,
            action="deposit_collateral",
            sender=BOB,
            owner_pubkey=BOB,
            amount_e8=E8,
        )
    assert balances.get(ALICE, NATIVE_ASSET) == alice_balance_before
    assert balances.get(BOB, NATIVE_ASSET) == bob_balance_before

    empty_state, released = _apply(
        balances=balances,
        monetary_state=alice_state,
        action="withdraw_collateral",
        sender=ALICE,
        owner_pubkey=ALICE,
        amount_e8=5 * E8,
    )
    assert empty_state.core.collateral_e8 == 0
    assert empty_state.core.debt_e8 == 0
    assert empty_state.vault_owner_pubkey is None
    assert released["vault_owner_released_pubkey"] == ALICE

    bob_state, reacquired = _apply(
        balances=balances,
        monetary_state=empty_state,
        action="deposit_collateral",
        sender=BOB,
        owner_pubkey=BOB,
        amount_e8=E8,
    )
    assert bob_state.vault_owner_pubkey == BOB
    assert reacquired["vault_owner_acquired_pubkey"] == BOB


def test_permissionless_liquidation_releases_terminal_owner() -> None:
    config = _config()
    monetary = init_monetary_state(config)
    core = monetary.core
    core = _core_ok(core, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    core = _core_ok(core, "deposit_collateral", amount_e8=2 * E8)
    core = _core_ok(core, "mint_zusd", amount_e8=150 * E8)
    core = _core_ok(core, "deposit_sp", amount_e8=150 * E8)
    core = _core_ok(core, "oracle_report", price_e8=70 * E8, auth_ok=True)
    core = _core_ok(core, "oracle_commit", auth_ok=True)
    monetary = replace(
        monetary,
        core=core,
        vault_owner_pubkey=ALICE,
        sp_deposits_e8={ALICE: 150 * E8},
    )

    balances = BalanceTable()
    sp_pubkey = stability_pool_pubkey(chain_id=config.chain_id)
    balances.set(sp_pubkey, config.zusd_asset, 150)

    next_state, effects = _apply(
        balances=balances,
        monetary_state=monetary,
        action="liquidate",
        sender=BOB,
    )

    assert next_state.core.collateral_e8 == 0
    assert next_state.core.debt_e8 == 0
    assert next_state.vault_owner_pubkey is None
    assert effects["vault_owner_released_pubkey"] == ALICE
