from __future__ import annotations

from dataclasses import replace

from src.core.dex import DexState
from src.core.zusd import E8
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    init_monetary_state,
    zusd_global_ledger_consistency_error,
)
from src.state.balances import NATIVE_ASSET, BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

_LOW_ASSET = NATIVE_ASSET
_HIGH_ASSET = "0x" + "ff" * 32
_WALLET = "0x" + "31" * 48
_ATTACKER = "0x" + "32" * 48


def _pool(
    *,
    pool_id_byte: str,
    asset0: str,
    asset1: str,
    reserve0: int,
    reserve1: int,
) -> PoolState:
    return PoolState(
        pool_id="0x" + pool_id_byte * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=30,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _monetary_state_with_free_debt(config: ZUSDMonetaryConfig, amount_e8: int):
    monetary = init_monetary_state(config)
    return replace(
        monetary,
        core=replace(
            monetary.core,
            debt_e8=amount_e8,
            free_debt_e8=amount_e8,
        ),
    )


def test_global_cover_counts_dex_pool_reserves_on_both_asset_sides() -> None:
    config = ZUSDMonetaryConfig(chain_id="tau-global-cover-pools")
    zusd_asset = config.zusd_asset
    balances = BalanceTable()
    balances.set(_WALLET, zusd_asset, 100)
    pool_asset0 = _pool(
        pool_id_byte="41",
        asset0=zusd_asset,
        asset1=_HIGH_ASSET,
        reserve0=500,
        reserve1=2_000,
    )
    pool_asset1 = _pool(
        pool_id_byte="42",
        asset0=_LOW_ASSET,
        asset1=zusd_asset,
        reserve0=3_000,
        reserve1=400,
    )
    pools = {
        pool_asset0.pool_id: pool_asset0,
        pool_asset1.pool_id: pool_asset1,
    }
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())
    monetary = _monetary_state_with_free_debt(config, 1_000 * E8)

    assert (
        zusd_global_ledger_consistency_error(
            config=config,
            state=state,
            monetary_state=monetary,
        )
        is None
    )


def test_global_cover_rejects_counterfeit_wallet_supply_masked_by_dex_pool_omission() -> None:
    config = ZUSDMonetaryConfig(chain_id="tau-global-cover-counterfeit")
    zusd_asset = config.zusd_asset
    balances = BalanceTable()
    balances.set(_WALLET, zusd_asset, 100)
    pool = _pool(
        pool_id_byte="51",
        asset0=_LOW_ASSET,
        asset1=zusd_asset,
        reserve0=5_000,
        reserve1=900,
    )
    state = DexState(
        balances=balances,
        pools={pool.pool_id: pool},
        lp_balances=LPTable(),
    )
    monetary = _monetary_state_with_free_debt(config, 1_000 * E8)

    assert (
        zusd_global_ledger_consistency_error(
            config=config,
            state=state,
            monetary_state=monetary,
        )
        is None
    )

    forged_balances = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        forged_balances.set(pubkey, asset, amount)
    forged_balances.set(_ATTACKER, zusd_asset, 900)
    forged_state = replace(state, balances=forged_balances)

    assert zusd_global_ledger_consistency_error(
        config=config,
        state=forged_state,
        monetary_state=monetary,
    ) == (f"free debt liability cover mismatch (expected {1_900 * E8}, got {1_000 * E8})")
    assert state.balances.get(_ATTACKER, zusd_asset) == 0
    assert pool.reserve1 == 900


def test_global_cover_is_invariant_under_ordinary_wallet_transfer() -> None:
    config = ZUSDMonetaryConfig(chain_id="tau-global-cover-transfer")
    zusd_asset = config.zusd_asset
    monetary = _monetary_state_with_free_debt(config, 100 * E8)

    before_balances = BalanceTable()
    before_balances.set(_WALLET, zusd_asset, 100)
    before = DexState(balances=before_balances, pools={}, lp_balances=LPTable())

    after_balances = BalanceTable()
    after_balances.set(_WALLET, zusd_asset, 60)
    after_balances.set(_ATTACKER, zusd_asset, 40)
    after = replace(before, balances=after_balances)

    for state in (before, after):
        assert (
            zusd_global_ledger_consistency_error(
                config=config,
                state=state,
                monetary_state=monetary,
            )
            is None
        )
