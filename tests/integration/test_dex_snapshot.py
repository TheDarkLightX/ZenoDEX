# [TESTER] v1

from __future__ import annotations

import pytest

from src.core.dex import DexState
from src.core.perps import (
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERPS_STATE_VERSION,
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpMarketState,
    PerpsState,
)
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


def test_snapshot_roundtrip_is_deterministic() -> None:
    balances = BalanceTable()
    lp = LPTable()
    pools = {}

    pk = "alice"
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    pool_id = "0x" + "aa" * 32

    balances.set(pk, asset0, 123)
    balances.set(pk, asset1, 456)

    pools[pool_id] = PoolState(
        pool_id=pool_id,
        asset0=min(asset0, asset1),
        asset1=max(asset0, asset1),
        reserve0=1000,
        reserve1=2000,
        fee_bps=30,
        lp_supply=10,
        status=PoolStatus.ACTIVE,
        created_at=1,
    )
    lp.set(pk, pool_id, 7)

    state = DexState(balances=balances, pools=pools, lp_balances=lp)

    snap1 = snapshot_from_state(state)
    state2 = state_from_snapshot(snap1.data)
    snap2 = snapshot_from_state(state2)

    assert snap1.canonical_bytes() == snap2.canonical_bytes()
    assert snap1.commitment_bytes() == snap2.commitment_bytes()


def test_snapshot_sorting_ignores_insertion_order() -> None:
    pk_a = "alice"
    pk_b = "bob"
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    # Insert in one order
    b1 = BalanceTable()
    b1.set(pk_b, asset1, 2)
    b1.set(pk_a, asset0, 1)

    # Insert in the opposite order
    b2 = BalanceTable()
    b2.set(pk_a, asset0, 1)
    b2.set(pk_b, asset1, 2)

    s1 = DexState(balances=b1, pools={}, lp_balances=LPTable())
    s2 = DexState(balances=b2, pools={}, lp_balances=LPTable())

    assert snapshot_from_state(s1).canonical_bytes() == snapshot_from_state(s2).canonical_bytes()


def test_state_from_snapshot_is_fail_closed_on_container_types() -> None:
    base = {
        "version": 1,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
    }

    bad_balances = dict(base)
    bad_balances["balances"] = {}
    with pytest.raises(TypeError):
        state_from_snapshot(bad_balances)

    bad_pools = dict(base)
    bad_pools["pools"] = {}
    with pytest.raises(TypeError):
        state_from_snapshot(bad_pools)

    bad_lp = dict(base)
    bad_lp["lp_balances"] = {}
    with pytest.raises(TypeError):
        state_from_snapshot(bad_lp)


def test_state_from_snapshot_requires_fee_accumulator() -> None:
    snap = {
        "version": 1,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "vault": None,
        "oracle": None,
    }
    with pytest.raises(ValueError):
        state_from_snapshot(snap)


def test_state_from_snapshot_rejects_unknown_version() -> None:
    snap = {
        "version": 3,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
    }
    with pytest.raises(ValueError):
        state_from_snapshot(snap)


def test_snapshot_roundtrip_with_perps_is_deterministic() -> None:
    balances = BalanceTable()
    lp = LPTable()
    pools = {}

    perps_global = {
        "now_epoch": 0,
        "breaker_active": False,
        "breaker_last_trigger_epoch": 0,
        "clearing_price_seen": False,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "oracle_seen": False,
        "oracle_last_update_epoch": 0,
        "index_price_e8": 0,
        "max_oracle_staleness_epochs": 100,
        "max_oracle_move_bps": 500,
        "initial_margin_bps": 1000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_position_abs": 1000000,
        "fee_pool_quote": 0,
        "funding_rate_bps": 0,
        "funding_cap_bps": 100,
        "insurance_balance": 0,
        "initial_insurance": 0,
        "fee_income": 0,
        "claims_paid": 0,
        "min_notional_for_bounty": 100000000,
    }
    perps = PerpsState(
        version=PERPS_STATE_VERSION,
        markets={
            "perp:demo": PerpMarketState(
                quote_asset="0x" + "33" * 32,
                global_state=perps_global,
                accounts={
                    "alice": PerpAccountState(
                        position_base=0,
                        entry_price_e8=0,
                        collateral_quote=0,
                        funding_paid_cumulative=0,
                        funding_last_applied_epoch=0,
                        liquidated_this_step=False,
                    ),
                },
            ),
            "perp:ch2p:demo": PerpClearinghouse2pMarketState(
                quote_asset="0x" + "44" * 32,
                account_a_pubkey="alice",
                account_b_pubkey="bob",
                state={
                    **{k: 0 for k in PERP_CLEARINGHOUSE_2P_STATE_KEYS},
                    "breaker_active": False,
                    "clearing_price_seen": False,
                    "oracle_seen": False,
                    "liquidated_this_step": False,
                    "initial_margin_bps": 1000,
                    "maintenance_margin_bps": 600,
                    "liquidation_penalty_bps": 50,
                    "max_oracle_move_bps": 500,
                    "max_oracle_staleness_epochs": 100,
                    "max_position_abs": 1000000,
                },
            ),
        },
    )

    state = DexState(balances=balances, pools=pools, lp_balances=lp, perps=perps)
    snap1 = snapshot_from_state(state)
    state2 = state_from_snapshot(snap1.data)
    snap2 = snapshot_from_state(state2)

    assert snap1.canonical_bytes() == snap2.canonical_bytes()


def test_state_from_snapshot_rejects_invalid_clearinghouse_conservation() -> None:
    snap = {
        "version": 2,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "nonces": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
        "perps": {
            "version": PERPS_STATE_VERSION,
            "markets": [
                {
                    "market_id": "perp:ch2p:bad",
                    "kind": "clearinghouse_2p_v1",
                    "quote_asset": "0x" + "44" * 32,
                    "account_a_pubkey": "alice",
                    "account_b_pubkey": "bob",
                    "state": {
                        **{k: 0 for k in PERP_CLEARINGHOUSE_2P_STATE_KEYS},
                        "breaker_active": False,
                        "clearing_price_seen": False,
                        "oracle_seen": False,
                        "liquidated_this_step": False,
                        "initial_margin_bps": 1000,
                        "maintenance_margin_bps": 600,
                        "liquidation_penalty_bps": 50,
                        "max_oracle_move_bps": 500,
                        "max_oracle_staleness_epochs": 100,
                        "max_position_abs": 1000000,
                        # Violates net_deposited_e8 == collateral_a + collateral_b + fee_pool.
                        "net_deposited_e8": 1,
                    },
                }
            ],
        },
    }
    with pytest.raises(ValueError):
        state_from_snapshot(snap)


def test_state_from_snapshot_rejects_too_many_balance_entries_when_limited() -> None:
    snap = {
        "version": 1,
        "balances": [
            {"pubkey": "alice", "asset": "asset0", "amount": 0},
            {"pubkey": "alice", "asset": "asset1", "amount": 0},
            {"pubkey": "alice", "asset": "asset2", "amount": 0},
        ],
        "pools": [],
        "lp_balances": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
    }
    with pytest.raises(ValueError):
        state_from_snapshot(snap, max_balances=2)


def test_state_from_snapshot_rejects_snapshot_too_large_when_limited() -> None:
    snap = {
        "version": 1,
        "balances": [
            {"pubkey": "alice", "asset": "A" * 2000, "amount": 0},
        ],
        "pools": [],
        "lp_balances": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
    }
    with pytest.raises(ValueError):
        state_from_snapshot(snap, max_snapshot_bytes=256)


def test_state_from_snapshot_rejects_fee_bps_above_10000() -> None:
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    snap = {
        "version": 1,
        "balances": [],
        "pools": [
            {
                "pool_id": "0x" + "aa" * 32,
                "asset0": asset0,
                "asset1": asset1,
                "fee_bps": 10_001,
            }
        ],
        "lp_balances": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
    }
    with pytest.raises(ValueError):
        state_from_snapshot(snap)
