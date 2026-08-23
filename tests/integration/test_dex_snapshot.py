# [TESTER] v1

from __future__ import annotations

import pytest

from src.core.dex import DexState
from src.core.perps import (
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PERPS_STATE_VERSION,
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpMarketState,
    PerpsState,
)
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


def _lp_conserving_state() -> DexState:
    pool_id = "0x" + "aa" * 32
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    lp = LPTable()
    lp.set("alice", pool_id, 7)
    lp.set("0x" + "00" * 48, pool_id, 3)
    return DexState(
        balances=BalanceTable(),
        pools={
            pool_id: PoolState(
                pool_id=pool_id,
                asset0=asset0,
                asset1=asset1,
                reserve0=1_000,
                reserve1=2_000,
                fee_bps=30,
                lp_supply=10,
                status=PoolStatus.ACTIVE,
                created_at=1,
            )
        },
        lp_balances=lp,
    )


def test_strict_snapshot_roundtrip_enforces_lp_supply_conservation() -> None:
    state = _lp_conserving_state()

    snapshot = snapshot_from_state(
        state,
        require_lp_supply_conservation=True,
    )
    restored = state_from_snapshot(
        snapshot.data,
        require_lp_supply_conservation=True,
    )

    assert snapshot_from_state(
        restored,
        require_lp_supply_conservation=True,
    ).canonical_bytes() == snapshot.canonical_bytes()


def test_strict_snapshot_rejects_lp_supply_mismatch_in_both_directions() -> None:
    state = _lp_conserving_state()
    pool_id = next(iter(state.pools))
    state.lp_balances.set("alice", pool_id, 6)

    with pytest.raises(ValueError, match="LP supply conservation mismatch"):
        snapshot_from_state(state, require_lp_supply_conservation=True)

    snapshot = snapshot_from_state(state)
    with pytest.raises(ValueError, match="LP supply conservation mismatch"):
        state_from_snapshot(
            snapshot.data,
            require_lp_supply_conservation=True,
        )


def test_strict_snapshot_rejects_lp_balance_for_unknown_pool() -> None:
    state = _lp_conserving_state()
    state.lp_balances.set("mallory", "0x" + "bb" * 32, 1)

    with pytest.raises(ValueError, match="LP balance references unknown pool"):
        snapshot_from_state(state, require_lp_supply_conservation=True)

    snapshot = snapshot_from_state(state)
    with pytest.raises(ValueError, match="LP balance references unknown pool"):
        state_from_snapshot(
            snapshot.data,
            require_lp_supply_conservation=True,
        )


@pytest.mark.parametrize("hostile", [0, 1, None, "true"])
def test_strict_snapshot_rejects_non_bool_conservation_flag(hostile: object) -> None:
    state = _lp_conserving_state()

    with pytest.raises(TypeError, match="require_lp_supply_conservation must be a bool"):
        snapshot_from_state(
            state,
            require_lp_supply_conservation=hostile,  # type: ignore[arg-type]
        )
    with pytest.raises(TypeError, match="require_lp_supply_conservation must be a bool"):
        state_from_snapshot(
            snapshot_from_state(state).data,
            require_lp_supply_conservation=hostile,  # type: ignore[arg-type]
        )


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
        "epoch_phase": "Open",
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
        "fee_pool_quote": 30_000,
        "funding_rate_bps": 0,
        "funding_cap_bps": 100,
        "insurance_balance": 30_000,
        "initial_insurance": 0,
        "fee_income": 30_000,
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
                pending_funding_closeout_root_hashes=("sha256:" + "12" * 32,),
                pending_funding_closeout_source_availability_hashes=(
                    "sha256:" + "34" * 32,
                ),
                pending_funding_closeout_carried_liability_hashes=(
                    "sha256:" + "56" * 32,
                ),
                funding_closeout_policy_ledger_hashes=(
                    "sha256:" + "78" * 32,
                ),
                funding_closeout_sink_claimant_balances_quote=(
                    ("protocol_sink", 20_000),
                    ("insurance_sink", 10_000),
                ),
                funding_closeout_receiver_claim_balances_quote=(
                    ("bb" * 48, 18_000),
                    ("cc" * 48, 12_000),
                ),
                funding_closeout_receiver_claim_lots_quote=(
                    ("bb" * 48, "bb-old", 6_000, 5),
                    ("bb" * 48, "bb-new", 12_000, 10),
                    ("cc" * 48, "cc-only", 12_000, 10),
                ),
            ),
            "perp:ch2p:demo": PerpClearinghouse2pMarketState(
                quote_asset="0x" + "44" * 32,
                account_a_pubkey="aa" * 48,
                account_b_pubkey="bb" * 48,
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
            "perp:ch3p:demo": PerpClearinghouse3pTransferMarketState(
                quote_asset="0x" + "55" * 32,
                account_a_pubkey="aa" * 48,
                account_b_pubkey="bb" * 48,
                account_c_pubkey="cc" * 48,
                state={
                    **{k: 0 for k in PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS},
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
    assert state2.perps is not None
    restored_market = state2.perps.markets["perp:demo"]
    assert isinstance(restored_market, PerpMarketState)
    assert restored_market.pending_funding_closeout_root_hashes == ("sha256:" + "12" * 32,)
    assert restored_market.pending_funding_closeout_source_availability_hashes == (
        "sha256:" + "34" * 32,
    )
    assert restored_market.pending_funding_closeout_carried_liability_hashes == (
        "sha256:" + "56" * 32,
    )
    assert restored_market.funding_closeout_policy_ledger_hashes == (
        "sha256:" + "78" * 32,
    )
    assert restored_market.funding_closeout_sink_claimant_balances_quote == (
        ("insurance_sink", 10_000),
        ("protocol_sink", 20_000),
    )
    assert restored_market.funding_closeout_receiver_claim_balances_quote == (
        ("bb" * 48, 18_000),
        ("cc" * 48, 12_000),
    )
    assert restored_market.funding_closeout_receiver_claim_lots_quote == (
        ("bb" * 48, "bb-old", 6_000, 5),
        ("bb" * 48, "bb-new", 12_000, 10),
        ("cc" * 48, "cc-only", 12_000, 10),
    )
    perps_snapshot = snap2.data["perps"]
    isolated_snapshot = next(
        entry
        for entry in perps_snapshot["markets"]
        if entry["market_id"] == "perp:demo"
    )
    assert isolated_snapshot["funding_closeout_sink_claimant_balances_quote"] == [
        {"claimant": "insurance_sink", "balance_quote": 10_000},
        {"claimant": "protocol_sink", "balance_quote": 20_000},
    ]
    assert isolated_snapshot["funding_closeout_receiver_claim_balances_quote"] == [
        {"account_pubkey": "bb" * 48, "balance_quote": 18_000},
        {"account_pubkey": "cc" * 48, "balance_quote": 12_000},
    ]
    assert isolated_snapshot["funding_closeout_receiver_claim_lots_quote"] == [
        {
            "account_pubkey": "bb" * 48,
            "lot_id": "bb-old",
            "balance_quote": 6_000,
            "expires_at_epoch": 5,
        },
        {
            "account_pubkey": "bb" * 48,
            "lot_id": "bb-new",
            "balance_quote": 12_000,
            "expires_at_epoch": 10,
        },
        {
            "account_pubkey": "cc" * 48,
            "lot_id": "cc-only",
            "balance_quote": 12_000,
            "expires_at_epoch": 10,
        },
    ]


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


def test_state_from_snapshot_rejects_invalid_clearinghouse_3p_conservation() -> None:
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
                    "market_id": "perp:ch3p:bad",
                    "kind": "clearinghouse_3p_transfer_v1",
                    "quote_asset": "0x" + "55" * 32,
                    "account_a_pubkey": "alice",
                    "account_b_pubkey": "bob",
                    "account_c_pubkey": "carol",
                    "state": {
                        **{k: 0 for k in PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS},
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
                        # Violates net_deposited_e8 == collateral_a + collateral_b + collateral_c + fee_pool.
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


def test_snapshot_roundtrip_preserves_curve_configuration() -> None:
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    pool_id = "0x" + "aa" * 32
    state = DexState(
        balances=BalanceTable(),
        pools={
            pool_id: PoolState(
                pool_id=pool_id,
                asset0=asset0,
                asset1=asset1,
                reserve0=1_000,
                reserve1=2_000,
                fee_bps=30,
                lp_supply=10,
                status=PoolStatus.ACTIVE,
                created_at=1,
                curve_tag="SUM_BOOST_V1",
                curve_params='{"mu_num":1,"mu_den":2}',
            )
        },
        lp_balances=LPTable(),
    )

    snap = snapshot_from_state(state)
    restored = state_from_snapshot(snap.data)
    restored_pool = restored.pools[pool_id]
    assert restored_pool.curve_tag == "SUM_BOOST_V1"
    assert restored_pool.curve_params == '{"mu_den":2,"mu_num":1}'
