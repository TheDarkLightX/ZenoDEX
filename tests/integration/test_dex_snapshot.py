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
from src.state.pools import PoolState, PoolStatus, compute_pool_id

_PK = "0x" + "aa" * 48
_PK_CASE = "0x" + "AA" * 48
_ASSET0 = "0x" + "11" * 32
_ASSET1 = "0x" + "22" * 32
_POOL_ID = "0x" + "bb" * 32
_POOL_ID_CASE = "0x" + "BB" * 32


def _snapshot_base(**overrides: object) -> dict:
    snap = {
        "version": 1,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "nonces": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
    }
    snap.update(overrides)
    return snap


def test_snapshot_roundtrip_is_deterministic() -> None:
    balances = BalanceTable()
    lp = LPTable()
    pools = {}

    pk = "alice"
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    pool_id = compute_pool_id(asset0, asset1, 30)

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


def test_state_from_snapshot_rejects_decoded_duplicate_balances() -> None:
    snap = _snapshot_base(
        balances=[
            {"pubkey": _PK, "asset": _ASSET0, "amount": 1},
            {"pubkey": _PK_CASE, "asset": _ASSET0, "amount": 2},
        ],
    )

    with pytest.raises(ValueError, match="duplicate decoded balance entry"):
        state_from_snapshot(snap)


def test_state_from_snapshot_rejects_decoded_duplicate_pool_ids() -> None:
    pool_id = compute_pool_id(_ASSET0, _ASSET1, 30)
    snap = _snapshot_base(
        pools=[
            {
                "pool_id": pool_id,
                "asset0": _ASSET0,
                "asset1": _ASSET1,
                "fee_bps": 30,
            },
            {
                "pool_id": pool_id,
                "asset0": _ASSET0,
                "asset1": _ASSET1,
                "fee_bps": 30,
            },
        ],
    )

    with pytest.raises(ValueError, match="duplicate decoded pool entry"):
        state_from_snapshot(snap)


def test_state_from_snapshot_rejects_canonical_hex_pool_id_parameter_mismatch() -> None:
    canonical_pool_id = compute_pool_id(_ASSET0, _ASSET1, 30)
    mismatched_pool_id = "0x" + "ff" * 32
    assert mismatched_pool_id != canonical_pool_id
    snap = _snapshot_base(
        pools=[
            {
                "pool_id": mismatched_pool_id,
                "asset0": _ASSET0,
                "asset1": _ASSET1,
                "fee_bps": 30,
            }
        ],
    )

    with pytest.raises(ValueError, match="pool_id does not match canonical pool identity"):
        state_from_snapshot(snap)


@pytest.mark.parametrize(
    "identity_overrides",
    (
        {"asset1": "0x" + "33" * 32},
        {"fee_bps": 31},
        {
            "curve_tag": "SUM_BOOST_V1",
            "curve_params": '{"mu_num":1,"mu_den":2}',
        },
    ),
)
def test_state_from_snapshot_rejects_pool_parameter_mutation_without_new_id(
    identity_overrides: dict[str, object],
) -> None:
    canonical_pool_id = compute_pool_id(_ASSET0, _ASSET1, 30)
    pool_entry: dict[str, object] = {
        "pool_id": canonical_pool_id,
        "asset0": _ASSET0,
        "asset1": _ASSET1,
        "fee_bps": 30,
    }
    pool_entry.update(identity_overrides)

    with pytest.raises(ValueError, match="pool_id does not match canonical pool identity"):
        state_from_snapshot(_snapshot_base(pools=[pool_entry]))


@pytest.mark.parametrize(
    "pool_id_variant",
    (
        lambda pool_id: "0X" + pool_id[2:],
        lambda pool_id: "0x" + pool_id[2:].upper(),
        lambda pool_id: pool_id[2:],
    ),
)
def test_state_from_snapshot_rejects_noncanonical_hex_pool_id_variants(
    pool_id_variant: object,
) -> None:
    canonical_pool_id = compute_pool_id(_ASSET0, _ASSET1, 30)
    assert callable(pool_id_variant)
    variant = pool_id_variant(canonical_pool_id)
    snap = _snapshot_base(
        pools=[
            {
                "pool_id": variant,
                "asset0": _ASSET0,
                "asset1": _ASSET1,
                "fee_bps": 30,
            }
        ],
    )

    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed 32-byte hex"):
        state_from_snapshot(snap, allow_symbolic_pool_ids=True)


def test_state_from_snapshot_symbolic_pool_ids_require_explicit_local_compatibility() -> None:
    symbolic_pool_id = "local-pool-a"
    snap = _snapshot_base(
        pools=[
            {
                "pool_id": symbolic_pool_id,
                "asset0": _ASSET0,
                "asset1": _ASSET1,
                "fee_bps": 30,
            }
        ],
    )

    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed 32-byte hex"):
        state_from_snapshot(snap)

    restored = state_from_snapshot(snap, allow_symbolic_pool_ids=True)
    assert restored.pools[symbolic_pool_id].pool_id == symbolic_pool_id


def test_state_from_snapshot_symbolic_compatibility_rejects_malformed_hex() -> None:
    snap = _snapshot_base(
        pools=[
            {
                "pool_id": "0xlocal-pool-a",
                "asset0": _ASSET0,
                "asset1": _ASSET1,
                "fee_bps": 30,
            }
        ],
    )

    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed 32-byte hex"):
        state_from_snapshot(snap, allow_symbolic_pool_ids=True)


def test_state_from_snapshot_rejects_duplicate_logical_symbolic_pools() -> None:
    snap = _snapshot_base(
        pools=[
            {
                "pool_id": "local-pool-a",
                "asset0": _ASSET0,
                "asset1": _ASSET1,
                "fee_bps": 30,
            },
            {
                "pool_id": "local-pool-b",
                "asset0": _ASSET0,
                "asset1": _ASSET1,
                "fee_bps": 30,
            },
        ],
    )

    with pytest.raises(ValueError, match="duplicate logical pool entry"):
        state_from_snapshot(snap, allow_symbolic_pool_ids=True)


def test_state_from_snapshot_rejects_non_bool_symbolic_compatibility_flag() -> None:
    with pytest.raises(TypeError, match="allow_symbolic_pool_ids must be a bool"):
        state_from_snapshot(
            _snapshot_base(),
            allow_symbolic_pool_ids=1,  # type: ignore[arg-type]
        )


def test_state_from_snapshot_rejects_decoded_duplicate_lp_balances() -> None:
    snap = _snapshot_base(
        lp_balances=[
            {"pubkey": _PK, "pool_id": _POOL_ID, "amount": 1},
            {"pubkey": _PK_CASE, "pool_id": _POOL_ID, "amount": 2},
        ],
    )

    with pytest.raises(ValueError, match="duplicate decoded lp entry"):
        state_from_snapshot(snap)


def test_state_from_snapshot_rejects_decoded_duplicate_lp_mint_timestamps() -> None:
    snap = _snapshot_base(
        version=3,
        perps=None,
        lp_balances=[
            {"pubkey": _PK, "pool_id": _POOL_ID, "amount": 1},
        ],
        lp_mint_timestamps=[
            {"pubkey": _PK, "pool_id": _POOL_ID, "last_mint_timestamp": 1},
            {"pubkey": _PK_CASE, "pool_id": _POOL_ID, "last_mint_timestamp": 2},
        ],
    )

    with pytest.raises(ValueError, match="duplicate decoded lp_mint_timestamps entry"):
        state_from_snapshot(snap)


def test_state_from_snapshot_rejects_decoded_duplicate_lp_duration_risk() -> None:
    snap = _snapshot_base(
        version=4,
        perps=None,
        lp_mint_timestamps=[],
        lp_duration_risk=[
            {"pubkey": _PK, "pool_id": _POOL_ID, "churn_tier": 1},
            {"pubkey": _PK_CASE, "pool_id": _POOL_ID, "churn_tier": 2},
        ],
    )

    with pytest.raises(ValueError, match="duplicate decoded lp_duration_risk entry"):
        state_from_snapshot(snap)


def test_state_from_snapshot_rejects_decoded_duplicate_nonces() -> None:
    snap = _snapshot_base(
        nonces=[
            {"pubkey": _PK, "last_nonce": 1},
            {"pubkey": _PK_CASE, "last_nonce": 2},
        ],
    )

    with pytest.raises(ValueError, match="duplicate decoded nonce entry"):
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
    curve_params = '{"mu_den":2,"mu_num":1}'
    pool_id = compute_pool_id(
        asset0,
        asset1,
        30,
        curve_tag="SUM_BOOST_V1",
        curve_params=curve_params,
    )
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
    assert restored_pool.curve_params == curve_params
