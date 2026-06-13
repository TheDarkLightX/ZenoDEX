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
    snap = _snapshot_base(
        pools=[
            {
                "pool_id": _POOL_ID,
                "asset0": _ASSET0,
                "asset1": _ASSET1,
                "fee_bps": 30,
            },
            {
                "pool_id": _POOL_ID_CASE,
                "asset0": _ASSET0,
                "asset1": _ASSET1,
                "fee_bps": 30,
            },
        ],
    )

    with pytest.raises(ValueError, match="duplicate decoded pool entry"):
        state_from_snapshot(snap)


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


# ---------------------------------------------------------------------------
# Behavior-preserving refactor guards for ``state_from_snapshot``.
#
# These tests pin the exact reject message for each schema section plus a
# round-trip (snapshot -> state -> snapshot) and a known-snapshot -> exact-state
# decode for every section that the per-section parser extraction will touch.
# They are written to be green on the un-refactored function and MUST stay green
# after the extraction (any drift in defaults / reject precedence fails here).
# ---------------------------------------------------------------------------


# ---- Section reject teeth (exact messages) --------------------------------


def test_reject_teeth_balances_section() -> None:
    with pytest.raises(TypeError, match="snapshot.balances must be a list"):
        state_from_snapshot(_snapshot_base(balances={}))
    with pytest.raises(TypeError, match="snapshot.balances entries must be objects"):
        state_from_snapshot(_snapshot_base(balances=["nope"]))
    with pytest.raises(ValueError, match=r"invalid balance entry \(amount\)"):
        state_from_snapshot(_snapshot_base(balances=[{"pubkey": "a", "asset": "x", "amount": -1}]))
    with pytest.raises(ValueError, match=r"invalid balance entry \(amount\)"):
        # bool must not pass the int check.
        state_from_snapshot(_snapshot_base(balances=[{"pubkey": "a", "asset": "x", "amount": True}]))
    with pytest.raises(ValueError, match="too many balances entries"):
        state_from_snapshot(
            _snapshot_base(
                balances=[
                    {"pubkey": "a", "asset": "x", "amount": 0},
                    {"pubkey": "b", "asset": "y", "amount": 0},
                ]
            ),
            max_balances=1,
        )


def test_reject_teeth_pools_section() -> None:
    with pytest.raises(TypeError, match="snapshot.pools must be a list"):
        state_from_snapshot(_snapshot_base(pools={}))
    with pytest.raises(TypeError, match="snapshot.pools entries must be objects"):
        state_from_snapshot(_snapshot_base(pools=["nope"]))
    with pytest.raises(ValueError, match="invalid pool status"):
        state_from_snapshot(
            _snapshot_base(
                pools=[{"pool_id": "p", "asset0": "a0", "asset1": "a1", "status": "BOGUS"}]
            )
        )
    with pytest.raises(ValueError, match="fee_bps out of range"):
        state_from_snapshot(
            _snapshot_base(pools=[{"pool_id": "p", "asset0": "a0", "asset1": "a1", "fee_bps": 10_001}])
        )


def test_reject_teeth_lp_section() -> None:
    with pytest.raises(TypeError, match="snapshot.lp_balances must be a list"):
        state_from_snapshot(_snapshot_base(lp_balances={}))
    with pytest.raises(ValueError, match=r"invalid lp entry \(amount\)"):
        state_from_snapshot(_snapshot_base(lp_balances=[{"pubkey": "a", "pool_id": "p", "amount": -1}]))


def test_reject_teeth_lp_mint_timestamps_section() -> None:
    # Required for v3+ when absent.
    snap_missing = _snapshot_base(version=3, perps=None)
    snap_missing.pop("lp_mint_timestamps", None)
    with pytest.raises(ValueError, match="lp_mint_timestamps is required for snapshot v3"):
        state_from_snapshot(snap_missing)
    with pytest.raises(TypeError, match="snapshot.lp_mint_timestamps must be a list"):
        state_from_snapshot(_snapshot_base(version=3, perps=None, lp_mint_timestamps={}))
    with pytest.raises(ValueError, match="invalid lp_mint_timestamps entry"):
        state_from_snapshot(
            _snapshot_base(
                version=3,
                perps=None,
                lp_mint_timestamps=[{"pubkey": "a", "pool_id": "p", "last_mint_timestamp": -1}],
            )
        )


def test_reject_teeth_lp_duration_risk_section() -> None:
    snap_missing = _snapshot_base(version=4, perps=None, lp_mint_timestamps=[])
    snap_missing.pop("lp_duration_risk", None)
    with pytest.raises(ValueError, match="lp_duration_risk is required for snapshot v4"):
        state_from_snapshot(snap_missing)
    with pytest.raises(TypeError, match="snapshot.lp_duration_risk must be a list"):
        state_from_snapshot(
            _snapshot_base(version=4, perps=None, lp_mint_timestamps=[], lp_duration_risk={})
        )


def test_reject_teeth_nonces_section() -> None:
    with pytest.raises(TypeError, match="snapshot.nonces must be a list"):
        state_from_snapshot(_snapshot_base(nonces={}))
    with pytest.raises(ValueError, match=r"invalid nonce entry \(last_nonce\)"):
        state_from_snapshot(_snapshot_base(nonces=[{"pubkey": "a", "last_nonce": -1}]))
    with pytest.raises(ValueError, match="last_nonce out of u32 range"):
        state_from_snapshot(_snapshot_base(nonces=[{"pubkey": "a", "last_nonce": 0x1_0000_0000}]))


def test_reject_teeth_fee_accumulator_section() -> None:
    # Absent key (sentinel) -> required reject, distinct from present-but-empty.
    snap_missing = _snapshot_base()
    snap_missing.pop("fee_accumulator", None)
    with pytest.raises(ValueError, match="snapshot.fee_accumulator is required"):
        state_from_snapshot(snap_missing)
    with pytest.raises(TypeError, match="snapshot.fee_accumulator must be an object"):
        state_from_snapshot(_snapshot_base(fee_accumulator=[]))
    with pytest.raises(TypeError, match="fee_accumulator.dust must be an int"):
        state_from_snapshot(_snapshot_base(fee_accumulator={"dust": "x"}))


def test_reject_teeth_vault_section() -> None:
    with pytest.raises(TypeError, match="snapshot.vault must be an object or null"):
        state_from_snapshot(_snapshot_base(vault=[]))
    with pytest.raises(TypeError, match="vault.reward_balance must be an int"):
        state_from_snapshot(_snapshot_base(vault={"reward_balance": "x"}))


def test_reject_teeth_oracle_section() -> None:
    with pytest.raises(TypeError, match="snapshot.oracle must be an object or null"):
        state_from_snapshot(_snapshot_base(oracle=[]))
    with pytest.raises(TypeError, match="oracle.price_timestamp must be an int"):
        state_from_snapshot(_snapshot_base(oracle={"price_timestamp": "x"}))


def test_reject_teeth_perps_section() -> None:
    with pytest.raises(TypeError, match="snapshot.perps must be an object or null"):
        state_from_snapshot(_snapshot_base(version=2, perps=[]))
    with pytest.raises(ValueError, match="snapshot.perps.version must be a positive int"):
        state_from_snapshot(_snapshot_base(version=2, perps={"version": 0, "markets": []}))
    with pytest.raises(TypeError, match="snapshot.perps.markets must be a list"):
        state_from_snapshot(
            _snapshot_base(version=2, perps={"version": PERPS_STATE_VERSION, "markets": {}})
        )
    with pytest.raises(ValueError, match="unsupported perps market kind"):
        state_from_snapshot(
            _snapshot_base(
                version=2,
                perps={
                    "version": PERPS_STATE_VERSION,
                    "markets": [{"market_id": "m", "kind": "bogus_kind"}],
                },
            )
        )


# ---- Section round-trip goldens (snapshot -> state -> snapshot) ------------


def _full_state_all_sections() -> DexState:
    """A DexState exercising every non-perps snapshot section together.

    ``NonceTable`` enforces 48-byte hex pubkeys, so the user identity here is a
    canonical hex pubkey (``_PK``) rather than a symbolic name.
    """
    balances = BalanceTable()
    balances.set(_PK, _ASSET0, 111)
    balances.set(_PK, _ASSET1, 222)

    pools = {
        _POOL_ID: PoolState(
            pool_id=_POOL_ID,
            asset0=min(_ASSET0, _ASSET1),
            asset1=max(_ASSET0, _ASSET1),
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=30,
            lp_supply=10,
            status=PoolStatus.ACTIVE,
            created_at=7,
        )
    }

    lp = LPTable()
    lp.set(_PK, _POOL_ID, 5)
    lp.set_last_mint_timestamp(_PK, _POOL_ID, 42)
    lp.set_last_remove_timestamp(_PK, _POOL_ID, 9)
    lp.set_churn_tier(_PK, _POOL_ID, 3)
    lp.set_last_churn_update_timestamp(_PK, _POOL_ID, 11)

    from src.core.fees import FeeAccumulatorState
    from src.core.oracle import OracleState
    from src.core.vault import VaultState
    from src.state.nonces import NonceTable

    nonces = NonceTable()
    nonces.set_last(_PK, 17)

    return DexState(
        balances=balances,
        pools=pools,
        lp_balances=lp,
        nonces=nonces,
        fee_accumulator=FeeAccumulatorState(dust=13),
        vault=VaultState(
            acc_reward_per_share=9,
            last_update_acc=2,
            pending_rewards=3,
            reward_balance=4,
            staked_lp_shares=5,
        ),
        oracle=OracleState(price_timestamp=1000, max_staleness_seconds=250),
    )


def test_roundtrip_all_sections_v4_is_stable() -> None:
    state = _full_state_all_sections()
    snap1 = snapshot_from_state(state)  # default version 4
    assert snap1.version == 4
    state2 = state_from_snapshot(snap1.data)
    snap2 = snapshot_from_state(state2)
    assert snap1.canonical_bytes() == snap2.canonical_bytes()
    assert snap1.commitment_bytes() == snap2.commitment_bytes()


def test_roundtrip_decodes_each_section_to_exact_state() -> None:
    state = _full_state_all_sections()
    snap = snapshot_from_state(state)
    restored = state_from_snapshot(snap.data)

    # balances
    assert restored.balances.get_all_balances() == state.balances.get_all_balances()
    # pools
    assert set(restored.pools) == set(state.pools)
    rp = restored.pools[_POOL_ID]
    sp = state.pools[_POOL_ID]
    assert (rp.reserve0, rp.reserve1, rp.fee_bps, rp.lp_supply, rp.created_at) == (
        sp.reserve0,
        sp.reserve1,
        sp.fee_bps,
        sp.lp_supply,
        sp.created_at,
    )
    assert rp.status is PoolStatus.ACTIVE
    # lp balances + all three lp metadata rails
    assert restored.lp_balances.get_all_balances() == state.lp_balances.get_all_balances()
    assert restored.lp_balances.get_last_mint_timestamp(_PK, _POOL_ID) == 42
    meta = restored.lp_balances.get_all_duration_risk_metadata()[(_PK, _POOL_ID)]
    assert meta.last_remove_timestamp == 9
    assert meta.churn_tier == 3
    assert meta.last_churn_update_timestamp == 11
    # nonces
    assert restored.nonces.get_all() == {_PK: 17}
    # fee accumulator
    assert restored.fee_accumulator.dust == 13
    # vault
    assert restored.vault is not None
    assert restored.vault.reward_balance == 4
    assert restored.vault.staked_lp_shares == 5
    # oracle
    assert restored.oracle is not None
    assert restored.oracle.price_timestamp == 1000
    assert restored.oracle.max_staleness_seconds == 250


def test_oracle_default_max_staleness_is_300() -> None:
    # The oracle max_staleness_seconds default is 300 (not 0): pin it.
    snap = _snapshot_base(oracle={"price_timestamp": 5})
    restored = state_from_snapshot(snap)
    assert restored.oracle is not None
    assert restored.oracle.price_timestamp == 5
    assert restored.oracle.max_staleness_seconds == 300


def test_pool_curve_defaults_when_absent() -> None:
    # curve_tag default "CPMM", curve_params default "" (empty allowed).
    snap = _snapshot_base(
        pools=[{"pool_id": _POOL_ID, "asset0": _ASSET0, "asset1": _ASSET1, "fee_bps": 30}]
    )
    restored = state_from_snapshot(snap)
    pool = restored.pools[_POOL_ID]
    assert pool.curve_tag == "CPMM"
    assert pool.curve_params == ""


def test_perps_chnp_pending_intent_defaults_and_required_nonce() -> None:
    from src.core.perps import PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1

    _E8 = 100_000_000
    _np_global = {
        "now_epoch": 0,
        "index_price_e8": 100 * _E8,
        "fee_pool_e8": 0,
        "insurance_e8": 0,
        "insurance_ext_e8": 0,
        "claims_paid_e8": 0,
        "net_deposited_e8": 0,
        "initial_margin_bps": 1000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_oracle_move_bps": 500,
        "funding_cap_bps": 100,
        "max_position_abs": 1_000_000,
        "min_notional_for_bounty_e8": 100 * _E8,
    }

    def _chnp_snapshot(intent: dict) -> dict:
        return _snapshot_base(
            version=2,
            perps={
                "version": PERPS_STATE_VERSION,
                "markets": [
                    {
                        "market_id": "perp:chnp:demo",
                        "kind": PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
                        "quote_asset": "0x" + "33" * 32,
                        "global_state": dict(_np_global),
                        "accounts": [
                            {
                                "pubkey": _PK,
                                "position_base": 0,
                                "entry_price_e8": 0,
                                "collateral_e8": 0,
                                "funding_paid_cum_e8": 0,
                                "nonce": 0,
                            }
                        ],
                        "pending_intents": [intent],
                    }
                ],
            },
        )

    # nonce has no default -> absent raises (required-ness preserved). The
    # ``_require_int(intent.get("nonce"))`` fires during argument evaluation,
    # before the dataclass validator, so the snapshot-layer message is observed.
    with pytest.raises(TypeError, match="perps.chnp.pending_intent.nonce must be an int"):
        state_from_snapshot(_chnp_snapshot({"pubkey": _PK, "target_base": 1}))

    # expiry_epoch default is 1 << 62 when absent (nonce must be a positive int
    # per the dataclass validator; pubkey must be canonical 48-byte hex).
    restored = state_from_snapshot(_chnp_snapshot({"pubkey": _PK, "nonce": 1}))
    market = restored.perps.markets["perp:chnp:demo"]
    assert market.pending_intents[0].expiry_epoch == (1 << 62)


def test_perps_roundtrip_all_kinds_stable() -> None:
    # Re-use the existing multi-kind perps fixture builder via a v5 snapshot and
    # confirm round-trip stability across isolated + ch2p + ch3p kinds.
    test_snapshot_roundtrip_with_perps_is_deterministic()
