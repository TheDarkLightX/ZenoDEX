from __future__ import annotations

import pytest

from src.core.batch_clearing import apply_settlement_pure
from src.core.dex import DexState
from src.core.perps import PERPS_STATE_VERSION_V5, PerpsState
from src.core.settlement import ReserveDelta, Settlement
from src.integration.dex_snapshot import snapshot_from_state
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus


def _pubkey(byte: str) -> str:
    return "0x" + byte * 96


def _pool(*, reserve0: int = 100, reserve1: int = 200, lp_supply: int = 50) -> PoolState:
    return PoolState(
        pool_id="pool",
        asset0="A",
        asset1="B",
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=30,
        lp_supply=lp_supply,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _state_and_aliases() -> tuple[
    DexState,
    BalanceTable,
    dict[str, PoolState],
    LPTable,
    NonceTable,
    dict[str, object],
]:
    pubkey = _pubkey("1")
    balances = BalanceTable()
    balances.set(pubkey, "A", 1_000)
    pools = {"pool": _pool()}
    lp_balances = LPTable()
    lp_balances.set(pubkey, "pool", 50)
    lp_balances.set_last_mint_timestamp(pubkey, "pool", 7)
    lp_balances.set_last_remove_timestamp(pubkey, "pool", 8)
    lp_balances.set_churn_tier(pubkey, "pool", 2)
    lp_balances.set_last_churn_update_timestamp(pubkey, "pool", 9)
    nonces = NonceTable()
    nonces.set_last(pubkey, 3)
    markets: dict[str, object] = {}
    state = DexState(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        nonces=nonces,
        perps=PerpsState(version=PERPS_STATE_VERSION_V5, markets=markets),
    )
    return state, balances, pools, lp_balances, nonces, markets


def test_dex_state_detaches_every_mutable_constructor_alias() -> None:
    pubkey = _pubkey("1")
    state, balances, pools, lp_balances, nonces, markets = _state_and_aliases()
    before = snapshot_from_state(state).commitment_hex()

    balances.set(pubkey, "A", 999_999)
    pools["pool"].reserve0 = 999_999
    pools["new"] = _pool(reserve0=1)
    lp_balances.set(pubkey, "pool", 999_999)
    lp_balances.set_last_mint_timestamp(pubkey, "pool", 999)
    lp_balances.set_last_remove_timestamp(pubkey, "pool", 999)
    lp_balances.set_churn_tier(pubkey, "pool", 999)
    lp_balances.set_last_churn_update_timestamp(pubkey, "pool", 999)
    nonces.set_last(pubkey, 4)
    markets["late-alias-write"] = object()

    assert snapshot_from_state(state).commitment_hex() == before
    assert state.balances.get(pubkey, "A") == 1_000
    assert state.pools["pool"].reserve0 == 100
    assert "new" not in state.pools
    assert state.lp_balances.get(pubkey, "pool") == 50
    assert state.lp_balances.get_last_mint_timestamp(pubkey, "pool") == 7
    assert state.lp_balances.get_last_remove_timestamp(pubkey, "pool") == 8
    assert state.lp_balances.get_churn_tier(pubkey, "pool") == 2
    assert state.lp_balances.get_last_churn_update_timestamp(pubkey, "pool") == 9
    assert state.nonces.get_last(pubkey) == 3
    assert state.perps is not None
    assert "late-alias-write" not in state.perps.markets


def test_dex_state_nested_public_mutators_fail_closed() -> None:
    pubkey = _pubkey("1")
    state, *_aliases = _state_and_aliases()

    with pytest.raises(TypeError, match="immutable"):
        state.balances.set(pubkey, "A", 2)
    with pytest.raises(TypeError, match="immutable"):
        state.balances._balances[(pubkey, "A")] = 2  # type: ignore[index]
    with pytest.raises(TypeError, match="immutable"):
        state.pools["other"] = _pool()  # type: ignore[index]
    with pytest.raises(TypeError, match="immutable"):
        state.pools["pool"].reserve0 = 2
    with pytest.raises(TypeError, match="immutable"):
        state.lp_balances.set(pubkey, "pool", 2)
    with pytest.raises(TypeError, match="immutable"):
        state.lp_balances.set_last_mint_timestamp(pubkey, "pool", 2)
    with pytest.raises(TypeError, match="immutable"):
        state.nonces.set_last(pubkey, 4)
    assert state.perps is not None
    with pytest.raises(TypeError, match="immutable"):
        state.perps.markets["other"] = object()  # type: ignore[index]


def test_pure_settlement_application_replaces_frozen_pool_values() -> None:
    state, *_aliases = _state_and_aliases()
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[
            ReserveDelta(
                pool_id="pool",
                asset="A",
                delta_add=5,
                delta_sub=0,
            )
        ],
        lp_deltas=[],
    )

    next_balances, next_pools, next_lp = apply_settlement_pure(
        settlement,
        state.balances,
        state.pools,
        state.lp_balances,
    )

    assert state.pools["pool"].reserve0 == 100
    assert next_pools["pool"].reserve0 == 105
    assert next_balances.get_all_balances() == state.balances.get_all_balances()
    assert next_lp.get_all_balances() == state.lp_balances.get_all_balances()
