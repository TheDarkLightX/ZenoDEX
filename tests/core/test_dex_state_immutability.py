from __future__ import annotations

from dataclasses import asdict, fields
from types import MappingProxyType
from typing import Any, cast

import pytest

from src.core.batch_clearing import apply_settlement_pure
from src.core.dex import DexState
from src.core.oracle import OracleState
from src.core.perps import (
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpMarketState,
    PerpsState,
    Value,
)
from src.core.settlement import ReserveDelta, Settlement
from src.core.vault import VaultState
from src.integration.dex_snapshot import snapshot_from_state
from src.state.balances import BalanceTable
from src.state.immutable_collections import FrozenDict, FrozenList, deep_freeze
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus


def _pubkey(byte: str) -> str:
    return "0x" + byte * 96


def _pool(
    *,
    reserve0: int = 100,
    reserve1: int = 200,
    lp_supply: int = 50,
) -> PoolState:
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

    assert not hasattr(state, "__dict__")
    assert not hasattr(state.balances, "__dict__")
    assert not hasattr(state.pools["pool"], "__dict__")
    assert not hasattr(state.lp_balances, "__dict__")
    assert not hasattr(state.nonces, "__dict__")
    assert state.perps is not None
    assert not hasattr(state.perps, "__dict__")
    assert not hasattr(state.fee_accumulator, "__dict__")

    with pytest.raises(TypeError, match="immutable"):
        state.balances.set(pubkey, "A", 2)
    with pytest.raises(TypeError, match="immutable"):
        state.balances._balances[(pubkey, "A")] = 2
    with pytest.raises(TypeError, match="immutable"):
        state.pools["other"] = _pool()
    with pytest.raises(TypeError, match="immutable"):
        state.pools["pool"].reserve0 = 2
    with pytest.raises(TypeError, match="immutable"):
        state.lp_balances.set(pubkey, "pool", 2)
    with pytest.raises(TypeError, match="immutable"):
        state.lp_balances.set_last_mint_timestamp(pubkey, "pool", 2)
    with pytest.raises(TypeError, match="immutable"):
        state.nonces.set_last(pubkey, 4)
    with pytest.raises(TypeError, match="immutable"):
        state.perps.markets["other"] = object()


def test_snapshot_seal_flags_do_not_enter_dataclass_schemas() -> None:
    nonce_builder = NonceTable()
    pool_builder = _pool()
    state, *_aliases = _state_and_aliases()

    assert "_snapshot_sealed" not in asdict(nonce_builder)
    assert "_snapshot_sealed" not in asdict(pool_builder)
    assert "_snapshot_sealed" not in {item.name for item in fields(state.nonces)}
    assert "_snapshot_sealed" not in {
        item.name for item in fields(state.pools["pool"])
    }


def test_dex_state_rejects_builtin_base_class_mutator_bypass() -> None:
    pubkey = _pubkey("1")
    state, *_aliases = _state_and_aliases()
    before = snapshot_from_state(state).commitment_hex()

    with pytest.raises(TypeError):
        dict.__setitem__(state.balances._balances, (pubkey, "A"), 2)
    with pytest.raises(TypeError):
        dict.__setitem__(state.pools, "other", _pool())
    with pytest.raises(TypeError):
        dict.__setitem__(state.lp_balances._balances, (pubkey, "pool"), 2)
    with pytest.raises(TypeError):
        dict.__setitem__(state.nonces._last, pubkey, 4)
    assert state.perps is not None
    with pytest.raises(TypeError):
        dict.__setitem__(state.perps.markets, "other", object())

    with pytest.raises(TypeError):
        BalanceTable.__setattr__(state.balances, "_balances", {})
    with pytest.raises(TypeError):
        LPTable.__setattr__(state.lp_balances, "_balances", {})
    with pytest.raises(TypeError):
        NonceTable.__setattr__(state.nonces, "_last", {})
    with pytest.raises(TypeError):
        PoolState.__setattr__(state.pools["pool"], "reserve0", 2)

    assert snapshot_from_state(state).commitment_hex() == before


def test_deep_freeze_owns_nested_lists_and_mappings() -> None:
    source = [{"amounts": [1, 2]}]
    frozen = deep_freeze(source)
    assert isinstance(frozen, FrozenList)

    source[0]["amounts"].append(3)
    assert frozen == [{"amounts": [1, 2]}]

    with pytest.raises(TypeError):
        list.append(cast(list[Any], frozen), {"amounts": [4]})
    with pytest.raises(TypeError):
        dict.__setitem__(frozen[0], "amounts", [9])
    with pytest.raises(TypeError, match="immutable"):
        frozen[0]["amounts"].append(9)


def test_frozen_collection_constructors_recursively_own_nested_values() -> None:
    mapping_source = {"payload": [{"amount": 1}]}
    list_source = [{"amounts": [2]}]
    frozen_mapping = FrozenDict(mapping_source)
    frozen_list = FrozenList(list_source)

    mapping_source["payload"][0]["amount"] = 99
    list_source[0]["amounts"].append(3)

    assert frozen_mapping["payload"][0]["amount"] == 1
    assert tuple(frozen_list[0]["amounts"]) == (2,)
    with pytest.raises(TypeError, match="immutable"):
        frozen_mapping["payload"][0]["amount"] = 7
    with pytest.raises(TypeError, match="immutable"):
        frozen_list[0]["amounts"].append(4)


def test_deep_freeze_owns_generic_mapping_backing_storage() -> None:
    backing = {"amounts": [1]}
    frozen = deep_freeze(MappingProxyType(backing))

    backing["amounts"].append(2)

    assert tuple(frozen["amounts"]) == (1,)
    with pytest.raises(TypeError, match="immutable"):
        frozen["amounts"].append(3)


class _AdversarialFrozenDict(FrozenDict):
    def __getitem__(self, key: Any) -> Any:
        del key
        return "attacker-controlled"


class _AdversarialFrozenList(FrozenList):
    def __getitem__(self, index: int | slice) -> Any:
        del index
        return "attacker-controlled"


def test_deep_freeze_rejects_behavior_changing_frozen_collection_subclasses() -> None:
    with pytest.raises(TypeError, match="subclasses"):
        deep_freeze(_AdversarialFrozenDict({"amount": 7}))
    with pytest.raises(TypeError, match="subclasses"):
        deep_freeze(_AdversarialFrozenList([7]))


class _AdversarialPerpMarket(PerpMarketState):
    def kernel_state_for_account(self, account: PerpAccountState) -> dict[str, Value]:
        del account
        return {"collateral_quote": 10**30}


def test_dex_state_rejects_behavior_changing_perps_market_subclasses() -> None:
    subclass_value = object.__new__(_AdversarialPerpMarket)
    perps = PerpsState(
        version=PERPS_STATE_VERSION_V5,
        markets={"adversarial": subclass_value},
    )

    with pytest.raises(TypeError, match="exact supported state type"):
        DexState(
            balances=BalanceTable(),
            pools={},
            lp_balances=LPTable(),
            nonces=NonceTable(),
            perps=perps,
        )


class _AdversarialBalanceTable(BalanceTable):
    def get_all_balances(self) -> dict[tuple[str, str], int]:
        return {("attacker", "A"): 10**30}


def test_dex_state_rejects_behavior_changing_table_subclasses() -> None:
    with pytest.raises(TypeError, match="exact BalanceTable"):
        DexState(
            balances=_AdversarialBalanceTable(),
            pools={},
            lp_balances=LPTable(),
        )


def test_optional_module_aliases_are_detached() -> None:
    vault = VaultState(
        acc_reward_per_share=3,
        last_update_acc=2,
        pending_rewards=1,
        reward_balance=2,
        staked_lp_shares=4,
    )
    oracle = OracleState(price_timestamp=5, max_staleness_seconds=10)
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        vault=vault,
        oracle=oracle,
    )

    object.__setattr__(vault, "reward_balance", 99)
    object.__setattr__(oracle, "price_timestamp", 99)

    assert state.vault is not None
    assert state.oracle is not None
    assert not hasattr(state.vault, "__dict__")
    assert not hasattr(state.oracle, "__dict__")
    assert state.vault.reward_balance == 2
    assert state.oracle.price_timestamp == 5


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
