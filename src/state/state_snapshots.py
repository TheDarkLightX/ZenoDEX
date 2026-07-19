"""Immutable owned snapshots for committed DEX state.

Mutable tables remain useful as local builders and settlement scratch space.
Committed ``DexState`` values, however, must never retain aliases to those
builders.  The snapshot classes below preserve the historical read interfaces
while rejecting every mutation method and freezing their private mappings.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any, NoReturn

from .balances import Amount, AssetId, BalanceDelta, BalanceTable, PubKey
from .immutable_collections import FrozenDict, deep_freeze
from .lp import LPTable, PoolId
from .nonces import NonceTable
from .pools import PoolState


def _immutable_state(*_args: object, **_kwargs: object) -> NoReturn:
    raise TypeError("committed state snapshot is immutable")


class FrozenBalanceTable(BalanceTable):
    """Read-compatible immutable ``BalanceTable`` snapshot."""

    def __init__(self, source: BalanceTable) -> None:
        object.__setattr__(self, "_snapshot_sealed", False)
        BalanceTable.__init__(self)
        for (pubkey, asset), amount in source.get_all_balances().items():
            BalanceTable.set(self, pubkey, asset, amount)
        object.__setattr__(self, "_balances", FrozenDict(self._balances))
        object.__setattr__(self, "_snapshot_sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if self.__dict__.get("_snapshot_sealed", False):
            raise TypeError("committed balance snapshot is immutable")
        object.__setattr__(self, name, value)

    def set(self, pubkey: PubKey, asset: AssetId, amount: Amount) -> None:
        _immutable_state(pubkey, asset, amount)

    def add(self, pubkey: PubKey, asset: AssetId, delta: BalanceDelta) -> None:
        _immutable_state(pubkey, asset, delta)

    def subtract(self, pubkey: PubKey, asset: AssetId, delta: Amount) -> None:
        _immutable_state(pubkey, asset, delta)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenBalanceTable:
        return self


class FrozenLPTable(LPTable):
    """Read-compatible immutable ``LPTable`` snapshot, including metadata."""

    def __init__(self, source: LPTable) -> None:
        object.__setattr__(self, "_snapshot_sealed", False)
        LPTable.__init__(self)
        for (pubkey, pool_id), amount in source.get_all_balances().items():
            LPTable.set(self, pubkey, pool_id, amount)
        for (pubkey, pool_id), timestamp in source.get_all_last_mint_timestamps().items():
            if LPTable.get(self, pubkey, pool_id) > 0:
                LPTable.set_last_mint_timestamp(self, pubkey, pool_id, timestamp)
        for (pubkey, pool_id), timestamp in source.get_all_last_remove_timestamps().items():
            LPTable.set_last_remove_timestamp(self, pubkey, pool_id, timestamp)
        for (pubkey, pool_id), tier in source.get_all_churn_tiers().items():
            LPTable.set_churn_tier(self, pubkey, pool_id, tier)
        for (
            pubkey,
            pool_id,
        ), timestamp in source.get_all_last_churn_update_timestamps().items():
            LPTable.set_last_churn_update_timestamp(self, pubkey, pool_id, timestamp)

        for name in (
            "_balances",
            "_last_mint_timestamps",
            "_last_remove_timestamps",
            "_churn_tiers",
            "_last_churn_update_timestamps",
        ):
            object.__setattr__(self, name, FrozenDict(getattr(self, name)))
        object.__setattr__(self, "_snapshot_sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if self.__dict__.get("_snapshot_sealed", False):
            raise TypeError("committed LP snapshot is immutable")
        object.__setattr__(self, name, value)

    set = _immutable_state
    add = _immutable_state
    subtract = _immutable_state
    set_last_mint_timestamp = _immutable_state
    clear_last_mint_timestamp = _immutable_state
    set_last_remove_timestamp = _immutable_state
    clear_last_remove_timestamp = _immutable_state
    set_churn_tier = _immutable_state
    set_last_churn_update_timestamp = _immutable_state
    clear_last_churn_update_timestamp = _immutable_state

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenLPTable:
        return self


class FrozenNonceTable(NonceTable):
    """Read-compatible immutable replay-protection snapshot."""

    def __init__(self, source: NonceTable) -> None:
        object.__setattr__(self, "_snapshot_sealed", False)
        NonceTable.__init__(self)
        for pubkey, nonce in source.get_all().items():
            NonceTable.set_last(self, pubkey, nonce)
        object.__setattr__(self, "_last", FrozenDict(self._last))
        object.__setattr__(self, "_snapshot_sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if self.__dict__.get("_snapshot_sealed", False):
            raise TypeError("committed nonce snapshot is immutable")
        object.__setattr__(self, name, value)

    def set_last(self, pubkey: PubKey, last_nonce: int) -> None:
        _immutable_state(pubkey, last_nonce)

    def apply_accept(self, pubkey: PubKey, nonce: int) -> None:
        _immutable_state(pubkey, nonce)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenNonceTable:
        return self


class FrozenPoolState(PoolState):
    """A canonical ``PoolState`` whose economic fields cannot be reassigned."""

    def __post_init__(self) -> None:
        object.__setattr__(self, "_snapshot_sealed", False)
        PoolState.__post_init__(self)
        object.__setattr__(self, "_snapshot_sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if self.__dict__.get("_snapshot_sealed", False):
            raise TypeError("committed pool snapshot is immutable")
        object.__setattr__(self, name, value)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenPoolState:
        return self


def freeze_balance_table(source: BalanceTable) -> BalanceTable:
    if not isinstance(source, BalanceTable):
        raise TypeError("balances must be a BalanceTable")
    if isinstance(source, FrozenBalanceTable):
        return source
    return FrozenBalanceTable(source)


def freeze_lp_table(source: LPTable) -> LPTable:
    if not isinstance(source, LPTable):
        raise TypeError("lp_balances must be an LPTable")
    if isinstance(source, FrozenLPTable):
        return source
    return FrozenLPTable(source)


def freeze_nonce_table(source: NonceTable) -> NonceTable:
    if not isinstance(source, NonceTable):
        raise TypeError("nonces must be a NonceTable")
    if isinstance(source, FrozenNonceTable):
        return source
    return FrozenNonceTable(source)


def freeze_pool_state(source: PoolState) -> PoolState:
    if not isinstance(source, PoolState):
        raise TypeError("pool values must be PoolState instances")
    if isinstance(source, FrozenPoolState):
        return source
    return FrozenPoolState(
        pool_id=source.pool_id,
        asset0=source.asset0,
        asset1=source.asset1,
        reserve0=source.reserve0,
        reserve1=source.reserve1,
        fee_bps=source.fee_bps,
        lp_supply=source.lp_supply,
        status=source.status,
        created_at=source.created_at,
        curve_tag=source.curve_tag,
        curve_params=source.curve_params,
    )


def freeze_pool_mapping(source: Mapping[str, PoolState]) -> FrozenDict:
    if not isinstance(source, Mapping):
        raise TypeError("pools must be a mapping")
    snapshot: dict[str, PoolState] = {}
    for pool_id, pool in source.items():
        if not isinstance(pool_id, str) or not pool_id:
            raise TypeError("pool keys must be non-empty strings")
        snapshot[pool_id] = freeze_pool_state(pool)
    return FrozenDict(snapshot)


def freeze_optional_module_state(value: Any) -> Any:
    """Detach and recursively freeze an optional nested module state."""

    if value is None:
        return None
    return deep_freeze(value)
