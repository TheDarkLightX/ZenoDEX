"""Owned immutable snapshots for committed DEX state.

Mutable tables remain local builders and settlement scratch space. A committed
``DexState`` detaches its complete object graph from those builders while
preserving the established read interfaces.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any, NoReturn

from ..core.perps import (
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpClearinghouseNpAccount,
    PerpClearinghouseNpMarketState,
    PerpClearinghouseNpPendingIntent,
    PerpMarketState,
    PerpsState,
)
from .balances import Amount, AssetId, BalanceTable, PubKey
from .immutable_collections import FrozenDict, deep_freeze
from .lp import LPTable, PoolId
from .nonces import NonceTable
from .pools import PoolState, copy_pool_state


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

    def add(self, pubkey: PubKey, asset: AssetId, delta: Amount) -> None:
        _immutable_state(pubkey, asset, delta)

    def subtract(self, pubkey: PubKey, asset: AssetId, delta: Amount) -> None:
        _immutable_state(pubkey, asset, delta)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenBalanceTable:
        return self


class FrozenLPTable(LPTable):
    """Read-compatible immutable ``LPTable`` snapshot with metadata."""

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

    def set(self, pubkey: PubKey, pool_id: PoolId, amount: Amount) -> None:
        _immutable_state(pubkey, pool_id, amount)

    def add(self, pubkey: PubKey, pool_id: PoolId, delta: int) -> None:
        _immutable_state(pubkey, pool_id, delta)

    def subtract(self, pubkey: PubKey, pool_id: PoolId, delta: Amount) -> None:
        _immutable_state(pubkey, pool_id, delta)

    def set_last_mint_timestamp(
        self,
        pubkey: PubKey,
        pool_id: PoolId,
        timestamp: int,
    ) -> None:
        _immutable_state(pubkey, pool_id, timestamp)

    def clear_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> None:
        _immutable_state(pubkey, pool_id)

    def set_last_remove_timestamp(
        self,
        pubkey: PubKey,
        pool_id: PoolId,
        timestamp: int,
    ) -> None:
        _immutable_state(pubkey, pool_id, timestamp)

    def clear_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> None:
        _immutable_state(pubkey, pool_id)

    def set_churn_tier(self, pubkey: PubKey, pool_id: PoolId, tier: int) -> None:
        _immutable_state(pubkey, pool_id, tier)

    def set_last_churn_update_timestamp(
        self,
        pubkey: PubKey,
        pool_id: PoolId,
        timestamp: int,
    ) -> None:
        _immutable_state(pubkey, pool_id, timestamp)

    def clear_last_churn_update_timestamp(
        self,
        pubkey: PubKey,
        pool_id: PoolId,
    ) -> None:
        _immutable_state(pubkey, pool_id)

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
    if type(source) is FrozenBalanceTable:
        return source
    if type(source) is not BalanceTable:
        raise TypeError("balances must be an exact BalanceTable")
    return FrozenBalanceTable(source)


def freeze_lp_table(source: LPTable) -> LPTable:
    if type(source) is FrozenLPTable:
        return source
    if type(source) is not LPTable:
        raise TypeError("lp_balances must be an exact LPTable")
    return FrozenLPTable(source)


def freeze_nonce_table(source: NonceTable) -> NonceTable:
    if type(source) is FrozenNonceTable:
        return source
    if type(source) is not NonceTable:
        raise TypeError("nonces must be an exact NonceTable")
    return FrozenNonceTable(source)


def freeze_pool_state(source: PoolState) -> PoolState:
    if type(source) is FrozenPoolState:
        return source
    if type(source) is not PoolState:
        raise TypeError("pool values must be exact PoolState instances")
    scratch = copy_pool_state(source)
    return FrozenPoolState(
        pool_id=scratch.pool_id,
        asset0=scratch.asset0,
        asset1=scratch.asset1,
        reserve0=scratch.reserve0,
        reserve1=scratch.reserve1,
        fee_bps=scratch.fee_bps,
        lp_supply=scratch.lp_supply,
        status=scratch.status,
        created_at=scratch.created_at,
        curve_tag=scratch.curve_tag,
        curve_params=scratch.curve_params,
    )


def freeze_pool_mapping(source: Mapping[str, PoolState]) -> FrozenDict:
    if type(source) is FrozenDict:
        for pool_id, pool in source.items():
            if type(pool_id) is not str or not pool_id:
                raise TypeError("pool keys must be non-empty exact strings")
            if type(pool) is not FrozenPoolState:
                raise TypeError("frozen pool mappings must contain frozen pools")
        return source
    if type(source) is not dict:
        raise TypeError("pools must be an exact dict or owned FrozenDict")
    snapshot: dict[str, PoolState] = {}
    for pool_id, pool in source.items():
        if type(pool_id) is not str or not pool_id:
            raise TypeError("pool keys must be non-empty exact strings")
        snapshot[pool_id] = freeze_pool_state(pool)
    return FrozenDict(snapshot)


def _validate_exact_perps_types(source: PerpsState) -> None:
    """Reject behavior-bearing subclasses before committed-state admission."""

    if type(source) is not PerpsState:
        raise TypeError("perps must be an exact PerpsState")
    if type(source.version) is not int:
        raise TypeError("perps.version must be an exact int")
    if not isinstance(source.markets, Mapping):
        raise TypeError("perps.markets must be mapping-compatible")

    allowed_market_types = (
        PerpMarketState,
        PerpClearinghouse2pMarketState,
        PerpClearinghouse3pTransferMarketState,
        PerpClearinghouseNpMarketState,
    )
    for market_id, market in source.markets.items():
        if type(market_id) is not str or not market_id:
            raise TypeError("perps market ids must be non-empty exact strings")
        if type(market) not in allowed_market_types:
            raise TypeError("perps market must use an exact supported state type")
        if type(market) is PerpMarketState and any(
            type(account) is not PerpAccountState for account in market.accounts.values()
        ):
            raise TypeError("isolated perps accounts must be exact PerpAccountState values")
        if type(market) is PerpClearinghouseNpMarketState:
            if type(market.accounts) is not tuple or any(
                type(account) is not PerpClearinghouseNpAccount for account in market.accounts
            ):
                raise TypeError("N-party perps accounts must use exact tuple values")
            if type(market.pending_intents) is not tuple or any(
                type(intent) is not PerpClearinghouseNpPendingIntent
                for intent in market.pending_intents
            ):
                raise TypeError("N-party pending intents must use exact tuple values")


def freeze_perps_state(source: PerpsState) -> PerpsState:
    """Own perps state after excluding behavior-changing runtime subclasses."""

    _validate_exact_perps_types(source)
    frozen = deep_freeze(source)
    if type(frozen) is not PerpsState:  # pragma: no cover
        raise AssertionError("perps snapshot lost its exact top-level type")
    _validate_exact_perps_types(frozen)
    return frozen


def freeze_optional_module_state(value: Any) -> Any:
    """Detach and recursively freeze an optional nested module state."""

    if value is None:
        return None
    if isinstance(value, PerpsState):
        return freeze_perps_state(value)
    return deep_freeze(value)
