"""In-place settlement application helpers for batch clearing."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, replace
from typing import Any, Callable, Dict, Optional, Tuple

from ..state.balances import Amount, AssetId, BalanceTable, PubKey
from ..state.lp import LPTable
from ..state.pools import PoolState
from .settlement import Settlement

_AnyFn = Callable[..., Any]


@dataclass(frozen=True)
class _SettlementApplyFactories:
    parse_create_pool_event_payload_fn: _AnyFn
    pool_state_fn: _AnyFn


def _apply_create_pool_events(
    settlement: Settlement,
    pools: Dict[str, PoolState],
    factories: _SettlementApplyFactories,
) -> None:
    if not settlement.events:
        return

    for event in settlement.events:
        if event.get("type") != "CREATE_POOL":
            continue
        pool_id, asset0, asset1, fee_bps, curve_tag, curve_params, status, created_at = (
            factories.parse_create_pool_event_payload_fn(event)
        )
        if pool_id in pools:
            raise ValueError(f"Pool already exists: {pool_id}")
        pools[pool_id] = factories.pool_state_fn(
            pool_id=pool_id,
            asset0=asset0,
            asset1=asset1,
            reserve0=0,
            reserve1=0,
            fee_bps=fee_bps,
            lp_supply=0,
            status=status,
            created_at=created_at,
            curve_tag=str(curve_tag),
            curve_params=str(curve_params),
        )


def _apply_balance_deltas(settlement: Settlement, balances: BalanceTable) -> None:
    balance_net: Dict[Tuple[PubKey, AssetId], Amount] = defaultdict(int)
    for balance_delta in settlement.balance_deltas:
        balance_net[(balance_delta.pubkey, balance_delta.asset)] += balance_delta.net_delta()
    for (pubkey, asset), net in sorted(balance_net.items(), key=lambda t: (t[0][0], t[0][1])):
        if net > 0:
            balances.add(pubkey, asset, net)
        elif net < 0:
            balances.subtract(pubkey, asset, -net)


def _apply_reserve_deltas(settlement: Settlement, pools: Dict[str, PoolState]) -> None:
    reserve_net: Dict[Tuple[str, AssetId], Amount] = defaultdict(int)
    for reserve_delta in settlement.reserve_deltas:
        reserve_net[(reserve_delta.pool_id, reserve_delta.asset)] += reserve_delta.net_delta()
    for (pool_id, asset), net in sorted(reserve_net.items(), key=lambda t: (t[0][0], t[0][1])):
        if pool_id not in pools:
            raise ValueError(f"Pool not found: {pool_id}")
        pool = pools[pool_id]
        current = pool.get_reserve(asset)
        new_reserve = current + net
        if new_reserve < 0:
            raise ValueError(f"Negative reserve: {pool_id}, {asset}, {current} + {net}")
        if asset == pool.asset0:
            pools[pool_id] = replace(pool, reserve0=new_reserve)
        else:
            # `get_reserve(asset)` above already guarantees membership.
            pools[pool_id] = replace(pool, reserve1=new_reserve)


def _apply_lp_deltas(
    settlement: Settlement,
    pools: Dict[str, PoolState],
    lp_balances: Optional[LPTable],
) -> None:
    supply_net: Dict[str, Amount] = defaultdict(int)
    lp_net: Dict[Tuple[PubKey, str], Amount] = defaultdict(int)
    for lp_delta in settlement.lp_deltas:
        supply_net[lp_delta.pool_id] += lp_delta.net_delta()
        lp_net[(lp_delta.pubkey, lp_delta.pool_id)] += lp_delta.net_delta()

    for pool_id, net in sorted(supply_net.items(), key=lambda t: t[0]):
        if pool_id not in pools:
            raise ValueError(f"Pool not found for LP delta: {pool_id}")
        new_supply = pools[pool_id].lp_supply + net
        if new_supply < 0:
            raise ValueError(f"Negative LP supply: {pool_id}")
        pools[pool_id] = replace(pools[pool_id], lp_supply=new_supply)

    if lp_balances is None:
        return
    for (pubkey, pool_id), net in sorted(lp_net.items(), key=lambda t: (t[0][0], t[0][1])):
        if net > 0:
            lp_balances.add(pubkey, pool_id, net)
        elif net < 0:
            lp_balances.subtract(pubkey, pool_id, -net)


def apply_settlement_with_factories(
    settlement: Settlement,
    balances: BalanceTable,
    pools: Dict[str, PoolState],
    lp_balances: Optional[LPTable],
    factories: _SettlementApplyFactories,
) -> None:
    _apply_create_pool_events(settlement, pools, factories)
    _apply_balance_deltas(settlement, balances)
    _apply_reserve_deltas(settlement, pools)
    _apply_lp_deltas(settlement, pools, lp_balances)
