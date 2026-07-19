"""Legacy settlement validation helpers for batch clearing."""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any, Callable, Dict, Optional, Tuple

from ..state.balances import Amount, AssetId, BalanceTable, PubKey
from ..state.lp import LPTable
from ..state.pools import PoolState
from .settlement import Settlement

_AnyFn = Callable[..., Any]


@dataclass(frozen=True)
class _SettlementValidationFactories:
    parse_create_pool_event_payload_fn: _AnyFn
    pool_state_fn: _AnyFn


def _created_pools_from_events(
    settlement: Settlement,
    pre_pools: Mapping[str, PoolState],
    factories: _SettlementValidationFactories,
) -> Tuple[Optional[Dict[str, PoolState]], Optional[str]]:
    created_pools: Dict[str, PoolState] = {}
    if not settlement.events:
        return created_pools, None

    for event in settlement.events:
        if event.get("type") != "CREATE_POOL":
            continue
        try:
            pool_id, asset0, asset1, fee_bps, curve_tag, curve_params, status, created_at = (
                factories.parse_create_pool_event_payload_fn(event)
            )
        except ValueError as exc:
            return None, str(exc)
        if pool_id in pre_pools:
            return None, f"CREATE_POOL conflicts with existing pool: {pool_id}"
        if pool_id in created_pools:
            return None, f"Duplicate CREATE_POOL event for pool: {pool_id}"
        try:
            created_pools[pool_id] = factories.pool_state_fn(
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
        except (TypeError, ValueError) as exc:
            return None, f"Invalid CREATE_POOL event for pool {pool_id}: {exc}"
    return created_pools, None


def _check_balance_nonnegative(settlement: Settlement, pre_balances: BalanceTable) -> Optional[str]:
    balance_net: Dict[Tuple[PubKey, AssetId], Amount] = defaultdict(int)
    for balance_delta in settlement.balance_deltas:
        balance_net[(balance_delta.pubkey, balance_delta.asset)] += balance_delta.net_delta()
    for (pubkey, asset), net in balance_net.items():
        current = pre_balances.get(pubkey, asset)
        if current + net < 0:
            return f"Negative balance: {pubkey}, {asset}, {current} + {net}"
    return None


def _check_reserve_nonnegative(
    settlement: Settlement,
    pools_view: Mapping[str, PoolState],
) -> Optional[str]:
    reserve_net: Dict[Tuple[str, AssetId], Amount] = defaultdict(int)
    for reserve_delta in settlement.reserve_deltas:
        reserve_net[(reserve_delta.pool_id, reserve_delta.asset)] += reserve_delta.net_delta()
    for (pool_id, asset), net in reserve_net.items():
        if pool_id not in pools_view:
            return f"Pool not found: {pool_id}"
        pool = pools_view[pool_id]
        try:
            current = pool.get_reserve(asset)
        except ValueError as exc:
            return str(exc)
        if current + net < 0:
            return f"Negative reserve: {pool_id}, {asset}, {current} + {net}"
    return None


def _check_lp_balance_nonnegative(
    settlement: Settlement,
    lp_view: LPTable,
) -> Optional[str]:
    lp_net: Dict[Tuple[PubKey, str], Amount] = defaultdict(int)
    for lp_delta in settlement.lp_deltas:
        lp_net[(lp_delta.pubkey, lp_delta.pool_id)] += lp_delta.net_delta()
    for (pubkey, pool_id), net in lp_net.items():
        current = lp_view.get(pubkey, pool_id)
        if current + net < 0:
            return f"Negative LP balance: {pubkey}, {pool_id}, {current} + {net}"
    return None


def _check_asset_conservation(settlement: Settlement) -> Optional[str]:
    asset_net: Dict[AssetId, Amount] = defaultdict(int)
    for balance_delta in settlement.balance_deltas:
        asset_net[balance_delta.asset] += balance_delta.net_delta()
    for reserve_delta in settlement.reserve_deltas:
        asset_net[reserve_delta.asset] += reserve_delta.net_delta()
    for asset, net in asset_net.items():
        if net != 0:
            return f"Asset conservation violation: {asset}, net_delta = {net}"
    return None


def _check_lp_supply_nonnegative(
    settlement: Settlement,
    pre_pools: Mapping[str, PoolState],
    pools_view: Mapping[str, PoolState],
) -> Optional[str]:
    supply_net: Dict[str, Amount] = defaultdict(int)
    for lp_delta in settlement.lp_deltas:
        supply_net[lp_delta.pool_id] += lp_delta.net_delta()
    for pool_id, net in supply_net.items():
        if pool_id not in pools_view:
            return f"LP delta references unknown pool: {pool_id}"
        start_supply = pre_pools[pool_id].lp_supply if pool_id in pre_pools else 0
        if start_supply + net < 0:
            return f"Negative LP supply: {pool_id}, {start_supply} + {net}"
    return None


def validate_settlement_with_factories(
    settlement: Settlement,
    pre_balances: BalanceTable,
    pre_pools: Mapping[str, PoolState],
    pre_lp_balances: Optional[LPTable],
    factories: _SettlementValidationFactories,
) -> Tuple[bool, Optional[str]]:
    created_pools, err = _created_pools_from_events(settlement, pre_pools, factories)
    if err is not None:
        return False, err
    pools_view: Dict[str, PoolState] = {**pre_pools, **(created_pools or {})}
    lp_view = pre_lp_balances or LPTable()

    try:
        for check_err in (
            _check_balance_nonnegative(settlement, pre_balances),
            _check_reserve_nonnegative(settlement, pools_view),
            _check_lp_balance_nonnegative(settlement, lp_view),
            _check_asset_conservation(settlement),
            _check_lp_supply_nonnegative(settlement, pre_pools, pools_view),
        ):
            if check_err is not None:
                return False, check_err
    except TypeError as exc:
        return False, str(exc)
    return True, None
