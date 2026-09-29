"""Replay context construction for strong settlement validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Mapping, Optional

from ..state.balances import BalanceSnapshot, BalanceTable
from ..state.lp import LPSnapshot, LPTable
from ..state.pools import PoolSnapshot, PoolState, copy_pool_state
from .settlement import BalanceDelta, LPDelta, ReserveDelta


@dataclass
class ReplayContext:
    balances: BalanceTable
    pools: Dict[str, PoolState]
    lp: LPTable
    expected_events: List[dict]
    bal_deltas: List[BalanceDelta]
    res_deltas: List[ReserveDelta]
    lp_deltas: List[LPDelta]


@dataclass(frozen=True)
class SettlementPreState:
    balances: BalanceTable | BalanceSnapshot
    pools: Mapping[str, PoolState | PoolSnapshot]
    lp_balances: Optional[LPTable | LPSnapshot]


def copy_balance_table(balances: BalanceTable | BalanceSnapshot) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, amount)
    return copied


def copy_lp_table(lp_balances: LPTable | LPSnapshot) -> LPTable:
    copied = LPTable()
    for (pubkey, pool_id), amount in lp_balances.get_all_balances().items():
        copied.set(pubkey, pool_id, amount)
    for (pubkey, pool_id), timestamp in lp_balances.get_all_last_mint_timestamps().items():
        if copied.get(pubkey, pool_id) > 0:
            copied.set_last_mint_timestamp(pubkey, pool_id, timestamp)
    return copied


def build_replay_context(
    *,
    pre_balances: BalanceTable | BalanceSnapshot,
    pre_pools: Mapping[str, PoolState | PoolSnapshot],
    pre_lp_balances: Optional[LPTable | LPSnapshot],
) -> ReplayContext:
    # Replay runs on private builder copies; committed snapshots are never mutated.
    return ReplayContext(
        balances=copy_balance_table(pre_balances),
        pools={pool_id: copy_pool_state(pool) for pool_id, pool in pre_pools.items()},
        lp=copy_lp_table(pre_lp_balances) if pre_lp_balances is not None else LPTable(),
        expected_events=[],
        bal_deltas=[],
        res_deltas=[],
        lp_deltas=[],
    )
