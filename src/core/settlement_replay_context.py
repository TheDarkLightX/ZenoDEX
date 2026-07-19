"""Replay context construction for strong settlement validation."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Dict, List, Optional

from ..state.balances import BalanceTable
from ..state.balances import copy_balance_table as mutable_balance_copy
from ..state.lp import LPTable
from ..state.lp import copy_lp_table as mutable_lp_copy
from ..state.pools import PoolState, copy_pool_state
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
    balances: BalanceTable
    pools: Mapping[str, PoolState]
    lp_balances: Optional[LPTable]


def copy_balance_table(balances: BalanceTable) -> BalanceTable:
    return mutable_balance_copy(balances)


def copy_lp_table(lp_balances: LPTable) -> LPTable:
    return mutable_lp_copy(lp_balances)


def build_replay_context(
    *,
    pre_balances: BalanceTable,
    pre_pools: Mapping[str, PoolState],
    pre_lp_balances: Optional[LPTable],
) -> ReplayContext:
    return ReplayContext(
        balances=copy_balance_table(pre_balances),
        pools={pool_id: copy_pool_state(pool) for pool_id, pool in pre_pools.items()},
        lp=copy_lp_table(pre_lp_balances) if pre_lp_balances is not None else LPTable(),
        expected_events=[],
        bal_deltas=[],
        res_deltas=[],
        lp_deltas=[],
    )
