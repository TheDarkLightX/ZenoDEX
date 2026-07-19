"""Settlement batch orchestration for deterministic batch clearing."""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Tuple

from ..state.balances import BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import PoolState, copy_pool_state
from .batch_clearing_deltas import (
    _aggregate_balance_deltas_chunked,
    _aggregate_lp_deltas_chunked,
    _aggregate_reserve_deltas_chunked,
)
from .settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement

_AnyFn = Callable[..., Any]


@dataclass(frozen=True)
class _IntentPartitions:
    create_pool_intents: List[Intent]
    intents_by_pool: Dict[str, List[Intent]]
    non_pool_intents: List[Intent]


@dataclass
class _SettlementBuffers:
    included_intents: List[Tuple[str, FillAction]]
    fills: List[Fill]
    balance_deltas: List[BalanceDelta]
    reserve_deltas: List[ReserveDelta]
    lp_deltas: List[LPDelta]
    events: List[Dict[str, Any]]


@dataclass(frozen=True)
class _SettlementExecutionState:
    pool_states: Dict[str, PoolState]
    balances: BalanceTable
    lp_balances: LPTable
    buffers: _SettlementBuffers


@dataclass(frozen=True)
class _SettlementPolicy:
    swap_ordering: str
    protocol_fee_share_bps: int
    protocol_fee_recipient_pubkey: Optional[PubKey]
    swap_tiebreak_seed: bytes | None = None


@dataclass(frozen=True)
class _SettlementComputeFactories:
    copy_balance_table_fn: _AnyFn
    copy_lp_table_fn: _AnyFn
    try_create_pool_fn: _AnyFn
    apply_create_pool_to_locals_fn: _AnyFn
    clear_batch_single_pool_fn: _AnyFn
    apply_filled_intent_to_locals_fn: _AnyFn


def compute_settlement_with_factories(
    intents: List[Intent],
    pools: Mapping[str, PoolState],
    balances: BalanceTable,
    lp_balances: Optional[LPTable],
    *,
    policy: _SettlementPolicy,
    chunk_size: int,
    factories: _SettlementComputeFactories,
) -> Settlement:
    pool_states: Dict[str, PoolState] = {
        pool_id: copy_pool_state(pool) for pool_id, pool in pools.items()
    }
    balances_local = factories.copy_balance_table_fn(balances)
    lp_local = factories.copy_lp_table_fn(lp_balances) if lp_balances is not None else LPTable()
    partitions = _partition_settlement_intents(intents)
    buffers = _new_settlement_buffers()
    execution_state = _SettlementExecutionState(
        pool_states=pool_states,
        balances=balances_local,
        lp_balances=lp_local,
        buffers=buffers,
    )

    _process_create_pool_phase(execution_state, partitions.create_pool_intents, factories=factories)
    _process_pool_intent_phase(
        execution_state,
        partitions.intents_by_pool,
        policy=policy,
        factories=factories,
    )
    _append_rejected_intents(buffers, partitions.non_pool_intents, reason="INVALID_INTENT")
    return _build_settlement_from_buffers(buffers, chunk_size=chunk_size)


def _new_settlement_buffers() -> _SettlementBuffers:
    return _SettlementBuffers(
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=[],
    )


def _partition_settlement_intents(intents: List[Intent]) -> _IntentPartitions:
    intents_by_pool: Dict[str, List[Intent]] = defaultdict(list)
    create_pool_intents: List[Intent] = []
    non_pool_intents: List[Intent] = []

    for intent in intents:
        if intent.kind == IntentKind.CREATE_POOL:
            create_pool_intents.append(intent)
            continue

        pool_id = intent.get_field("pool_id")
        if isinstance(pool_id, str) and pool_id:
            intents_by_pool[pool_id].append(intent)
        else:
            non_pool_intents.append(intent)

    return _IntentPartitions(
        create_pool_intents=create_pool_intents,
        intents_by_pool=dict(intents_by_pool),
        non_pool_intents=non_pool_intents,
    )


def _append_rejected_intents(
    buffers: _SettlementBuffers,
    intents: List[Intent],
    *,
    reason: str,
) -> None:
    for intent in intents:
        buffers.included_intents.append((intent.intent_id, FillAction.REJECT))
        buffers.fills.append(Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason=reason))


def _build_settlement_from_buffers(
    buffers: _SettlementBuffers,
    *,
    chunk_size: int,
) -> Settlement:
    # Invariant chunking: aggregate deltas in bounded chunks to reduce payload
    # size while preserving semantics.
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",  # Will be set by caller
        included_intents=buffers.included_intents,
        fills=buffers.fills,
        balance_deltas=_aggregate_balance_deltas_chunked(
            buffers.balance_deltas,
            chunk_size=chunk_size,
        ),
        reserve_deltas=_aggregate_reserve_deltas_chunked(
            buffers.reserve_deltas,
            chunk_size=chunk_size,
        ),
        lp_deltas=_aggregate_lp_deltas_chunked(
            buffers.lp_deltas,
            chunk_size=chunk_size,
        ),
        events=buffers.events or None,
    )


def _process_create_pool_phase(
    state: _SettlementExecutionState,
    create_pool_intents: List[Intent],
    *,
    factories: _SettlementComputeFactories,
) -> None:
    # CREATE_POOL executes first so later intents can reference new pools.
    for intent in sorted(create_pool_intents, key=lambda i: i.intent_id):
        fill, pool_id, created_pool, _err = factories.try_create_pool_fn(
            intent,
            state.pool_states,
            state.balances,
        )
        state.buffers.included_intents.append((intent.intent_id, fill.action))
        state.buffers.fills.append(fill)

        if fill.action != FillAction.FILL:
            continue

        if pool_id is None or created_pool is None:
            raise RuntimeError("create_pool fill missing pool identifier or created pool")
        factories.apply_create_pool_to_locals_fn(
            intent=intent,
            pool_id=pool_id,
            created_pool=created_pool,
            balances=state.balances,
            lp_balances=state.lp_balances,
            balance_deltas=state.buffers.balance_deltas,
            reserve_deltas=state.buffers.reserve_deltas,
            lp_deltas=state.buffers.lp_deltas,
            events=state.buffers.events,
        )


def _process_pool_intent_phase(
    state: _SettlementExecutionState,
    intents_by_pool: Dict[str, List[Intent]],
    *,
    policy: _SettlementPolicy,
    factories: _SettlementComputeFactories,
) -> None:
    for pool_id in sorted(intents_by_pool.keys()):
        pool_intents = intents_by_pool[pool_id]
        if pool_id not in state.pool_states:
            _append_rejected_intents(state.buffers, pool_intents, reason="POOL_NOT_FOUND")
            continue

        pool_state = state.pool_states[pool_id]
        fills = factories.clear_batch_single_pool_fn(
            pool_intents,
            pool_state,
            state.balances,
            state.lp_balances,
            swap_ordering=policy.swap_ordering,
            protocol_fee_share_bps=policy.protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=policy.protocol_fee_recipient_pubkey,
            swap_tiebreak_seed=policy.swap_tiebreak_seed,
        )

        for fill in fills:
            state.buffers.fills.append(fill)
            state.buffers.included_intents.append((fill.intent_id, fill.action))

            if fill.action != FillAction.FILL:
                continue

            intent = next(i for i in pool_intents if i.intent_id == fill.intent_id)
            factories.apply_filled_intent_to_locals_fn(
                intent=intent,
                fill=fill,
                pool_id=pool_id,
                pool_state=pool_state,
                balances=state.balances,
                lp_balances=state.lp_balances,
                balance_deltas=state.buffers.balance_deltas,
                reserve_deltas=state.buffers.reserve_deltas,
                lp_deltas=state.buffers.lp_deltas,
                protocol_fee_recipient_pubkey=policy.protocol_fee_recipient_pubkey,
            )

        state.pool_states[pool_id] = pool_state
