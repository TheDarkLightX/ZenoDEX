"""
Batch clearing algorithm for deterministic settlement.

PRODUCTION REQUIREMENT: Always use batch clearing, never sequential execution.
--------------------------------------------------------------------------
- Sequential CPMM execution has fundamental sandwich MEV: an adversary who
  controls ordering can insert transactions before and after a victim swap,
  extracting value via price manipulation (H-GT-002).
- Batch clearing with AB-optimal ordering eliminates this MEV vector by
  processing all intents atomically against a single reserve snapshot, with
  the ordering chosen to maximize executed volume (A) and surplus (B)
  rather than being attacker-controlled (H-BC-016).
- Production deployments MUST route through ``compute_settlement()`` with
  ``swap_ordering="optimal_ab_bounded"`` (exact, bounded) or
  ``"greedy_ab_refined"`` (heuristic, unbounded-n). Direct sequential
  application of swaps against a live pool is NOT safe for adversarial
  environments.
--------------------------------------------------------------------------

This module implements the batch clearing algorithm that processes multiple
intents in a single batch to reduce ordering dependence.

Algorithm Design:
- Type: Greedy Monotone Processing / Constrained Optimization
- Time Complexity: O(n log n) for sorting + O(n) for processing
- Space Complexity: O(n) for intent storage and delta tracking
- Invariant: After processing intent i, total deltas satisfy conservation:
  Σ_account_deltas + Σ_pool_deltas = 0 (per asset)
"""

from __future__ import annotations

import itertools
from collections import defaultdict
from dataclasses import dataclass, replace
from typing import Any, Dict, List, Optional, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from ..state.balances import Amount, AssetId, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import CURVE_TAG_CPMM, PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .batch_clearing_create_pool import (
    _apply_create_pool_to_locals,
    _parse_create_pool_event_payload,
    _try_create_pool_with_factory,
)
from .batch_clearing_deltas import (
    _aggregate_balance_deltas_chunked,
    _aggregate_lp_deltas_chunked,
    _aggregate_reserve_deltas_chunked,
)
from .batch_clearing_swaps import (
    _apply_swap_fill_to_scratch_balances,
    _reserves_after_swap_fill,
)
from .cpmm import compute_fee_total
from .domain_limits import is_strict_int
from .liquidity import add_liquidity, create_pool, remove_liquidity
from .settlement import (
    BalanceDelta,
    Fill,
    FillAction,
    LPDelta,
    ReserveDelta,
    Settlement,
)

_SWAP_ORDERING_LIMIT_PRICE = "limit_price"
_SWAP_ORDERING_OPTIMAL_AB_BOUNDED = "optimal_ab_bounded"
_SWAP_ORDERING_GREEDY_AB = "greedy_ab"
_SWAP_ORDERING_GREEDY_AB_REFINED = "greedy_ab_refined"
_SWAP_ORDERING_GREEDY_AB_GLOBAL = "greedy_ab_global"
_SWAP_ORDERING_MCI_AB_GLOBAL = "mci_ab_global"
_SWAP_ORDERING_COW_PAIR_NETTING_V1 = "cow_pair_netting_v1"
_SWAP_ORDERING_CHOICES = frozenset({
    _SWAP_ORDERING_LIMIT_PRICE,
    _SWAP_ORDERING_OPTIMAL_AB_BOUNDED,
    _SWAP_ORDERING_GREEDY_AB,
    _SWAP_ORDERING_GREEDY_AB_REFINED,
    _SWAP_ORDERING_GREEDY_AB_GLOBAL,
    _SWAP_ORDERING_MCI_AB_GLOBAL,
    _SWAP_ORDERING_COW_PAIR_NETTING_V1,
})

# Bounded brute-force safety cap for AB-optimal ordering.
# For N > this limit, greedy_ab should be used instead.
_MAX_SWAP_ORDERING_BRUTE_FORCE_N = 12
# Global pair-swap refinement can be expensive; cap intent count for this mode.
_MAX_SWAP_ORDERING_GLOBAL_REFINE_N = 24
# MCI insertion is heavier than greedy seeding; keep it opt-in and bounded.
_MAX_SWAP_ORDERING_MCI_N = 18
# Chunk size for settlement delta aggregation (invariant chunking promotion).
_DELTA_AGG_CHUNK_SIZE = 128


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


def _build_settlement_from_buffers(buffers: _SettlementBuffers) -> Settlement:
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
            chunk_size=_DELTA_AGG_CHUNK_SIZE,
        ),
        reserve_deltas=_aggregate_reserve_deltas_chunked(
            buffers.reserve_deltas,
            chunk_size=_DELTA_AGG_CHUNK_SIZE,
        ),
        lp_deltas=_aggregate_lp_deltas_chunked(
            buffers.lp_deltas,
            chunk_size=_DELTA_AGG_CHUNK_SIZE,
        ),
        events=buffers.events or None,
    )


def _process_create_pool_phase(
    state: _SettlementExecutionState,
    create_pool_intents: List[Intent],
) -> None:
    # CREATE_POOL executes first so later intents can reference new pools.
    for intent in sorted(create_pool_intents, key=lambda i: i.intent_id):
        fill, pool_id, created_pool, _err = _try_create_pool(intent, state.pool_states, state.balances)
        state.buffers.included_intents.append((intent.intent_id, fill.action))
        state.buffers.fills.append(fill)

        if fill.action != FillAction.FILL:
            continue

        if pool_id is None or created_pool is None:
            raise RuntimeError("create_pool fill missing pool identifier or created pool")
        _apply_create_pool_to_locals(
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
) -> None:
    for pool_id in sorted(intents_by_pool.keys()):
        pool_intents = intents_by_pool[pool_id]
        if pool_id not in state.pool_states:
            _append_rejected_intents(state.buffers, pool_intents, reason="POOL_NOT_FOUND")
            continue

        pool_state = state.pool_states[pool_id]
        fills = clear_batch_single_pool(
            pool_intents,
            pool_state,
            state.balances,
            state.lp_balances,
            swap_ordering=policy.swap_ordering,
            protocol_fee_share_bps=policy.protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=policy.protocol_fee_recipient_pubkey,
        )

        for fill in fills:
            state.buffers.fills.append(fill)
            state.buffers.included_intents.append((fill.intent_id, fill.action))

            if fill.action != FillAction.FILL:
                continue

            intent = next(i for i in pool_intents if i.intent_id == fill.intent_id)
            _apply_filled_intent_to_locals(
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


def compute_settlement(
    intents: List[Intent],
    pools: Dict[str, PoolState],
    balances: BalanceTable,
    lp_balances: Optional[LPTable] = None,
    *,
    swap_ordering: str = _SWAP_ORDERING_GREEDY_AB_REFINED,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> Settlement:
    """
    Compute settlement for a batch of intents.

    Algorithm:
    1. Group intents by pool_id
    2. For each pool, sort intents by limit price (best first)
    3. Process intents sequentially, computing fills
    4. Aggregate deltas across all pools
    5. Verify global conservation and non-negativity

    Args:
        intents: List of intents to process
        pools: Dictionary mapping pool_id -> PoolState
        balances: Current balance table (for validation)

    Returns:
        Settlement object with fills and deltas
    """
    if swap_ordering not in _SWAP_ORDERING_CHOICES:
        raise ValueError(f"unsupported swap_ordering: {swap_ordering!r}")
    if not is_strict_int(protocol_fee_share_bps) or not (0 <= protocol_fee_share_bps <= 10000):
        raise ValueError("protocol_fee_share_bps must be an int in [0, 10000]")
    if protocol_fee_share_bps > 0 and not protocol_fee_recipient_pubkey:
        raise ValueError("protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0")
    # Work on local copies (functional core / imperative shell).
    pool_states: Dict[str, PoolState] = {pool_id: replace(pool) for pool_id, pool in pools.items()}
    balances_local = _copy_balance_table(balances)
    lp_local = _copy_lp_table(lp_balances) if lp_balances is not None else LPTable()
    partitions = _partition_settlement_intents(intents)
    buffers = _new_settlement_buffers()
    policy = _SettlementPolicy(
        swap_ordering=swap_ordering,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    execution_state = _SettlementExecutionState(
        pool_states=pool_states,
        balances=balances_local,
        lp_balances=lp_local,
        buffers=buffers,
    )

    _process_create_pool_phase(execution_state, partitions.create_pool_intents)
    _process_pool_intent_phase(
        execution_state,
        partitions.intents_by_pool,
        policy=policy,
    )
    _append_rejected_intents(buffers, partitions.non_pool_intents, reason="INVALID_INTENT")
    return _build_settlement_from_buffers(buffers)


def _copy_balance_table(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, amount)
    return copied


def _copy_lp_table(lp_balances: LPTable) -> LPTable:
    copied = LPTable()
    for (pubkey, pool_id), amount in lp_balances.get_all_balances().items():
        copied.set(pubkey, pool_id, amount)
    for (pubkey, pool_id), timestamp in lp_balances.get_all_last_mint_timestamps().items():
        if copied.get(pubkey, pool_id) > 0:
            copied.set_last_mint_timestamp(pubkey, pool_id, timestamp)
    return copied


def _try_create_pool(
    intent: Intent,
    pool_states: Dict[str, PoolState],
    balances: BalanceTable,
) -> tuple[Fill, Optional[str], Optional[PoolState], Optional[str]]:
    return _try_create_pool_with_factory(
        intent,
        pool_states,
        balances,
        create_pool_fn=create_pool,
    )


def _apply_filled_intent_to_locals(
    intent: Intent,
    fill: Fill,
    pool_id: str,
    pool_state: PoolState,
    balances: BalanceTable,
    lp_balances: LPTable,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    lp_deltas: List[LPDelta],
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> None:
    sender = intent.sender_pubkey
    recipient = intent.get_field("recipient", sender)

    if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        asset_in = intent.get_field("asset_in")
        asset_out = intent.get_field("asset_out")
        amount_in = fill.amount_in_filled or 0
        amount_out = fill.amount_out_filled or 0
        protocol_fee = fill.protocol_fee_paid or 0

        balances.subtract(sender, asset_in, amount_in)
        balances.add(recipient, asset_out, amount_out)
        if protocol_fee:
            if not protocol_fee_recipient_pubkey:
                raise ValueError("protocol_fee_recipient_pubkey is required for protocol fee capture")
            # Review finding (grade A-): the fee-recipient guard was correct at
            # runtime, but the later delta row still carried Optional[PubKey].
            # Keep the validated non-null recipient in one variable so the
            # consensus delta witness and balance mutation share the same value.
            fee_recipient = protocol_fee_recipient_pubkey
            balances.add(fee_recipient, asset_in, protocol_fee)

        balance_deltas.append(BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=amount_in))
        balance_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=amount_out, delta_sub=0))
        if protocol_fee:
            balance_deltas.append(
                BalanceDelta(
                    pubkey=fee_recipient,
                    asset=asset_in,
                    delta_add=protocol_fee,
                    delta_sub=0,
                )
            )

        # CoW-style netting: do not touch pool reserves/deltas.
        if fill.reason == "COW_NETTED":
            return

        reserve_amount_in = amount_in - protocol_fee
        reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_in, delta_add=reserve_amount_in, delta_sub=0))
        reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_out, delta_add=0, delta_sub=amount_out))

        if asset_in == pool_state.asset0:
            pool_state.reserve0 += reserve_amount_in
            pool_state.reserve1 -= amount_out
        else:
            pool_state.reserve1 += reserve_amount_in
            pool_state.reserve0 -= amount_out
        return

    if intent.kind == IntentKind.ADD_LIQUIDITY:
        amount0_used = fill.amount0_used or 0
        amount1_used = fill.amount1_used or 0
        lp_minted = fill.lp_minted or 0

        balances.subtract(sender, pool_state.asset0, amount0_used)
        balances.subtract(sender, pool_state.asset1, amount1_used)
        lp_balances.add(recipient, pool_id, lp_minted)

        balance_deltas.append(BalanceDelta(pubkey=sender, asset=pool_state.asset0, delta_add=0, delta_sub=amount0_used))
        balance_deltas.append(BalanceDelta(pubkey=sender, asset=pool_state.asset1, delta_add=0, delta_sub=amount1_used))
        reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool_state.asset0, delta_add=amount0_used, delta_sub=0))
        reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool_state.asset1, delta_add=amount1_used, delta_sub=0))
        lp_deltas.append(LPDelta(pubkey=recipient, pool_id=pool_id, delta_add=lp_minted, delta_sub=0))

        pool_state.reserve0 += amount0_used
        pool_state.reserve1 += amount1_used
        pool_state.lp_supply += lp_minted
        return

    if intent.kind == IntentKind.REMOVE_LIQUIDITY:
        lp_burned = fill.lp_burned or 0
        amount0_out = fill.amount0_out or 0
        amount1_out = fill.amount1_out or 0

        lp_balances.subtract(sender, pool_id, lp_burned)
        balances.add(recipient, pool_state.asset0, amount0_out)
        balances.add(recipient, pool_state.asset1, amount1_out)

        lp_deltas.append(LPDelta(pubkey=sender, pool_id=pool_id, delta_add=0, delta_sub=lp_burned))
        balance_deltas.append(BalanceDelta(pubkey=recipient, asset=pool_state.asset0, delta_add=amount0_out, delta_sub=0))
        balance_deltas.append(BalanceDelta(pubkey=recipient, asset=pool_state.asset1, delta_add=amount1_out, delta_sub=0))
        reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool_state.asset0, delta_add=0, delta_sub=amount0_out))
        reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool_state.asset1, delta_add=0, delta_sub=amount1_out))

        pool_state.reserve0 -= amount0_out
        pool_state.reserve1 -= amount1_out
        pool_state.lp_supply -= lp_burned
        return

    raise ValueError(f"Unsupported intent kind for fill application: {intent.kind}")


def clear_batch_single_pool(
    intents: List[Intent],
    pool_state: PoolState,
    balances: BalanceTable,
    lp_balances: LPTable,
    *,
    swap_ordering: str = _SWAP_ORDERING_GREEDY_AB_REFINED,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> List[Fill]:
    """
    Process batch of intents for a single pool.
    
    Deterministic: clear swaps under the selected ordering and process
    liquidity intents in receive order.
    
    Args:
        intents: List of intents for this pool
        pool_state: Current pool state
        
    Returns:
        List of Fill objects
    """
    if swap_ordering not in _SWAP_ORDERING_CHOICES:
        raise ValueError(f"unsupported swap_ordering: {swap_ordering!r}")
    if not is_strict_int(protocol_fee_share_bps) or not (0 <= protocol_fee_share_bps <= 10000):
        raise ValueError("protocol_fee_share_bps must be an int in [0, 10000]")
    if protocol_fee_share_bps > 0 and not protocol_fee_recipient_pubkey:
        raise ValueError("protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0")
    # Sort intents deterministically
    # For swaps: sort by effective limit price (best first)
    # For liquidity: process in order received
    swap_intents = [i for i in intents if i.kind in (
        IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT
    )]
    liquidity_intents = [i for i in intents if i.kind in (
        IntentKind.ADD_LIQUIDITY, IntentKind.REMOVE_LIQUIDITY
    )]
    
    fills: List[Fill] = []
    current_reserves = (pool_state.reserve0, pool_state.reserve1)
    current_lp_supply = pool_state.lp_supply

    balances_scratch = _copy_balance_table(balances)
    lp_scratch = _copy_lp_table(lp_balances)

    # Optional CoW-style pre-netting pass (EXPERIMENTAL): match opposite-direction
    # exact-in swaps directly between users when both sides' min_out constraints are met.
    #
    # This is *not* a lattice/LLL solver; it is a deterministic, certificate-friendly
    # primitive that can be extended later.
    post_swap_ordering = swap_ordering
    if swap_ordering == _SWAP_ORDERING_COW_PAIR_NETTING_V1:
        netted_fills, remaining_swaps = _cow_pair_netting_exact_in_v1(
            swap_intents,
            pool_state=pool_state,
            balances=balances_scratch,
        )
        fills.extend(netted_fills)
        swap_intents = remaining_swaps
        # After netting, clear the remainder using AB-optimal bounded when possible.
        post_swap_ordering = (
            _SWAP_ORDERING_OPTIMAL_AB_BOUNDED
            if len(swap_intents) <= _MAX_SWAP_ORDERING_BRUTE_FORCE_N
            else _SWAP_ORDERING_GREEDY_AB_REFINED
        )

    # Process swap intents first.
    if post_swap_ordering == _SWAP_ORDERING_OPTIMAL_AB_BOUNDED:
        sorted_swaps = _order_swaps_optimal_ab_bounded(
            swap_intents,
            pool_state=pool_state,
            balances=balances_scratch,
            reserves=current_reserves,
        )
    elif post_swap_ordering == _SWAP_ORDERING_GREEDY_AB:
        sorted_swaps = _order_swaps_greedy_ab(
            swap_intents,
            pool_state=pool_state,
            reserves=current_reserves,
        )
    elif post_swap_ordering == _SWAP_ORDERING_GREEDY_AB_REFINED:
        greedy = _order_swaps_greedy_ab(
            swap_intents,
            pool_state=pool_state,
            reserves=current_reserves,
        )
        sorted_swaps = _refine_b_ordering(
            greedy,
            pool_state=pool_state,
            reserves=current_reserves,
        )
    elif post_swap_ordering == _SWAP_ORDERING_GREEDY_AB_GLOBAL:
        greedy = _order_swaps_greedy_ab(
            swap_intents,
            pool_state=pool_state,
            reserves=current_reserves,
        )
        refined = _refine_b_ordering(
            greedy,
            pool_state=pool_state,
            reserves=current_reserves,
        )
        sorted_swaps = _refine_ab_ordering_global(
            refined,
            pool_state=pool_state,
            reserves=current_reserves,
        )
    elif post_swap_ordering == _SWAP_ORDERING_MCI_AB_GLOBAL:
        mci = _order_swaps_mci_ab(
            swap_intents,
            pool_state=pool_state,
            reserves=current_reserves,
        )
        sorted_swaps = _refine_ab_ordering_global(
            mci,
            pool_state=pool_state,
            reserves=current_reserves,
        )
    else:
        sorted_swaps = _order_swaps_limit_price(swap_intents)
    
    for intent in sorted_swaps:
        fill = _process_swap_intent(
            intent,
            current_reserves,
            pool_state,
            balances_scratch,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )
        fills.append(fill)
        
        if fill.action == FillAction.FILL:
            current_reserves = _reserves_after_swap_fill(
                intent,
                fill,
                pool_state,
                current_reserves,
                protocol_fee_share_bps=protocol_fee_share_bps,
            )
            _apply_swap_fill_to_scratch_balances(
                intent,
                fill,
                balances_scratch,
                protocol_fee_recipient_pubkey,
            )
    
    # Process liquidity intents (in order received)
    for intent in liquidity_intents:
        snap_pool = replace(
            pool_state,
            reserve0=current_reserves[0],
            reserve1=current_reserves[1],
            lp_supply=current_lp_supply,
        )
        fill = _process_liquidity_intent(intent, snap_pool, lp_scratch, balances_scratch)
        fills.append(fill)

        if fill.action == FillAction.FILL:
            if intent.kind == IntentKind.ADD_LIQUIDITY:
                current_reserves = (
                    current_reserves[0] + (fill.amount0_used or 0),
                    current_reserves[1] + (fill.amount1_used or 0),
                )
                current_lp_supply = current_lp_supply + (fill.lp_minted or 0)

                recipient = intent.get_field("recipient", intent.sender_pubkey)
                balances_scratch.subtract(intent.sender_pubkey, snap_pool.asset0, fill.amount0_used or 0)
                balances_scratch.subtract(intent.sender_pubkey, snap_pool.asset1, fill.amount1_used or 0)
                lp_scratch.add(recipient, snap_pool.pool_id, fill.lp_minted or 0)
            else:  # REMOVE_LIQUIDITY
                current_reserves = (
                    current_reserves[0] - (fill.amount0_out or 0),
                    current_reserves[1] - (fill.amount1_out or 0),
                )
                current_lp_supply = current_lp_supply - (fill.lp_burned or 0)

                recipient = intent.get_field("recipient", intent.sender_pubkey)
                lp_scratch.subtract(intent.sender_pubkey, snap_pool.pool_id, fill.lp_burned or 0)
                balances_scratch.add(recipient, snap_pool.asset0, fill.amount0_out or 0)
                balances_scratch.add(recipient, snap_pool.asset1, fill.amount1_out or 0)
    
    return fills


def _order_swaps_limit_price(intents: List[Intent]) -> List[Intent]:
    return sorted(
        intents,
        key=lambda i: (
            -_get_limit_price(i),  # Best price first (descending)
            i.intent_id,  # Tie-break by intent_id
        ),
    )


def _order_swaps_optimal_ab_bounded(
    intents: List[Intent],
    *,
    pool_state: PoolState,
    balances: BalanceTable,
    reserves: Tuple[Amount, Amount],
) -> List[Intent]:
    """
    Choose a deterministic swap order that maximizes the (A,B)+tie-break key:

      A = total executed input volume (sum(amount_in_filled))
      B = total surplus (sum(amount_out_filled - min_amount_out)) for exact-in swaps
      tie-break = lexicographically smallest tuple(intent_id, ...)

    Uses brute-force search only in bounded regimes and otherwise falls back to
    the standard limit-price ordering.

    To keep the objective meaningful, AB optimization is only attempted when all
    swaps share the same direction (same asset_in/out). Mixed-direction batches
    fall back to limit-price ordering.
    """
    if len(intents) <= 1:
        return list(intents)
    if len(intents) > _MAX_SWAP_ORDERING_BRUTE_FORCE_N:
        return _order_swaps_limit_price(intents)

    first_asset_in = intents[0].get_field("asset_in")
    first_asset_out = intents[0].get_field("asset_out")
    if not isinstance(first_asset_in, str) or not isinstance(first_asset_out, str):
        return _order_swaps_limit_price(intents)
    if first_asset_in == first_asset_out:
        return _order_swaps_limit_price(intents)

    if not (
        (first_asset_in == pool_state.asset0 and first_asset_out == pool_state.asset1)
        or (first_asset_in == pool_state.asset1 and first_asset_out == pool_state.asset0)
    ):
        return _order_swaps_limit_price(intents)

    for it in intents[1:]:
        asset_in = it.get_field("asset_in")
        asset_out = it.get_field("asset_out")
        if asset_in != first_asset_in or asset_out != first_asset_out:
            return _order_swaps_limit_price(intents)

    if first_asset_in == pool_state.asset0:
        r_in0 = int(reserves[0])
        r_out0 = int(reserves[1])
    else:
        r_in0 = int(reserves[1])
        r_out0 = int(reserves[0])

    sender_bal_in: Dict[PubKey, Amount] = {}
    for it in intents:
        sender_bal_in[it.sender_pubkey] = balances.get(it.sender_pubkey, first_asset_in)

    def _objective_for_order(order: Tuple[Intent, ...]) -> Tuple[int, int, Tuple[str, ...]]:
        r_in = r_in0
        r_out = r_out0
        bal_in = dict(sender_bal_in)
        A = 0
        B = 0
        for it in order:
            sender = it.sender_pubkey

            if it.kind == IntentKind.SWAP_EXACT_IN:
                amount_in = it.get_field("amount_in")
                min_amount_out = it.get_field("min_amount_out", 0)
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    continue
                if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool) or min_amount_out < 0:
                    continue
                if bal_in.get(sender, 0) < amount_in:
                    continue
                try:
                    if pool_state.curve_tag == CURVE_TAG_CPMM:
                        quote = quote_cpmm_swap_exact_in(
                            reserve_in=r_in,
                            reserve_out=r_out,
                            amount_in=amount_in,
                            fee_bps=pool_state.fee_bps,
                        )
                        amount_out = quote.amount_out
                        new_r_in, new_r_out = quote.reserve_in_after, quote.reserve_out_after
                    else:
                        amount_out, (new_r_in, new_r_out) = swap_exact_in_for_pool(
                            pool_state,
                            reserve_in=r_in,
                            reserve_out=r_out,
                            amount_in=amount_in,
                        )
                except ValueError:
                    continue
                if amount_out < min_amount_out:
                    continue

                A += int(amount_in)
                B += int(amount_out) - int(min_amount_out)
                bal_in[sender] = int(bal_in.get(sender, 0) - amount_in)
                r_in, r_out = int(new_r_in), int(new_r_out)
                continue

            if it.kind == IntentKind.SWAP_EXACT_OUT:
                amount_out = it.get_field("amount_out")
                max_amount_in = it.get_field("max_amount_in")
                if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
                    continue
                if not isinstance(max_amount_in, int) or isinstance(max_amount_in, bool) or max_amount_in < 0:
                    continue
                try:
                    if pool_state.curve_tag == CURVE_TAG_CPMM:
                        quote = quote_cpmm_swap_exact_out(
                            reserve_in=r_in,
                            reserve_out=r_out,
                            amount_out=amount_out,
                            fee_bps=pool_state.fee_bps,
                        )
                        amount_in = quote.amount_in
                        new_r_in, new_r_out = quote.reserve_in_after, quote.reserve_out_after
                    else:
                        amount_in, (new_r_in, new_r_out) = swap_exact_out_for_pool(
                            pool_state,
                            reserve_in=r_in,
                            reserve_out=r_out,
                            amount_out=amount_out,
                        )
                except ValueError:
                    continue
                if amount_in > max_amount_in:
                    continue
                if bal_in.get(sender, 0) < amount_in:
                    continue

                A += int(amount_in)
                bal_in[sender] = int(bal_in.get(sender, 0) - amount_in)
                r_in, r_out = int(new_r_in), int(new_r_out)
                continue

        order_ids = tuple(it.intent_id for it in order)
        return int(A), int(B), order_ids

    best_A = -1
    best_B = -1
    best_order_ids: Tuple[str, ...] | None = None
    best_order: Tuple[Intent, ...] | None = None

    for perm in itertools.permutations(intents):
        cand_key = _ab_ordering_key(A_B_order=_objective_for_order(perm))
        if best_order is None or _is_better_ab_key(cand_key, (best_A, best_B, best_order_ids or tuple())):
            best_A, best_B, best_order_ids, best_order = cand_key[0], cand_key[1], cand_key[2], perm

    return list(best_order) if best_order is not None else _order_swaps_limit_price(intents)


def _get_limit_price(intent: Intent) -> int:
    """
    Get effective limit price for sorting.
    
    For SWAP_EXACT_IN: min_amount_out / amount_in (higher is better)
    For SWAP_EXACT_OUT: amount_out / max_amount_in (higher is better)
    """
    if intent.kind == IntentKind.SWAP_EXACT_IN:
        amount_in = intent.get_field("amount_in", 1)
        min_amount_out = intent.get_field("min_amount_out", 0)
        return (min_amount_out * 10**18) // amount_in if amount_in > 0 else 0
    elif intent.kind == IntentKind.SWAP_EXACT_OUT:
        amount_out = intent.get_field("amount_out", 1)
        max_amount_in = intent.get_field("max_amount_in", 10**18)
        return (amount_out * 10**18) // max_amount_in if max_amount_in > 0 else 0
    return 0


def _process_swap_intent(
    intent: Intent,
    reserves: Tuple[Amount, Amount],
    pool_state: PoolState,
    balances: BalanceTable,
    *,
    protocol_fee_share_bps: int = 0,
) -> Fill:
    """Process a single swap intent against a pool snapshot."""
    reserve0, reserve1 = reserves

    def _reject(reason: str) -> Fill:
        return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason=reason)

    sender = intent.sender_pubkey

    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(asset_in, str) or not isinstance(asset_out, str):
        return _reject("MISSING_PARAMS")
    if asset_in == asset_out:
        return _reject("INVALID_ASSET_PAIR")

    # Validate that (asset_in, asset_out) is exactly the pool pair.
    if asset_in == pool_state.asset0 and asset_out == pool_state.asset1:
        reserve_in, reserve_out = reserve0, reserve1
    elif asset_in == pool_state.asset1 and asset_out == pool_state.asset0:
        reserve_in, reserve_out = reserve1, reserve0
    else:
        return _reject("ASSET_NOT_IN_POOL")

    try:
        if intent.kind == IntentKind.SWAP_EXACT_IN:
            amount_in = intent.get_field("amount_in")
            min_amount_out = intent.get_field("min_amount_out", 0)
            if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                return _reject("MISSING_PARAMS")
            if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool) or min_amount_out < 0:
                return _reject("MISSING_PARAMS")

            if balances.get(sender, asset_in) < amount_in:
                return _reject("INSUFFICIENT_BALANCE")

            if pool_state.curve_tag == CURVE_TAG_CPMM:
                quote = quote_cpmm_swap_exact_in(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_in=amount_in,
                    fee_bps=pool_state.fee_bps,
                    protocol_fee_share_bps=protocol_fee_share_bps,
                )
                amount_out = quote.amount_out
                fee = quote.fee_paid
                protocol_fee = quote.protocol_fee_paid
            else:
                if protocol_fee_share_bps:
                    return _reject("PROTOCOL_FEE_UNSUPPORTED_CURVE")
                amount_out, _new_reserves = swap_exact_in_for_pool(
                    pool_state,
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_in=amount_in,
                )
                fee = compute_fee_total(amount_in, pool_state.fee_bps)
                protocol_fee = 0
            
            # Check slippage constraint
            if amount_out < min_amount_out:
                return _reject("SLIPPAGE")
            return Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                amount_in_filled=amount_in,
                amount_out_filled=amount_out,
                fee_paid=fee,
                protocol_fee_paid=protocol_fee,
                reserve_in_before=int(reserve_in),
                reserve_out_before=int(reserve_out),
            )
        
        elif intent.kind == IntentKind.SWAP_EXACT_OUT:
            amount_out = intent.get_field("amount_out")
            max_amount_in = intent.get_field("max_amount_in")
            if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
                return _reject("MISSING_PARAMS")
            if not isinstance(max_amount_in, int) or isinstance(max_amount_in, bool) or max_amount_in < 0:
                return _reject("MISSING_PARAMS")

            if pool_state.curve_tag == CURVE_TAG_CPMM:
                quote = quote_cpmm_swap_exact_out(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_out=amount_out,
                    fee_bps=pool_state.fee_bps,
                    protocol_fee_share_bps=protocol_fee_share_bps,
                )
                amount_in = quote.amount_in
                fee = quote.fee_paid
                protocol_fee = quote.protocol_fee_paid
            else:
                if protocol_fee_share_bps:
                    return _reject("PROTOCOL_FEE_UNSUPPORTED_CURVE")
                amount_in, _new_reserves = swap_exact_out_for_pool(
                    pool_state,
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_out=amount_out,
                )
                fee = compute_fee_total(amount_in, pool_state.fee_bps)
                protocol_fee = 0

            if balances.get(sender, asset_in) < amount_in:
                return _reject("INSUFFICIENT_BALANCE")
            
            # Check slippage constraint
            if amount_in > max_amount_in:
                return _reject("SLIPPAGE")
            return Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                amount_in_filled=amount_in,
                amount_out_filled=amount_out,
                fee_paid=fee,
                protocol_fee_paid=protocol_fee,
                reserve_in_before=int(reserve_in),
                reserve_out_before=int(reserve_out),
            )
    
    except (ValueError, ZeroDivisionError) as e:
        return _reject(f"COMPUTATION_ERROR: {str(e)}")
    
    return _reject("UNKNOWN_INTENT_TYPE")


@dataclass(frozen=True)
class _CowCandidateExactIn:
    intent: Intent
    amount_in: int
    min_amount_out: int
    sender: PubKey
    recipient: PubKey
    asset_in: AssetId
    asset_out: AssetId


def _cow_pair_netting_exact_in_v1(
    swap_intents: List[Intent],
    *,
    pool_state: PoolState,
    balances: BalanceTable,
) -> tuple[List[Fill], List[Intent]]:
    """Try to net opposite-direction exact-in swaps directly between users.

    A pair (a: asset0->asset1, b: asset1->asset0) is matchable if:
    - b.amount_in >= a.min_amount_out
    - a.amount_in >= b.min_amount_out
    - aggregate per-sender debits are feasible on the pre-netting balances snapshot

    Outputs for a matched pair:
    - a.amount_out_filled = b.amount_in
    - b.amount_out_filled = a.amount_in
    - fee_paid = 0, reason = "COW_NETTED"

    This is an experimental, certificate-friendly primitive; it is *not* intended
    to be AB-optimal globally.
    """
    a0 = pool_state.asset0
    a1 = pool_state.asset1

    side_01: List[_CowCandidateExactIn] = []
    side_10: List[_CowCandidateExactIn] = []
    remaining: List[Intent] = []

    for it in swap_intents:
        if it.kind != IntentKind.SWAP_EXACT_IN:
            remaining.append(it)
            continue
        asset_in = it.get_field("asset_in")
        asset_out = it.get_field("asset_out")
        amount_in = it.get_field("amount_in")
        min_out = it.get_field("min_amount_out", 0)
        if not isinstance(asset_in, str) or not isinstance(asset_out, str):
            remaining.append(it)
            continue
        if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
            remaining.append(it)
            continue
        if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
            remaining.append(it)
            continue

        sender = it.sender_pubkey
        recipient = it.get_field("recipient", sender)
        if not isinstance(recipient, str) or not recipient:
            remaining.append(it)
            continue

        if asset_in == a0 and asset_out == a1:
            side_01.append(
                _CowCandidateExactIn(
                    intent=it,
                    amount_in=int(amount_in),
                    min_amount_out=int(min_out),
                    sender=sender,
                    recipient=recipient,
                    asset_in=a0,
                    asset_out=a1,
                )
            )
        elif asset_in == a1 and asset_out == a0:
            side_10.append(
                _CowCandidateExactIn(
                    intent=it,
                    amount_in=int(amount_in),
                    min_amount_out=int(min_out),
                    sender=sender,
                    recipient=recipient,
                    asset_in=a1,
                    asset_out=a0,
                )
            )
        else:
            remaining.append(it)

    side_01.sort(key=lambda c: c.intent.intent_id)
    side_10.sort(key=lambda c: c.intent.intent_id)

    # Brute-force best matching under a simple (A,B)+lex key, capped for safety.
    brute_cap = 8
    use_bruteforce = len(side_01) + len(side_10) <= brute_cap

    def _pair_feasible(x: _CowCandidateExactIn, y: _CowCandidateExactIn) -> bool:
        return y.amount_in >= x.min_amount_out and x.amount_in >= y.min_amount_out

    best_pairs: List[tuple[_CowCandidateExactIn, _CowCandidateExactIn]] = []
    best_key: tuple[int, int, Tuple[Tuple[str, str], ...]] | None = None

    if use_bruteforce:
        # Track per-sender debit feasibility in the recursion to prune.
        bal0: Dict[PubKey, int] = {}
        bal1: Dict[PubKey, int] = {}
        for c in side_01:
            bal0[c.sender] = int(balances.get(c.sender, a0))
        for c in side_10:
            bal1[c.sender] = int(balances.get(c.sender, a1))

        def rec(
            i: int,
            used_j: set[int],
            deb0: Dict[PubKey, int],
            deb1: Dict[PubKey, int],
            acc: List[tuple[_CowCandidateExactIn, _CowCandidateExactIn]],
        ) -> None:
            nonlocal best_pairs, best_key
            if i >= len(side_01):
                A = sum(int(x.amount_in + y.amount_in) for x, y in acc)
                B = sum(int(y.amount_in - x.min_amount_out + x.amount_in - y.min_amount_out) for x, y in acc)
                pair_ids = tuple(sorted((x.intent.intent_id, y.intent.intent_id) for x, y in acc))
                key = (A, B, pair_ids)
                if best_key is None or key > best_key:
                    best_key = key
                    best_pairs = list(acc)
                return

            # Option: leave side_01[i] unmatched.
            rec(i + 1, used_j, deb0, deb1, acc)

            x = side_01[i]
            # Quick sender balance check for x (aggregate).
            cur_deb0 = int(deb0.get(x.sender, 0))
            if cur_deb0 + x.amount_in > int(bal0.get(x.sender, 0)):
                return

            for j, y in enumerate(side_10):
                if j in used_j:
                    continue
                if not _pair_feasible(x, y):
                    continue
                cur_deb1 = int(deb1.get(y.sender, 0))
                if cur_deb1 + y.amount_in > int(bal1.get(y.sender, 0)):
                    continue

                used_j2 = set(used_j)
                used_j2.add(j)
                deb0_2 = dict(deb0)
                deb1_2 = dict(deb1)
                deb0_2[x.sender] = cur_deb0 + x.amount_in
                deb1_2[y.sender] = cur_deb1 + y.amount_in
                acc.append((x, y))
                rec(i + 1, used_j2, deb0_2, deb1_2, acc)
                acc.pop()

        rec(0, set(), {}, {}, [])
    else:
        # Deterministic greedy fallback (constraint-first).
        # Order by stricter min_out first, then lex id.
        side_01_sorted = sorted(side_01, key=lambda c: (-c.min_amount_out, c.intent.intent_id))
        side_10_pool = list(side_10)
        deb0: Dict[PubKey, int] = defaultdict(int)
        deb1: Dict[PubKey, int] = defaultdict(int)

        for x in side_01_sorted:
            if deb0[x.sender] + x.amount_in > int(balances.get(x.sender, a0)):
                continue
            best_j: int | None = None
            best_y: _CowCandidateExactIn | None = None
            for j, y in enumerate(side_10_pool):
                if not _pair_feasible(x, y):
                    continue
                if deb1[y.sender] + y.amount_in > int(balances.get(y.sender, a1)):
                    continue
                if best_y is None or (y.amount_in, y.intent.intent_id) < (best_y.amount_in, best_y.intent.intent_id):
                    best_j, best_y = j, y
            if best_j is None or best_y is None:
                continue
            deb0[x.sender] += x.amount_in
            deb1[best_y.sender] += best_y.amount_in
            best_pairs.append((x, best_y))
            side_10_pool.pop(best_j)

    matched_ids = {c.intent.intent_id for p in best_pairs for c in p}

    # Apply to balances snapshot atomically: subtract all debits, then add all credits.
    debit_by_sender_asset: Dict[Tuple[PubKey, AssetId], int] = defaultdict(int)
    credit_by_recipient_asset: Dict[Tuple[PubKey, AssetId], int] = defaultdict(int)
    for x, y in best_pairs:
        # x receives y.amount_in of asset1; y receives x.amount_in of asset0
        debit_by_sender_asset[(x.sender, x.asset_in)] += int(x.amount_in)
        debit_by_sender_asset[(y.sender, y.asset_in)] += int(y.amount_in)
        credit_by_recipient_asset[(x.recipient, x.asset_out)] += int(y.amount_in)
        credit_by_recipient_asset[(y.recipient, y.asset_out)] += int(x.amount_in)

    for (sender, asset), amt in debit_by_sender_asset.items():
        if balances.get(sender, asset) < amt:
            # Fail-closed: if balances are insufficient for the aggregate debits, do not mutate
            # the balances snapshot and fall back to "no netting" for this batch.
            swap_intents_sorted = sorted(list(swap_intents), key=lambda it: it.intent_id)
            return [], swap_intents_sorted

    for (sender, asset), amt in debit_by_sender_asset.items():
        balances.subtract(sender, asset, int(amt))
    for (rcpt, asset), amt in credit_by_recipient_asset.items():
        balances.add(rcpt, asset, int(amt))

    fills: List[Fill] = []
    for x, y in best_pairs:
        fills.append(
            Fill(
                intent_id=x.intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=int(x.amount_in),
                amount_out_filled=int(y.amount_in),
                fee_paid=0,
            )
        )
        fills.append(
            Fill(
                intent_id=y.intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=int(y.amount_in),
                amount_out_filled=int(x.amount_in),
                fee_paid=0,
            )
        )

    fills.sort(key=lambda f: f.intent_id)
    remaining.extend([c.intent for c in side_01 if c.intent.intent_id not in matched_ids])
    remaining.extend([c.intent for c in side_10 if c.intent.intent_id not in matched_ids])
    remaining.sort(key=lambda it: it.intent_id)
    return fills, remaining


def _process_liquidity_intent(
    intent: Intent,
    pool_state: PoolState,
    lp_balances: LPTable,
    balances: BalanceTable,
) -> Fill:
    """Process a single liquidity intent against the provided pool snapshot."""
    sender = intent.sender_pubkey

    try:
        if intent.kind == IntentKind.ADD_LIQUIDITY:
            amount0_desired = intent.get_field("amount0_desired")
            amount1_desired = intent.get_field("amount1_desired")
            amount0_min = intent.get_field("amount0_min", 0)
            amount1_min = intent.get_field("amount1_min", 0)

            if any(v is None for v in (amount0_desired, amount1_desired)):
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="MISSING_PARAMS")
            if not (is_strict_int(amount0_desired) and amount0_desired > 0):
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS")
            if not (is_strict_int(amount1_desired) and amount1_desired > 0):
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS")
            if not (is_strict_int(amount0_min) and amount0_min >= 0):
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS")
            if not (is_strict_int(amount1_min) and amount1_min >= 0):
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS")

            amount0_used, amount1_used, lp_minted = add_liquidity(
                pool_state=pool_state,
                amount0_desired=amount0_desired,
                amount1_desired=amount1_desired,
                amount0_min=amount0_min,
                amount1_min=amount1_min,
            )

            if balances.get(sender, pool_state.asset0) < amount0_used:
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INSUFFICIENT_BALANCE")
            if balances.get(sender, pool_state.asset1) < amount1_used:
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INSUFFICIENT_BALANCE")

            return Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                reason="ADD_LIQUIDITY",
                amount0_used=amount0_used,
                amount1_used=amount1_used,
                lp_minted=lp_minted,
            )

        if intent.kind == IntentKind.REMOVE_LIQUIDITY:
            lp_amount = intent.get_field("lp_amount")
            amount0_min = intent.get_field("amount0_min", 0)
            amount1_min = intent.get_field("amount1_min", 0)

            if lp_amount is None:
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="MISSING_PARAMS")
            if not (is_strict_int(lp_amount) and lp_amount > 0):
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS")
            if not (is_strict_int(amount0_min) and amount0_min >= 0):
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS")
            if not (is_strict_int(amount1_min) and amount1_min >= 0):
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS")

            if lp_balances.get(sender, pool_state.pool_id) < lp_amount:
                return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INSUFFICIENT_LP")

            amount0_out, amount1_out = remove_liquidity(
                pool_state=pool_state,
                lp_amount=lp_amount,
                amount0_min=amount0_min,
                amount1_min=amount1_min,
            )

            return Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                reason="REMOVE_LIQUIDITY",
                amount0_out=amount0_out,
                amount1_out=amount1_out,
                lp_burned=lp_amount,
            )

    except (ValueError, TypeError, ZeroDivisionError) as exc:
        return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason=f"COMPUTATION_ERROR: {exc}")

    return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="UNKNOWN_INTENT_TYPE")


def validate_settlement(
    settlement: Settlement,
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable] = None,
) -> Tuple[bool, Optional[str]]:
    """
    Validate a settlement proposal (LEGACY: conservation/non-negativity only).

    WARNING:
    This function does *not* bind the deltas to the user intents or to the swap
    kernels (e.g., it cannot detect "k decreases" / impossible swap fills that
    still conserve assets). Do not use this as an acceptance gate for untrusted
    settlements. Prefer `src/core/settlement_strong_validator.validate_settlement_strong`.
    
    Checks:
    1. All balance deltas result in non-negative balances
    2. All reserve deltas result in non-negative reserves
    3. Asset conservation: Σ_account_deltas + Σ_pool_deltas = 0 (per asset)
    4. LP conservation: Σ_lp_deltas = Σ_lp_mints - Σ_lp_burns
    
    Args:
        settlement: Settlement to validate
        pre_balances: Pre-settlement balances
        pre_pools: Pre-settlement pools
        
    Returns:
        Tuple of (is_valid, error_message)
    """
    # Determine pools created by this settlement (if any).
    created_pools: Dict[str, PoolState] = {}
    if settlement.events:
        for event in settlement.events:
            if event.get("type") != "CREATE_POOL":
                continue
            try:
                pool_id, asset0, asset1, fee_bps, curve_tag, curve_params, status, created_at = (
                    _parse_create_pool_event_payload(event)
                )
            except ValueError as exc:
                return False, str(exc)
            if pool_id in pre_pools:
                return False, f"CREATE_POOL conflicts with existing pool: {pool_id}"
            if pool_id in created_pools:
                return False, f"Duplicate CREATE_POOL event for pool: {pool_id}"
            try:
                created_pools[pool_id] = PoolState(
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
                return False, f"Invalid CREATE_POOL event for pool {pool_id}: {exc}"

    pools_view: Dict[str, PoolState] = {**pre_pools, **created_pools}
    lp_view = pre_lp_balances or LPTable()

    # Aggregate balance deltas per (pubkey, asset) and check non-negativity.
    balance_net: Dict[Tuple[PubKey, AssetId], Amount] = defaultdict(int)
    for balance_delta in settlement.balance_deltas:
        balance_net[(balance_delta.pubkey, balance_delta.asset)] += balance_delta.net_delta()
    for (pubkey, asset), net in balance_net.items():
        current = pre_balances.get(pubkey, asset)
        if current + net < 0:
            return False, f"Negative balance: {pubkey}, {asset}, {current} + {net}"

    # Aggregate reserve deltas per (pool_id, asset) and check non-negativity.
    reserve_net: Dict[Tuple[str, AssetId], Amount] = defaultdict(int)
    for reserve_delta in settlement.reserve_deltas:
        reserve_net[(reserve_delta.pool_id, reserve_delta.asset)] += reserve_delta.net_delta()
    for (pool_id, asset), net in reserve_net.items():
        if pool_id not in pools_view:
            return False, f"Pool not found: {pool_id}"
        pool = pools_view[pool_id]
        try:
            current = pool.get_reserve(asset)
        except ValueError as exc:
            return False, str(exc)
        if current + net < 0:
            return False, f"Negative reserve: {pool_id}, {asset}, {current} + {net}"

    # Aggregate LP deltas per (pubkey, pool_id) and check non-negativity.
    lp_net: Dict[Tuple[PubKey, str], Amount] = defaultdict(int)
    for lp_delta in settlement.lp_deltas:
        lp_net[(lp_delta.pubkey, lp_delta.pool_id)] += lp_delta.net_delta()
    for (pubkey, pool_id), net in lp_net.items():
        current = lp_view.get(pubkey, pool_id)
        if current + net < 0:
            return False, f"Negative LP balance: {pubkey}, {pool_id}, {current} + {net}"

    # Asset conservation (per asset): Σ_account_deltas + Σ_pool_deltas = 0.
    asset_net: Dict[AssetId, Amount] = defaultdict(int)
    for balance_delta in settlement.balance_deltas:
        asset_net[balance_delta.asset] += balance_delta.net_delta()
    for reserve_delta in settlement.reserve_deltas:
        asset_net[reserve_delta.asset] += reserve_delta.net_delta()
    for asset, net in asset_net.items():
        if net != 0:
            return False, f"Asset conservation violation: {asset}, net_delta = {net}"

    # LP supply must remain non-negative; for created pools, supply must be established via lp_deltas.
    supply_net: Dict[str, Amount] = defaultdict(int)
    for lp_delta in settlement.lp_deltas:
        supply_net[lp_delta.pool_id] += lp_delta.net_delta()
    for pool_id, net in supply_net.items():
        if pool_id not in pools_view:
            return False, f"LP delta references unknown pool: {pool_id}"
        start_supply = pre_pools[pool_id].lp_supply if pool_id in pre_pools else 0
        if start_supply + net < 0:
            return False, f"Negative LP supply: {pool_id}, {start_supply} + {net}"

    return True, None


def apply_settlement(
    settlement: Settlement,
    balances: BalanceTable,
    pools: Dict[str, PoolState],
    lp_balances: Optional[LPTable] = None,
) -> None:
    """
    Apply a validated settlement to state.
    
    Modifies balances and pools in place.
    
    Args:
        settlement: Validated settlement
        balances: Balance table to update
        pools: Pool states to update
        
    Raises:
        ValueError: If settlement is invalid
    """
    # Create any pools declared by settlement events.
    if settlement.events:
        for event in settlement.events:
            if event.get("type") != "CREATE_POOL":
                continue
            pool_id, asset0, asset1, fee_bps, curve_tag, curve_params, status, created_at = (
                _parse_create_pool_event_payload(event)
            )
            if pool_id in pools:
                raise ValueError(f"Pool already exists: {pool_id}")

            pools[pool_id] = PoolState(
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

    # Apply balance deltas (order-independent): net per (pubkey, asset).
    balance_net: Dict[Tuple[PubKey, AssetId], Amount] = defaultdict(int)
    for balance_delta in settlement.balance_deltas:
        balance_net[(balance_delta.pubkey, balance_delta.asset)] += balance_delta.net_delta()
    for (pubkey, asset), net in sorted(balance_net.items(), key=lambda t: (t[0][0], t[0][1])):
        if net > 0:
            balances.add(pubkey, asset, net)
        elif net < 0:
            balances.subtract(pubkey, asset, -net)

    # Apply reserve deltas (order-independent): net per (pool_id, asset).
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
            pool.reserve0 = new_reserve
        else:
            # `get_reserve(asset)` above already guarantees membership.
            pool.reserve1 = new_reserve

    # Apply LP deltas (order-independent): net per pool for supply, per (pubkey, pool_id) for balances.
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
        pools[pool_id].lp_supply = new_supply

    if lp_balances is not None:
        for (pubkey, pool_id), net in sorted(lp_net.items(), key=lambda t: (t[0][0], t[0][1])):
            if net > 0:
                lp_balances.add(pubkey, pool_id, net)
            elif net < 0:
                lp_balances.subtract(pubkey, pool_id, -net)


def apply_settlement_pure(
    settlement: Settlement,
    balances: BalanceTable,
    pools: Dict[str, PoolState],
    lp_balances: Optional[LPTable] = None,
) -> tuple[BalanceTable, Dict[str, PoolState], LPTable]:
    """
    Pure variant of `apply_settlement`.

    Returns fresh (balances, pools, lp_balances) copies with the settlement applied.
    """
    balances_copy = _copy_balance_table(balances)
    pools_copy: Dict[str, PoolState] = {pool_id: replace(pool) for pool_id, pool in pools.items()}
    lp_copy = _copy_lp_table(lp_balances) if lp_balances is not None else LPTable()

    apply_settlement(settlement, balances_copy, pools_copy, lp_copy)
    return balances_copy, pools_copy, lp_copy


# ---------------------------------------------------------------------------
# Greedy AB-optimal ordering (WS5)
# ---------------------------------------------------------------------------

def _simulate_swap_reserves(
    intent: Intent,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> Tuple[Amount, Amount, Tuple[Amount, Amount]]:
    """Simulate a single swap and return (A_contrib, B_contrib, new_reserves).

    A = amount_in executed
    B = amount_out - min_amount_out (surplus)

    NOTE: This simulator evaluates AMM executability only (reserves, slippage).
    It does not check user balance sufficiency; a swap ordered by greedy may
    fail during actual execution if a prior swap consumed the user's balance.
    Non-executable swaps are appended in limit-price order by the caller.

    Returns (0, 0, reserves) if swap cannot execute.
    """
    if intent.kind != IntentKind.SWAP_EXACT_IN:
        return 0, 0, reserves

    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    reserve0, reserve1 = reserves

    if asset_in == pool_state.asset0 and asset_out == pool_state.asset1:
        reserve_in, reserve_out = reserve0, reserve1
    elif asset_in == pool_state.asset1 and asset_out == pool_state.asset0:
        reserve_in, reserve_out = reserve1, reserve0
    else:
        return 0, 0, reserves

    amount_in = intent.get_field("amount_in")
    min_amount_out = intent.get_field("min_amount_out", 0)
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return 0, 0, reserves
    if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool):
        return 0, 0, reserves
    if min_amount_out < 0:
        return 0, 0, reserves

    try:
        if pool_state.curve_tag == CURVE_TAG_CPMM:
            quote = quote_cpmm_swap_exact_in(
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=amount_in,
                fee_bps=pool_state.fee_bps,
            )
            amount_out = quote.amount_out
            new_r_in, new_r_out = quote.reserve_in_after, quote.reserve_out_after
        else:
            amount_out, (new_r_in, new_r_out) = swap_exact_in_for_pool(
                pool_state,
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=amount_in,
            )
    except ValueError:
        return 0, 0, reserves

    if amount_out < min_amount_out:
        return 0, 0, reserves

    surplus = amount_out - min_amount_out

    # Reconstruct full reserves tuple
    if asset_in == pool_state.asset0:
        new_reserves = (new_r_in, new_r_out)
    else:
        new_reserves = (new_r_out, new_r_in)

    return amount_in, surplus, new_reserves


def _eval_ordering_ab(
    ordering: List[Intent],
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> Tuple[Amount, Amount]:
    """Simulate an ordering and return total (A, B) achieved."""
    total_a: Amount = 0
    total_b: Amount = 0
    current_reserves = reserves
    for intent in ordering:
        a, b, new_r = _simulate_swap_reserves(intent, pool_state, current_reserves)
        if a > 0:
            total_a += a
            total_b += b
            current_reserves = new_r
    return total_a, total_b


def _ab_ordering_key(
    ordering: List[Intent] | None = None,
    pool_state: PoolState | None = None,
    reserves: Tuple[Amount, Amount] | None = None,
    *,
    A_B_order: Tuple[Amount, Amount, Tuple[str, ...]] | None = None,
) -> Tuple[int, int, Tuple[str, ...]]:
    if A_B_order is not None:
        return int(A_B_order[0]), int(A_B_order[1]), tuple(str(x) for x in A_B_order[2])
    if ordering is None or pool_state is None or reserves is None:
        raise ValueError("ordering, pool_state, and reserves are required unless A_B_order is provided")
    A, B = _eval_ordering_ab(ordering, pool_state, reserves)
    return int(A), int(B), tuple(it.intent_id for it in ordering)


def _is_better_ab_key(candidate: Tuple[int, int, Tuple[str, ...]], best: Tuple[int, int, Tuple[str, ...]]) -> bool:
    cand_a, cand_b, cand_ids = candidate
    best_a, best_b, best_ids = best
    if cand_a > best_a:
        return True
    if cand_a < best_a:
        return False
    if cand_b > best_b:
        return True
    if cand_b < best_b:
        return False
    return cand_ids < best_ids


def _greedy_marginal_ab(
    remaining: List[Intent],
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> Tuple[int, Amount, Amount, Tuple[Amount, Amount]]:
    """Find the swap with tightest slippage that is still executable.

    Prefers swaps with the lowest absolute surplus (amount_out - min_amount_out)
    so that slippage-sensitive swaps execute while reserves are favorable.
    Ties broken by (amount_in desc, intent_id asc) for determinism.

    Returns (best_index, best_a, best_b, new_reserves).
    Returns (-1, 0, 0, reserves) if no swap can execute.
    """
    best_idx = -1
    best_a: Amount = 0
    best_b: Amount = 0
    best_id: str = ""
    best_tightness: int = -1  # surplus; lower = tighter
    best_new_reserves = reserves

    for i, intent in enumerate(remaining):
        a, b, new_r = _simulate_swap_reserves(intent, pool_state, reserves)
        if a == 0:
            continue
        iid = intent.intent_id
        # Tightest first: lowest absolute surplus (b), then highest A, then lowest id.
        is_better = False
        if best_idx == -1:
            is_better = True
        elif b < best_tightness:
            is_better = True
        elif b == best_tightness:
            if a > best_a:
                is_better = True
            elif a == best_a and iid < best_id:
                is_better = True

        if is_better:
            best_idx = i
            best_a = a
            best_b = b
            best_id = iid
            best_tightness = b
            best_new_reserves = new_r

    return best_idx, best_a, best_b, best_new_reserves


def _order_swaps_greedy_ab(
    intents: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> List[Intent]:
    """Greedy O(n^2) swap ordering that approximates AB-optimal.

    At each step, picks the swap with tightest slippage (lowest surplus)
    so slippage-sensitive swaps execute while reserves are favorable.
    Falls back to limit_price for mixed-direction batches.

    Reserve-level guarantee: the returned ordering has (A, B) >= limit_price
    ordering when evaluated against pool reserves only (SWAP_EXACT_IN).
    If the greedy ordering is worse, limit_price ordering is returned instead.

    Limitation: this ordering does not model sender balance constraints.
    A swap ordered first by greedy may consume a shared sender's balance,
    causing a later swap to be rejected at execution time. The caller
    (clear_batch_single_pool) handles such rejections via its own
    balance-checking loop.
    """
    if len(intents) <= 1:
        return list(intents)

    # Check all same direction
    first_asset_in = intents[0].get_field("asset_in")
    first_asset_out = intents[0].get_field("asset_out")
    for it in intents[1:]:
        if it.get_field("asset_in") != first_asset_in or it.get_field("asset_out") != first_asset_out:
            return _order_swaps_limit_price(intents)

    remaining = list(intents)
    greedy_ordered: List[Intent] = []
    current_reserves = reserves

    while remaining:
        idx, a, b, new_r = _greedy_marginal_ab(remaining, pool_state, current_reserves)
        if idx == -1:
            # No more executable swaps; append rest in limit-price order
            greedy_ordered.extend(_order_swaps_limit_price(remaining))
            break
        greedy_ordered.append(remaining.pop(idx))
        current_reserves = new_r

    # Guarantee: greedy >= limit_price. Compare and take the better.
    limit_ordered = _order_swaps_limit_price(intents)
    greedy_ab = _eval_ordering_ab(greedy_ordered, pool_state, reserves)
    limit_ab = _eval_ordering_ab(limit_ordered, pool_state, reserves)

    if greedy_ab >= limit_ab:
        return greedy_ordered
    return limit_ordered


def _order_swaps_mci_ab(
    intents: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> List[Intent]:
    """Marginal-contribution insertion seed for AB ordering.

    Build the ordering incrementally by trying every remaining intent at every
    insertion position and selecting the candidate with the best full `(A, B,
    lex-order)` key. This is an experimental, bounded heuristic intended to
    seed the existing global refinement pass with a stronger starting point
    than the slippage-first greedy order.
    """
    if len(intents) <= 1:
        return list(intents)
    if len(intents) > _MAX_SWAP_ORDERING_MCI_N:
        greedy = _order_swaps_greedy_ab(intents, pool_state=pool_state, reserves=reserves)
        return _refine_b_ordering(greedy, pool_state=pool_state, reserves=reserves)

    first_asset_in = intents[0].get_field("asset_in")
    first_asset_out = intents[0].get_field("asset_out")
    if not isinstance(first_asset_in, str) or not isinstance(first_asset_out, str):
        return _order_swaps_limit_price(intents)
    if first_asset_in == first_asset_out:
        return _order_swaps_limit_price(intents)
    if not (
        (first_asset_in == pool_state.asset0 and first_asset_out == pool_state.asset1)
        or (first_asset_in == pool_state.asset1 and first_asset_out == pool_state.asset0)
    ):
        return _order_swaps_limit_price(intents)
    for it in intents[1:]:
        if it.get_field("asset_in") != first_asset_in or it.get_field("asset_out") != first_asset_out:
            return _order_swaps_limit_price(intents)

    remaining = sorted(intents, key=lambda it: it.intent_id)
    ordered: List[Intent] = []

    while remaining:
        best_idx = -1
        best_order: List[Intent] | None = None
        best_key: Tuple[int, int, Tuple[str, ...]] | None = None
        for rem_idx, candidate in enumerate(remaining):
            for pos in range(len(ordered) + 1):
                trial = ordered[:pos] + [candidate] + ordered[pos:]
                trial_key = _ab_ordering_key(trial, pool_state, reserves)
                if best_order is None or _is_better_ab_key(
                    trial_key,
                    best_key if best_key is not None else (-1, -1, tuple()),
                ):
                    best_idx = rem_idx
                    best_order = trial
                    best_key = trial_key
        if best_order is None or best_idx < 0:
            raise RuntimeError("AB ordering search produced no candidate")
        ordered = best_order
        remaining.pop(best_idx)

    return ordered


def _refine_b_ordering(
    ordering: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> List[Intent]:
    """B-refinement pass: improve surplus (B) without decreasing volume (A).

    Takes a greedy-AB ordering and performs repeated adjacent-swap passes.
    For each pair of adjacent intents (i, i+1), if swapping them improves B
    while keeping A equal, the swap is applied. Repeats until a full pass
    produces no improvement (bubble-sort style).

    Complexity: O(n^2) per pass, at most O(n) passes, so O(n^3) worst case.
    In practice converges in 1-2 passes for typical batch sizes.

    This addresses the B-suboptimality of greedy ordering (H-BC-001):
    greedy_ab is A-optimal but B-suboptimal in 39-94% of cases.
    """
    if len(ordering) <= 1:
        return list(ordering)

    result = list(ordering)
    base_a, base_b = _eval_ordering_ab(result, pool_state, reserves)

    improved = True
    while improved:
        improved = False
        for i in range(len(result) - 1):
            # Try swapping adjacent pair (i, i+1)
            result[i], result[i + 1] = result[i + 1], result[i]
            new_a, new_b = _eval_ordering_ab(result, pool_state, reserves)

            if new_a < base_a:
                # A decreased: revert swap
                result[i], result[i + 1] = result[i + 1], result[i]
            elif new_a == base_a and new_b > base_b:
                # A unchanged, B improved: keep the swap
                base_b = new_b
                improved = True
            elif new_a > base_a:
                # A increased (unexpected but beneficial): keep the swap
                base_a = new_a
                base_b = new_b
                improved = True
            else:
                # A unchanged, B not improved: revert swap
                result[i], result[i + 1] = result[i + 1], result[i]

    return result


def _refine_ab_ordering_global(
    ordering: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> List[Intent]:
    """Global pair-swap AB refinement with deterministic tie-breaks.

    Starts from an existing ordering (typically `greedy_ab_refined`) and applies
    improving non-adjacent pair swaps. A candidate swap is accepted only when it
    strictly improves `(A, B)` lexicographically (maximize A first, then B).

    To avoid pathological runtime, for large batches this function falls back to
    adjacent-only refinement.
    """
    n = len(ordering)
    if n <= 1:
        return list(ordering)
    if n > _MAX_SWAP_ORDERING_GLOBAL_REFINE_N:
        return _refine_b_ordering(ordering, pool_state=pool_state, reserves=reserves)

    result = list(ordering)
    base_a, base_b = _eval_ordering_ab(result, pool_state, reserves)

    # Bounded number of passes; each pass applies at most one best-improving swap.
    max_passes = n
    for _ in range(max_passes):
        best_pair: Optional[Tuple[int, int]] = None
        best_a: Amount = base_a
        best_b: Amount = base_b

        for i in range(n - 1):
            for j in range(i + 1, n):
                result[i], result[j] = result[j], result[i]
                cand_a, cand_b = _eval_ordering_ab(result, pool_state, reserves)
                result[i], result[j] = result[j], result[i]

                better = False
                if cand_a > best_a:
                    better = True
                elif cand_a == best_a and cand_b > best_b:
                    better = True

                if not better:
                    continue

                best_pair = (i, j)
                best_a = cand_a
                best_b = cand_b

        if best_pair is None:
            break

        i, j = best_pair
        result[i], result[j] = result[j], result[i]
        base_a, base_b = best_a, best_b

    return result
