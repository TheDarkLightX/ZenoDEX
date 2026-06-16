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

from collections import defaultdict
from dataclasses import dataclass, replace
from typing import Any, Dict, List, Optional, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from ..state.balances import Amount, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .batch_clearing_ab_order import (
    _OptimalAbOrderingFactories,
    _SwapReserveSimulationFactories,
    order_swaps_optimal_ab_bounded_with_factories,
    simulate_swap_reserves_with_factories,
)
from .batch_clearing_apply import (
    _apply_filled_intent_to_locals_with_context,
    _FilledIntentLocalContext,
)
from .batch_clearing_apply_settlement import (
    _SettlementApplyFactories,
    apply_settlement_with_factories,
)
from .batch_clearing_cow import _cow_pair_netting_exact_in_v1
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
from .batch_clearing_liquidity import _process_liquidity_intent_with_factories
from .batch_clearing_single_pool import (
    _SinglePoolFactories,
    _SinglePoolOrderingPolicy,
    clear_batch_single_pool_with_factories,
)
from .batch_clearing_swaps import (
    _apply_swap_fill_to_scratch_balances,
    _process_swap_intent_with_factories,
    _reserves_after_swap_fill,
    _SwapIntentFactories,
)
from .batch_clearing_validate import (
    _SettlementValidationFactories,
    validate_settlement_with_factories,
)
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
    _apply_filled_intent_to_locals_with_context(
        intent,
        fill,
        _FilledIntentLocalContext(
            pool_id=pool_id,
            pool_state=pool_state,
            balances=balances,
            lp_balances=lp_balances,
            balance_deltas=balance_deltas,
            reserve_deltas=reserve_deltas,
            lp_deltas=lp_deltas,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        ),
    )


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
    return clear_batch_single_pool_with_factories(
        intents,
        pool_state,
        balances,
        lp_balances,
        policy=_SinglePoolOrderingPolicy(
            swap_ordering=swap_ordering,
            ordering_choices=_SWAP_ORDERING_CHOICES,
            limit_price=_SWAP_ORDERING_LIMIT_PRICE,
            optimal_ab_bounded=_SWAP_ORDERING_OPTIMAL_AB_BOUNDED,
            greedy_ab=_SWAP_ORDERING_GREEDY_AB,
            greedy_ab_refined=_SWAP_ORDERING_GREEDY_AB_REFINED,
            greedy_ab_global=_SWAP_ORDERING_GREEDY_AB_GLOBAL,
            mci_ab_global=_SWAP_ORDERING_MCI_AB_GLOBAL,
            cow_pair_netting_v1=_SWAP_ORDERING_COW_PAIR_NETTING_V1,
            max_brute_force_n=_MAX_SWAP_ORDERING_BRUTE_FORCE_N,
        ),
        factories=_SinglePoolFactories(
            copy_balance_table_fn=_copy_balance_table,
            copy_lp_table_fn=_copy_lp_table,
            cow_pair_netting_fn=_cow_pair_netting_exact_in_v1,
            order_limit_price_fn=_order_swaps_limit_price,
            order_optimal_ab_bounded_fn=_order_swaps_optimal_ab_bounded,
            order_greedy_ab_fn=_order_swaps_greedy_ab,
            order_mci_ab_fn=_order_swaps_mci_ab,
            refine_b_ordering_fn=_refine_b_ordering,
            refine_ab_ordering_global_fn=_refine_ab_ordering_global,
            process_swap_intent_fn=_process_swap_intent,
            reserves_after_swap_fill_fn=_reserves_after_swap_fill,
            apply_swap_fill_to_scratch_balances_fn=_apply_swap_fill_to_scratch_balances,
            process_liquidity_intent_fn=_process_liquidity_intent,
        ),
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )


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
    return order_swaps_optimal_ab_bounded_with_factories(
        intents,
        pool_state=pool_state,
        balances=balances,
        reserves=reserves,
        max_brute_force_n=_MAX_SWAP_ORDERING_BRUTE_FORCE_N,
        factories=_OptimalAbOrderingFactories(
            quote_exact_in_fn=quote_cpmm_swap_exact_in,
            quote_exact_out_fn=quote_cpmm_swap_exact_out,
            swap_exact_in_fn=swap_exact_in_for_pool,
            swap_exact_out_fn=swap_exact_out_for_pool,
            order_limit_price_fn=_order_swaps_limit_price,
            ab_ordering_key_fn=_ab_ordering_key,
            is_better_ab_key_fn=_is_better_ab_key,
        ),
    )


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
    return _process_swap_intent_with_factories(
        intent,
        reserves,
        pool_state,
        balances,
        protocol_fee_share_bps=protocol_fee_share_bps,
        factories=_SwapIntentFactories(
            quote_exact_in_fn=quote_cpmm_swap_exact_in,
            quote_exact_out_fn=quote_cpmm_swap_exact_out,
            swap_exact_in_fn=swap_exact_in_for_pool,
            swap_exact_out_fn=swap_exact_out_for_pool,
        ),
    )


def _process_liquidity_intent(
    intent: Intent,
    pool_state: PoolState,
    lp_balances: LPTable,
    balances: BalanceTable,
) -> Fill:
    return _process_liquidity_intent_with_factories(
        intent,
        pool_state,
        lp_balances,
        balances,
        add_liquidity_fn=add_liquidity,
        remove_liquidity_fn=remove_liquidity,
    )


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
    return validate_settlement_with_factories(
        settlement,
        pre_balances,
        pre_pools,
        pre_lp_balances,
        _SettlementValidationFactories(
            parse_create_pool_event_payload_fn=_parse_create_pool_event_payload,
            pool_state_fn=PoolState,
        ),
    )


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
    apply_settlement_with_factories(
        settlement,
        balances,
        pools,
        lp_balances,
        _SettlementApplyFactories(
            parse_create_pool_event_payload_fn=_parse_create_pool_event_payload,
            pool_state_fn=PoolState,
        ),
    )


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
    return simulate_swap_reserves_with_factories(
        intent,
        pool_state,
        reserves,
        _SwapReserveSimulationFactories(
            quote_exact_in_fn=quote_cpmm_swap_exact_in,
            swap_exact_in_fn=swap_exact_in_for_pool,
        ),
    )


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
