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

from dataclasses import replace
from typing import Dict, List, Optional, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from ..state.balances import Amount, BalanceTable, PubKey
from ..state.intents import Intent
from ..state.lp import LPTable
from ..state.pools import PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .batch_clearing_apply import (
    _apply_filled_intent_to_locals_with_context,
    _FilledIntentLocalApplyRequest,
    _FilledIntentLocalContext,
)
from .batch_clearing_apply_settlement import (
    _SettlementApplyFactories,
    apply_settlement_with_factories,
)
from .batch_clearing_compute import (
    _SettlementComputeFactories,
    _SettlementPolicy,
    compute_settlement_with_factories,
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
from .batch_clearing_ordering import (
    _MAX_SWAP_ORDERING_BRUTE_FORCE_N,
    _ab_ordering_key,
    _eval_ordering_ab,
    _get_limit_price,
    _is_better_ab_key,
    _order_swaps_greedy_ab,
    _order_swaps_limit_price,
    _order_swaps_mci_ab,
    _order_swaps_optimal_ab_bounded,
    _refine_ab_ordering_global,
    _refine_b_ordering,
    _simulate_swap_reserves,
)
from .batch_clearing_requests import (
    ClearBatchSinglePoolRequest,
    ComputeSettlementRequest,
    validate_swap_tiebreak_seed,
)
from .batch_clearing_single_pool import (
    _ClearSinglePoolRequest,
    _SinglePoolFactories,
    _SinglePoolOrderingPolicy,
    clear_batch_single_pool_with_factories,
)
from .batch_clearing_swaps import (
    _apply_swap_fill_to_scratch_balances,
    _process_swap_intent_with_factories,
    _reserves_after_swap_fill,
    _SwapIntentFactories,
    _SwapIntentProcessRequest,
    _SwapIntentRuntimeRequest,
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

# Chunk size for settlement delta aggregation (invariant chunking promotion).
_DELTA_AGG_CHUNK_SIZE = 128

# Private ordering aliases are retained for legacy tests and internal callers
# that imported them from this module before the ordering split.
_ORDERING_COMPAT_EXPORTS = (
    _ab_ordering_key,
    _eval_ordering_ab,
    _get_limit_price,
    _is_better_ab_key,
    _simulate_swap_reserves,
)
_DELTA_COMPAT_EXPORTS = (
    _aggregate_balance_deltas_chunked,
    _aggregate_lp_deltas_chunked,
    _aggregate_reserve_deltas_chunked,
)


def compute_settlement(
    intents: List[Intent],
    pools: Dict[str, PoolState],
    balances: BalanceTable,
    lp_balances: Optional[LPTable] = None,
    *,
    swap_ordering: str = _SWAP_ORDERING_GREEDY_AB_REFINED,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
    swap_tiebreak_seed: bytes | None = None,
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
    validate_swap_tiebreak_seed(swap_tiebreak_seed)
    if swap_ordering not in _SWAP_ORDERING_CHOICES:
        raise ValueError(f"unsupported swap_ordering: {swap_ordering!r}")
    if not is_strict_int(protocol_fee_share_bps) or not (0 <= protocol_fee_share_bps <= 10000):
        raise ValueError("protocol_fee_share_bps must be an int in [0, 10000]")
    if protocol_fee_share_bps > 0 and not protocol_fee_recipient_pubkey:
        raise ValueError("protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0")
    return compute_settlement_with_factories(
        intents,
        pools,
        balances,
        lp_balances,
        policy=_SettlementPolicy(
            swap_ordering=swap_ordering,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
            swap_tiebreak_seed=swap_tiebreak_seed,
        ),
        chunk_size=_DELTA_AGG_CHUNK_SIZE,
        factories=_SettlementComputeFactories(
            copy_balance_table_fn=_copy_balance_table,
            copy_lp_table_fn=_copy_lp_table,
            try_create_pool_fn=_try_create_pool,
            apply_create_pool_to_locals_fn=_apply_create_pool_to_locals,
            clear_batch_single_pool_fn=clear_batch_single_pool,
            apply_filled_intent_to_locals_fn=_apply_filled_intent_to_locals,
        ),
    )


def compute_settlement_for_request(request: ComputeSettlementRequest) -> Settlement:
    return compute_settlement(
        request.intents,
        request.pools,
        request.balances,
        request.lp_balances,
        swap_ordering=request.swap_ordering,
        protocol_fee_share_bps=request.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=request.protocol_fee_recipient_pubkey,
        swap_tiebreak_seed=request.swap_tiebreak_seed,
    )


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
    intent: Intent | _FilledIntentLocalApplyRequest,
    fill: Fill | None = None,
    pool_id: str | None = None,
    pool_state: PoolState | None = None,
    balances: BalanceTable | None = None,
    lp_balances: LPTable | None = None,
    balance_deltas: List[BalanceDelta] | None = None,
    reserve_deltas: List[ReserveDelta] | None = None,
    lp_deltas: List[LPDelta] | None = None,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> None:
    if isinstance(intent, _FilledIntentLocalApplyRequest):
        _apply_filled_intent_to_locals_with_context(
            intent.intent,
            intent.fill,
            intent.context,
        )
        return
    if (
        fill is None
        or pool_id is None
        or pool_state is None
        or balances is None
        or lp_balances is None
        or balance_deltas is None
        or reserve_deltas is None
        or lp_deltas is None
    ):
        raise ValueError("fill, pool_id, pool_state, balances, lp_balances, and delta lists are required")
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
    swap_tiebreak_seed: bytes | None = None,
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
        _ClearSinglePoolRequest(
            intents=intents,
            pool_state=pool_state,
            balances=balances,
            lp_balances=lp_balances,
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
            swap_tiebreak_seed=swap_tiebreak_seed,
        )
    )


def clear_batch_single_pool_for_request(request: ClearBatchSinglePoolRequest) -> List[Fill]:
    validate_swap_tiebreak_seed(request.swap_tiebreak_seed)
    return clear_batch_single_pool(
        request.intents,
        request.pool_state,
        request.balances,
        request.lp_balances,
        swap_ordering=request.swap_ordering,
        protocol_fee_share_bps=request.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=request.protocol_fee_recipient_pubkey,
        swap_tiebreak_seed=request.swap_tiebreak_seed,
    )


def _process_swap_intent(
    intent: Intent | _SwapIntentRuntimeRequest,
    reserves: Tuple[Amount, Amount] | None = None,
    pool_state: PoolState | None = None,
    balances: BalanceTable | None = None,
    *,
    protocol_fee_share_bps: int = 0,
) -> Fill:
    if isinstance(intent, _SwapIntentRuntimeRequest):
        request = intent
        intent = request.intent
        reserves = request.reserves
        pool_state = request.pool_state
        balances = request.balances
        protocol_fee_share_bps = request.protocol_fee_share_bps
    if reserves is None or pool_state is None or balances is None:
        raise ValueError("reserves, pool_state, and balances are required")
    return _process_swap_intent_with_factories(
        _SwapIntentProcessRequest(
            intent=intent,
            reserves=reserves,
            pool_state=pool_state,
            balances=balances,
            protocol_fee_share_bps=protocol_fee_share_bps,
            factories=_SwapIntentFactories(
                quote_exact_in_fn=quote_cpmm_swap_exact_in,
                quote_exact_out_fn=quote_cpmm_swap_exact_out,
                swap_exact_in_fn=swap_exact_in_for_pool,
                swap_exact_out_fn=swap_exact_out_for_pool,
            ),
        )
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
