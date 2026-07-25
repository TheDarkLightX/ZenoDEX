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
from typing import Any, Dict, List, Literal, Optional, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from ..state.balances import Amount, AssetId, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus, copy_pool_state
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .cpmm import MIN_LP_LOCK, compute_fee_total
from .domain_limits import DEX_LP_AMOUNT_MAX, is_strict_int
from .liquidity import add_liquidity, create_pool, remove_liquidity
from .route_settlement import (
    ROUTE_REJECT_BINDING_MISSING,
    ROUTE_REJECT_INSUFFICIENT_BALANCE,
    ROUTE_REJECT_INVALID_PARAMS,
    RouteBinding,
    is_route_intent_kind,
    replay_route_legs,
    route_totals_violation,
    validate_route_intent_against_binding,
)
from .settlement import (
    BalanceDelta,
    Fill,
    FillAction,
    LPDelta,
    ReserveDelta,
    Settlement,
)

LP_LOCK_PUBKEY: PubKey = "0x" + "00" * 48

_SWAP_ORDERING_LIMIT_PRICE = "limit_price"
_SWAP_ORDERING_OPTIMAL_AB_BOUNDED = "optimal_ab_bounded"
_SWAP_ORDERING_GREEDY_AB = "greedy_ab"
_SWAP_ORDERING_GREEDY_AB_REFINED = "greedy_ab_refined"
_SWAP_ORDERING_GREEDY_AB_GLOBAL = "greedy_ab_global"
_SWAP_ORDERING_MCI_AB_GLOBAL = "mci_ab_global"
_SWAP_ORDERING_COW_PAIR_NETTING_V1 = "cow_pair_netting_v1"
_SWAP_ORDERING_COW_PAIR_NETTING_EXACT_UNCOUPLED_V2 = "cow_pair_netting_exact_uncoupled_v2"
_SWAP_ORDERING_CHOICES = frozenset({
    _SWAP_ORDERING_LIMIT_PRICE,
    _SWAP_ORDERING_OPTIMAL_AB_BOUNDED,
    _SWAP_ORDERING_GREEDY_AB,
    _SWAP_ORDERING_GREEDY_AB_REFINED,
    _SWAP_ORDERING_GREEDY_AB_GLOBAL,
    _SWAP_ORDERING_MCI_AB_GLOBAL,
    _SWAP_ORDERING_COW_PAIR_NETTING_V1,
    _SWAP_ORDERING_COW_PAIR_NETTING_EXACT_UNCOUPLED_V2,
})
_CowPairNettingProfile = Literal["legacy_v1", "exact_uncoupled_v2"]
_COW_PAIR_NETTING_MATCH_LEGACY_V1: _CowPairNettingProfile = "legacy_v1"
_COW_PAIR_NETTING_MATCH_EXACT_UNCOUPLED_V2: _CowPairNettingProfile = "exact_uncoupled_v2"
_COW_PAIR_NETTING_MATCH_CHOICES = frozenset({
    _COW_PAIR_NETTING_MATCH_LEGACY_V1,
    _COW_PAIR_NETTING_MATCH_EXACT_UNCOUPLED_V2,
})

# Bounded brute-force safety cap for AB-optimal ordering.
# For N > this limit, greedy_ab should be used instead.
#
# Guardrail: a one-state-per-subset Held-Karp replacement is not exact for the
# current integer CPMM semantics. Prefixes with the same executed subset can
# leave different reserves because fees and floor/ceil rounding are order
# sensitive. Any polynomial replacement must carry enough terminal state, or
# prove a narrower curve/order contract before replacing the bounded oracle.
_MAX_SWAP_ORDERING_BRUTE_FORCE_N = 12
# Global pair-swap refinement can be expensive; cap intent count for this mode.
_MAX_SWAP_ORDERING_GLOBAL_REFINE_N = 24
# MCI insertion is heavier than greedy seeding; keep it opt-in and bounded.
_MAX_SWAP_ORDERING_MCI_N = 18
# Exact CoW matching is polynomial, but its lex tie-break re-solves the assignment
# problem once per feasible edge. Keep the exact path bounded and preserve the
# existing deterministic greedy fallback for larger valid batches.
_MAX_COW_EXACT_MATCH_TOTAL_CANDIDATES = 32
_MAX_COW_EXACT_MATCH_FEASIBLE_EDGES = 256
# Chunk size for settlement delta aggregation (invariant chunking promotion).
_DELTA_AGG_CHUNK_SIZE = 128


def is_cow_pair_netting_ordering(swap_ordering: str) -> bool:
    """Return true for profiles whose settlements may contain COW_NETTED fills."""
    return str(swap_ordering) in {
        _SWAP_ORDERING_COW_PAIR_NETTING_V1,
        _SWAP_ORDERING_COW_PAIR_NETTING_EXACT_UNCOUPLED_V2,
    }


def compute_settlement(
    intents: List[Intent],
    pools: Dict[str, PoolState],
    balances: BalanceTable,
    lp_balances: Optional[LPTable] = None,
    *,
    swap_ordering: str = _SWAP_ORDERING_GREEDY_AB_REFINED,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
    route_bindings: Optional[Dict[str, RouteBinding]] = None,
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
    pool_states: Dict[str, PoolState] = {
        pool_id: copy_pool_state(pool) for pool_id, pool in pools.items()
    }
    balances_local = _copy_balance_table(balances)
    lp_local = _copy_lp_table(lp_balances) if lp_balances is not None else LPTable()

    events: List[Dict[str, Any]] = []

    # Group intents by pool
    intents_by_pool: Dict[str, List[Intent]] = defaultdict(list)
    create_pool_intents: List[Intent] = []
    route_intents: List[Intent] = []
    non_pool_intents: List[Intent] = []

    for intent in intents:
        if intent.kind == IntentKind.CREATE_POOL:
            create_pool_intents.append(intent)
            continue

        if is_route_intent_kind(intent.kind):
            route_intents.append(intent)
            continue

        pool_id = intent.get_field("pool_id")
        if isinstance(pool_id, str) and pool_id:
            intents_by_pool[pool_id].append(intent)
        else:
            non_pool_intents.append(intent)
    
    # Process each pool's intents
    all_fills: List[Fill] = []
    all_balance_deltas: List[BalanceDelta] = []
    all_reserve_deltas: List[ReserveDelta] = []
    all_lp_deltas: List[LPDelta] = []
    included_intents: List[Tuple[str, FillAction]] = []
    
    # Process CREATE_POOL first so the rest of the batch can reference new pools.
    for intent in sorted(create_pool_intents, key=lambda i: i.intent_id):
        fill, pool_id, created_pool, _err = _try_create_pool(intent, pool_states, balances_local)
        included_intents.append((intent.intent_id, fill.action))
        all_fills.append(fill)

        if fill.action != FillAction.FILL:
            continue

        # Invariant: _try_create_pool returns a FILL only on success, which sets both
        # pool_id and created_pool. Explicit fail-closed check (not `assert`) so it
        # survives `python -O` and any future regression of that contract.
        if pool_id is None or created_pool is None:
            raise AssertionError(
                "internal: _try_create_pool returned FILL without pool_id/created_pool")
        _apply_create_pool_to_locals(
            intent=intent,
            pool_id=pool_id,
            created_pool=created_pool,
            balances=balances_local,
            lp_balances=lp_local,
            balance_deltas=all_balance_deltas,
            reserve_deltas=all_reserve_deltas,
            lp_deltas=all_lp_deltas,
            events=events,
        )

    # Process atomic route intents (snapshot-bound; before per-pool clearing,
    # whose fills would otherwise invalidate the receipt-pinned pool states).
    # Deterministic order: intent_id ascending.
    for intent in sorted(route_intents, key=lambda i: i.intent_id):
        fill = _clear_route_intent_against_locals(
            intent=intent,
            binding=(route_bindings or {}).get(intent.intent_id),
            pool_states=pool_states,
            balances=balances_local,
            balance_deltas=all_balance_deltas,
            reserve_deltas=all_reserve_deltas,
        )
        included_intents.append((intent.intent_id, fill.action))
        all_fills.append(fill)

    # Process pool intents
    for pool_id in sorted(intents_by_pool.keys()):
        pool_intents = intents_by_pool[pool_id]
        if pool_id not in pool_states:
            # Pool doesn't exist - reject all intents
            for intent in pool_intents:
                included_intents.append((intent.intent_id, FillAction.REJECT))
                all_fills.append(Fill(
                    intent_id=intent.intent_id,
                    action=FillAction.REJECT,
                    reason="POOL_NOT_FOUND"
                ))
            continue
        
        pool_state = pool_states[pool_id]
        fills = clear_batch_single_pool(
            pool_intents,
            pool_state,
            balances_local,
            lp_local,
            swap_ordering=swap_ordering,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        )

        for fill in fills:
            all_fills.append(fill)
            included_intents.append((fill.intent_id, fill.action))

            if fill.action != FillAction.FILL:
                continue

            intent = next(i for i in pool_intents if i.intent_id == fill.intent_id)
            _apply_filled_intent_to_locals(
                intent=intent,
                fill=fill,
                pool_id=pool_id,
                pool_state=pool_state,
                balances=balances_local,
                lp_balances=lp_local,
                balance_deltas=all_balance_deltas,
                reserve_deltas=all_reserve_deltas,
                lp_deltas=all_lp_deltas,
                protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
            )

        pool_states[pool_id] = pool_state
    
    # Process non-pool intents (invalid/malformed)
    for intent in non_pool_intents:
        included_intents.append((intent.intent_id, FillAction.REJECT))
        all_fills.append(Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_INTENT"))
    
    # Create settlement
    # Invariant chunking: aggregate deltas in bounded chunks to reduce payload
    # size while preserving semantics.
    all_balance_deltas = _aggregate_balance_deltas_chunked(
        all_balance_deltas, chunk_size=_DELTA_AGG_CHUNK_SIZE
    )
    all_reserve_deltas = _aggregate_reserve_deltas_chunked(
        all_reserve_deltas, chunk_size=_DELTA_AGG_CHUNK_SIZE
    )
    all_lp_deltas = _aggregate_lp_deltas_chunked(
        all_lp_deltas, chunk_size=_DELTA_AGG_CHUNK_SIZE
    )

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",  # Will be set by caller
        included_intents=included_intents,
        fills=all_fills,
        balance_deltas=all_balance_deltas,
        reserve_deltas=all_reserve_deltas,
        lp_deltas=all_lp_deltas,
        events=events or None,
    )
    
    return settlement


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


def _parse_create_pool_event_payload(
    event: dict[str, Any],
) -> tuple[str, str, str, int, str, str, PoolStatus, int]:
    pool_id = event.get("pool_id")
    asset0 = event.get("asset0")
    asset1 = event.get("asset1")
    fee_bps = event.get("fee_bps")
    curve_tag = event.get("curve_tag", CURVE_TAG_CPMM)
    curve_params = event.get("curve_params", "")
    status_str = event.get("status", PoolStatus.ACTIVE.value)
    created_at = event.get("created_at", 0)

    if not isinstance(pool_id, str) or not pool_id:
        raise ValueError("Invalid CREATE_POOL event: missing pool_id")
    if not isinstance(asset0, str) or not isinstance(asset1, str):
        raise ValueError(f"Invalid CREATE_POOL assets for pool: {pool_id}")
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool):
        raise ValueError(f"Invalid CREATE_POOL fee_bps for pool: {pool_id}")
    if not isinstance(curve_tag, str) or not curve_tag:
        raise ValueError(f"Invalid CREATE_POOL curve_tag for pool: {pool_id}")
    if not isinstance(curve_params, str):
        raise ValueError(f"Invalid CREATE_POOL curve_params for pool: {pool_id}")
    if not isinstance(created_at, int) or isinstance(created_at, bool) or created_at < 0:
        raise ValueError(f"Invalid CREATE_POOL created_at for pool: {pool_id}")

    try:
        status = PoolStatus(str(status_str))
    except ValueError as exc:
        raise ValueError(f"Invalid CREATE_POOL status for pool: {pool_id}") from exc

    return pool_id, asset0, asset1, fee_bps, curve_tag, curve_params, status, created_at


def _aggregate_balance_deltas_chunked(
    deltas: List[BalanceDelta], *, chunk_size: int
) -> List[BalanceDelta]:
    global_acc: Dict[Tuple[PubKey, AssetId], Tuple[Amount, Amount]] = {}
    step = max(1, int(chunk_size))
    for i in range(0, len(deltas), step):
        chunk_acc: Dict[Tuple[PubKey, AssetId], Tuple[Amount, Amount]] = {}
        for d in deltas[i : i + step]:
            key = (d.pubkey, d.asset)
            add_prev, sub_prev = chunk_acc.get(key, (0, 0))
            chunk_acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
        for key, (add_chunk, sub_chunk) in chunk_acc.items():
            add_prev, sub_prev = global_acc.get(key, (0, 0))
            global_acc[key] = (int(add_prev) + int(add_chunk), int(sub_prev) + int(sub_chunk))

    out: List[BalanceDelta] = []
    for key in sorted(global_acc.keys()):
        delta_add, delta_sub = global_acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(BalanceDelta(pubkey=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _aggregate_reserve_deltas_chunked(
    deltas: List[ReserveDelta], *, chunk_size: int
) -> List[ReserveDelta]:
    global_acc: Dict[Tuple[str, AssetId], Tuple[Amount, Amount]] = {}
    step = max(1, int(chunk_size))
    for i in range(0, len(deltas), step):
        chunk_acc: Dict[Tuple[str, AssetId], Tuple[Amount, Amount]] = {}
        for d in deltas[i : i + step]:
            key = (d.pool_id, d.asset)
            add_prev, sub_prev = chunk_acc.get(key, (0, 0))
            chunk_acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
        for key, (add_chunk, sub_chunk) in chunk_acc.items():
            add_prev, sub_prev = global_acc.get(key, (0, 0))
            global_acc[key] = (int(add_prev) + int(add_chunk), int(sub_prev) + int(sub_chunk))

    out: List[ReserveDelta] = []
    for key in sorted(global_acc.keys()):
        delta_add, delta_sub = global_acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(ReserveDelta(pool_id=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _aggregate_lp_deltas_chunked(
    deltas: List[LPDelta], *, chunk_size: int
) -> List[LPDelta]:
    global_acc: Dict[Tuple[PubKey, str], Tuple[Amount, Amount]] = {}
    step = max(1, int(chunk_size))
    for i in range(0, len(deltas), step):
        chunk_acc: Dict[Tuple[PubKey, str], Tuple[Amount, Amount]] = {}
        for d in deltas[i : i + step]:
            key = (d.pubkey, d.pool_id)
            add_prev, sub_prev = chunk_acc.get(key, (0, 0))
            chunk_acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
        for key, (add_chunk, sub_chunk) in chunk_acc.items():
            add_prev, sub_prev = global_acc.get(key, (0, 0))
            global_acc[key] = (int(add_prev) + int(add_chunk), int(sub_prev) + int(sub_chunk))

    out: List[LPDelta] = []
    for key in sorted(global_acc.keys()):
        delta_add, delta_sub = global_acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(LPDelta(pubkey=key[0], pool_id=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _try_create_pool(
    intent: Intent,
    pool_states: Dict[str, PoolState],
    balances: BalanceTable,
) -> tuple[Fill, Optional[str], Optional[PoolState], Optional[str]]:
    """
    Attempt to create a pool from a CREATE_POOL intent.

    Returns (fill, pool_id, created_pool_state, error_message).
    """
    sender = intent.sender_pubkey

    asset0 = intent.get_field("asset0")
    asset1 = intent.get_field("asset1")
    fee_bps = intent.get_field("fee_bps")
    amount0 = intent.get_field("amount0")
    amount1 = intent.get_field("amount1")
    created_at = intent.get_field("created_at", 0)
    curve_tag = intent.get_field("curve_tag", None)
    curve_params = intent.get_field("curve_params", None)

    if any(v is None for v in (asset0, asset1, fee_bps, amount0, amount1)):
        return (
            Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="MISSING_PARAMS"),
            None,
            None,
            "missing params",
        )

    if not isinstance(asset0, str) or not isinstance(asset1, str):
        return (
            Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS"),
            None,
            None,
            "asset ids must be strings",
        )
    if not is_strict_int(fee_bps) or not (0 <= fee_bps <= 10000):
        return (
            Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS"),
            None,
            None,
            "fee_bps out of domain",
        )
    if not is_strict_int(amount0) or not (1 <= amount0 <= DEX_LP_AMOUNT_MAX):
        return (
            Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS"),
            None,
            None,
            "amount0 out of domain",
        )
    if not is_strict_int(amount1) or not (1 <= amount1 <= DEX_LP_AMOUNT_MAX):
        return (
            Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS"),
            None,
            None,
            "amount1 out of domain",
        )
    if created_at is not None and (not is_strict_int(created_at) or created_at < 0):
        return (
            Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_PARAMS"),
            None,
            None,
            "created_at out of domain",
        )

    if balances.get(sender, asset0) < amount0 or balances.get(sender, asset1) < amount1:
        return (
            Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INSUFFICIENT_BALANCE"),
            None,
            None,
            "insufficient balance",
        )

    created_at_value = 0 if created_at is None else created_at

    try:
        pool_id, pool_state, lp_minted = create_pool(
            asset0=asset0,
            asset1=asset1,
            amount0=amount0,
            amount1=amount1,
            fee_bps=fee_bps,
            creator_pubkey=sender,
            created_at=created_at_value,
            curve_tag=curve_tag,
            curve_params=curve_params,
        )
    except Exception as exc:
        return (
            Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason=f"COMPUTATION_ERROR: {exc}"),
            None,
            None,
            str(exc),
        )

    if pool_id in pool_states:
        return (
            Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="POOL_ALREADY_EXISTS"),
            None,
            None,
            "pool already exists",
        )

    # Insert so subsequent intents in this batch can reference it.
    pool_states[pool_id] = pool_state

    return (
        Fill(
            intent_id=intent.intent_id,
            action=FillAction.FILL,
            reason="POOL_CREATED",
            amount0_used=amount0,
            amount1_used=amount1,
            lp_minted=lp_minted,
        ),
        pool_id,
        pool_state,
        None,
    )


def _apply_create_pool_to_locals(
    intent: Intent,
    pool_id: str,
    created_pool: PoolState,
    balances: BalanceTable,
    lp_balances: LPTable,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    lp_deltas: List[LPDelta],
    events: List[Dict[str, Any]],
) -> None:
    sender = intent.sender_pubkey
    asset0 = intent.get_field("asset0")
    asset1 = intent.get_field("asset1")
    fee_bps = intent.get_field("fee_bps")
    amount0 = intent.get_field("amount0")
    amount1 = intent.get_field("amount1")
    created_at = intent.get_field("created_at", created_pool.created_at)

    if asset0 is None or asset1 is None or amount0 is None or amount1 is None:
        raise ValueError("CREATE_POOL intent missing required liquidity fields")

    lp_minted = created_pool.lp_supply - MIN_LP_LOCK

    # Apply to local state (so later intents see updated balances/LP).
    balances.subtract(sender, asset0, amount0)
    balances.subtract(sender, asset1, amount1)
    lp_balances.add(sender, pool_id, lp_minted)
    lp_balances.add(LP_LOCK_PUBKEY, pool_id, MIN_LP_LOCK)

    # Emit create event. Apply reserves/supply via deltas for conservation.
    events.append(
        {
            "type": "CREATE_POOL",
            "pool_id": pool_id,
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": fee_bps,
            "curve_tag": created_pool.curve_tag,
            "curve_params": created_pool.curve_params,
            "status": PoolStatus.ACTIVE.value,
            "created_at": created_at,
        }
    )

    balance_deltas.append(BalanceDelta(pubkey=sender, asset=asset0, delta_add=0, delta_sub=amount0))
    balance_deltas.append(BalanceDelta(pubkey=sender, asset=asset1, delta_add=0, delta_sub=amount1))

    reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=amount0, delta_sub=0))
    reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset1, delta_add=amount1, delta_sub=0))

    lp_deltas.append(LPDelta(pubkey=sender, pool_id=pool_id, delta_add=lp_minted, delta_sub=0))
    lp_deltas.append(LPDelta(pubkey=LP_LOCK_PUBKEY, pool_id=pool_id, delta_add=MIN_LP_LOCK, delta_sub=0))


def _clear_route_intent_against_locals(
    *,
    intent: Intent,
    binding: Optional[RouteBinding],
    pool_states: Dict[str, PoolState],
    balances: BalanceTable,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
) -> Fill:
    """
    Clear one atomic route intent against the local candidate state.

    Two-phase (atomic by construction): replay EVERY leg first against the
    current locals (pure, no mutation), then apply all legs only on full
    success. Any failure returns a REJECT fill with a stable reason and the
    locals untouched.
    """

    def _reject(reason: str) -> Fill:
        return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason=reason)

    if binding is None:
        return _reject(ROUTE_REJECT_BINDING_MISSING)

    err = validate_route_intent_against_binding(intent, binding)
    if err is not None:
        return _reject(ROUTE_REJECT_INVALID_PARAMS)

    sender = intent.sender_pubkey
    recipient = intent.get_field("recipient", sender)

    replay = replay_route_legs(binding=binding, pools=pool_states)
    if not replay.ok:
        return _reject(replay.reject_reason or ROUTE_REJECT_INVALID_PARAMS)

    totals_err = route_totals_violation(intent, replay)
    if totals_err is not None:
        return _reject(totals_err)

    if balances.get(sender, binding.asset_in) < int(replay.total_amount_in):
        return _reject(ROUTE_REJECT_INSUFFICIENT_BALANCE)

    # All legs replayed; commit to the locals.
    for leg in replay.legs:
        balances.subtract(sender, leg.asset_in, int(leg.amount_in))
        balances.add(recipient, leg.asset_out, int(leg.amount_out))
        balance_deltas.append(
            BalanceDelta(pubkey=sender, asset=leg.asset_in, delta_add=0, delta_sub=int(leg.amount_in))
        )
        balance_deltas.append(
            BalanceDelta(pubkey=recipient, asset=leg.asset_out, delta_add=int(leg.amount_out), delta_sub=0)
        )
        reserve_deltas.append(
            ReserveDelta(pool_id=leg.pool_id, asset=leg.asset_in, delta_add=int(leg.amount_in), delta_sub=0)
        )
        reserve_deltas.append(
            ReserveDelta(pool_id=leg.pool_id, asset=leg.asset_out, delta_add=0, delta_sub=int(leg.amount_out))
        )
        pool_state = pool_states[leg.pool_id]
        pool_state.reserve0 = int(leg.new_reserve0)
        pool_state.reserve1 = int(leg.new_reserve1)

    return Fill(
        intent_id=intent.intent_id,
        action=FillAction.FILL,
        amount_in_filled=int(replay.total_amount_in),
        amount_out_filled=int(replay.total_amount_out),
        fee_paid=int(replay.total_fee_paid),
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
            protocol_fee_recipient = protocol_fee_recipient_pubkey
            if not protocol_fee_recipient:
                raise ValueError("protocol_fee_recipient_pubkey is required for protocol fee capture")
            balances.add(protocol_fee_recipient, asset_in, protocol_fee)

        balance_deltas.append(BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=amount_in))
        balance_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=amount_out, delta_sub=0))
        if protocol_fee:
            protocol_fee_recipient = protocol_fee_recipient_pubkey
            if not protocol_fee_recipient:
                raise ValueError("protocol_fee_recipient_pubkey is required for protocol fee capture")
            balance_deltas.append(
                BalanceDelta(
                    pubkey=protocol_fee_recipient,
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
    if is_cow_pair_netting_ordering(swap_ordering):
        matching_profile = (
            _COW_PAIR_NETTING_MATCH_EXACT_UNCOUPLED_V2
            if swap_ordering == _SWAP_ORDERING_COW_PAIR_NETTING_EXACT_UNCOUPLED_V2
            else _COW_PAIR_NETTING_MATCH_LEGACY_V1
        )
        netted_fills, remaining_swaps = _cow_pair_netting_exact_in_v1(
            swap_intents,
            pool_state=pool_state,
            balances=balances_scratch,
            matching_profile=matching_profile,
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
            # Update reserves based on asset mapping
            asset_in = intent.get_field("asset_in")
            if asset_in == pool_state.asset0:
                # Swapping asset0 -> asset1
                if intent.kind == IntentKind.SWAP_EXACT_IN:
                    if pool_state.curve_tag == CURVE_TAG_CPMM:
                        quote = quote_cpmm_swap_exact_in(
                            reserve_in=current_reserves[0],
                            reserve_out=current_reserves[1],
                            amount_in=fill.amount_in_filled or 0,
                            fee_bps=pool_state.fee_bps,
                            protocol_fee_share_bps=protocol_fee_share_bps,
                        )
                        new_r0, new_r1 = quote.reserve_in_after, quote.reserve_out_after
                    else:
                        _, (new_r0, new_r1) = swap_exact_in_for_pool(
                            pool_state,
                            reserve_in=current_reserves[0],
                            reserve_out=current_reserves[1],
                            amount_in=fill.amount_in_filled or 0,
                        )
                else:  # SWAP_EXACT_OUT
                    if pool_state.curve_tag == CURVE_TAG_CPMM:
                        quote = quote_cpmm_swap_exact_out(
                            reserve_in=current_reserves[0],
                            reserve_out=current_reserves[1],
                            amount_out=fill.amount_out_filled or 0,
                            fee_bps=pool_state.fee_bps,
                            protocol_fee_share_bps=protocol_fee_share_bps,
                        )
                        new_r0, new_r1 = quote.reserve_in_after, quote.reserve_out_after
                    else:
                        _, (new_r0, new_r1) = swap_exact_out_for_pool(
                            pool_state,
                            reserve_in=current_reserves[0],
                            reserve_out=current_reserves[1],
                            amount_out=fill.amount_out_filled or 0,
                        )
                current_reserves = (new_r0, new_r1)
            else:  # asset_in == asset1, swapping asset1 -> asset0
                if intent.kind == IntentKind.SWAP_EXACT_IN:
                    if pool_state.curve_tag == CURVE_TAG_CPMM:
                        quote = quote_cpmm_swap_exact_in(
                            reserve_in=current_reserves[1],
                            reserve_out=current_reserves[0],
                            amount_in=fill.amount_in_filled or 0,
                            fee_bps=pool_state.fee_bps,
                            protocol_fee_share_bps=protocol_fee_share_bps,
                        )
                        new_r1, new_r0 = quote.reserve_in_after, quote.reserve_out_after
                    else:
                        _, (new_r1, new_r0) = swap_exact_in_for_pool(
                            pool_state,
                            reserve_in=current_reserves[1],
                            reserve_out=current_reserves[0],
                            amount_in=fill.amount_in_filled or 0,
                        )
                else:  # SWAP_EXACT_OUT
                    if pool_state.curve_tag == CURVE_TAG_CPMM:
                        quote = quote_cpmm_swap_exact_out(
                            reserve_in=current_reserves[1],
                            reserve_out=current_reserves[0],
                            amount_out=fill.amount_out_filled or 0,
                            fee_bps=pool_state.fee_bps,
                            protocol_fee_share_bps=protocol_fee_share_bps,
                        )
                        new_r1, new_r0 = quote.reserve_in_after, quote.reserve_out_after
                    else:
                        _, (new_r1, new_r0) = swap_exact_out_for_pool(
                            pool_state,
                            reserve_in=current_reserves[1],
                            reserve_out=current_reserves[0],
                            amount_out=fill.amount_out_filled or 0,
                        )
                current_reserves = (new_r0, new_r1)

            # Apply to scratch balances for subsequent intents.
            asset_in = intent.get_field("asset_in")
            asset_out = intent.get_field("asset_out")
            recipient = intent.get_field("recipient", intent.sender_pubkey)
            balances_scratch.subtract(intent.sender_pubkey, asset_in, fill.amount_in_filled or 0)
            balances_scratch.add(recipient, asset_out, fill.amount_out_filled or 0)
            protocol_fee = int(fill.protocol_fee_paid or 0)
            if protocol_fee:
                protocol_fee_recipient = protocol_fee_recipient_pubkey
                if not protocol_fee_recipient:
                    raise ValueError("protocol_fee_recipient_pubkey is required for protocol fee capture")
                balances_scratch.add(protocol_fee_recipient, asset_in, protocol_fee)
    
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
                except Exception:
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
                except Exception:
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


def _cow_feasible(x: "_CowCandidateExactIn", y: "_CowCandidateExactIn") -> bool:
    return y.amount_in >= x.min_amount_out and x.amount_in >= y.min_amount_out


def _cow_pair_ab(x: "_CowCandidateExactIn", y: "_CowCandidateExactIn") -> tuple[int, int]:
    """(A, B) contribution of matching pair (x, y). B >= 0 by feasibility."""
    a = int(x.amount_in + y.amount_in)
    b = int((y.amount_in - x.min_amount_out) + (x.amount_in - y.min_amount_out))
    return a, b


def _cow_max_weight_assignment(w: List[List[int]]) -> List[int]:
    """Max-weight perfect assignment on a square integer matrix, via Kuhn-Munkres on
    negated weights (O(n^3), deterministic). Returns ``match[i] = j``."""
    n = len(w)
    if n == 0:
        return []
    cost = [[-w[i][j] for j in range(n)] for i in range(n)]  # minimize -w  <=>  maximize w
    # INF must exceed any reduced cost the algorithm forms. Python ints are unbounded,
    # so derive it from the actual weights (a fixed 1<<62 overflows for large amounts).
    INF = 1 + sum(abs(cost[i][j]) for i in range(n) for j in range(n))
    u = [0] * (n + 1)
    v = [0] * (n + 1)
    p = [0] * (n + 1)
    way = [0] * (n + 1)
    for i in range(1, n + 1):
        p[0] = i
        j0 = 0
        minv = [INF] * (n + 1)
        used = [False] * (n + 1)
        while True:
            used[j0] = True
            i0 = p[j0]
            delta = INF
            j1 = -1
            for j in range(1, n + 1):
                if not used[j]:
                    cur = cost[i0 - 1][j - 1] - u[i0] - v[j]
                    if cur < minv[j]:
                        minv[j] = cur
                        way[j] = j0
                    if minv[j] < delta:
                        delta = minv[j]
                        j1 = j
            for j in range(n + 1):
                if used[j]:
                    u[p[j]] += delta
                    v[j] -= delta
                else:
                    minv[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while True:
            j1 = way[j0]
            p[j0] = p[j1]
            j0 = j1
            if j0 == 0:
                break
    match = [-1] * n
    for j in range(1, n + 1):
        if p[j] != 0:
            match[p[j] - 1] = j - 1
    return match


def _cow_max_weight_pairs(
    side_01: List["_CowCandidateExactIn"],
    side_10: List["_CowCandidateExactIn"],
    scale: int,
    *,
    forced: set,
    banned: set,
) -> tuple[int, set] | None:
    """Max total ``A*scale + B`` feasible matching that includes ``forced`` and excludes
    ``banned``. Returns ``(weight, pairs)`` or ``None`` if ``forced`` cannot be realized."""
    n0, n1 = len(side_01), len(side_10)
    n = max(n0, n1)
    if n == 0:
        return 0, set()
    # Dynamic sentinels (Python ints are unbounded -> no fixed-width overflow): `big`
    # exceeds any matching's total real weight, so an infeasible/banned cell is never
    # chosen over leaving a row unmatched, and each forced edge's bonus dominates.
    big = 1
    for i in range(n0):
        for j in range(n1):
            if (i, j) not in banned and _cow_feasible(side_01[i], side_10[j]):
                a, b = _cow_pair_ab(side_01[i], side_10[j])
                big += a * scale + b
    w = [[0] * n for _ in range(n)]
    for i in range(n0):
        for j in range(n1):
            if (i, j) in banned or not _cow_feasible(side_01[i], side_10[j]):
                w[i][j] = -big
            else:
                a, b = _cow_pair_ab(side_01[i], side_10[j])
                w[i][j] = a * scale + b
    for (i, j) in forced:
        w[i][j] += big
    match = _cow_max_weight_assignment(w)
    pairs: set = set()
    real = 0
    for i in range(n):
        j = match[i]
        if j < 0 or i >= n0 or j >= n1 or w[i][j] < 0:  # skip dummy / infeasible / banned
            continue
        pairs.add((i, j))
        a, b = _cow_pair_ab(side_01[i], side_10[j])
        real += a * scale + b
    if not forced.issubset(pairs):
        return None
    return real, pairs


def _cow_exact_match_uncoupled(
    side_01: List["_CowCandidateExactIn"],
    side_10: List["_CowCandidateExactIn"],
) -> List[tuple["_CowCandidateExactIn", "_CowCandidateExactIn"]]:
    """Exact ``(A, B, lex-max-of-ascending-pair-ids)`` matching for the uncoupled case,
    in polynomial time. Bit-identical to the capped brute force where they overlap; for
    larger batches it returns the true optimum (which the greedy fallback does not)."""
    scale = 1
    for x in side_01:
        for y in side_10:
            if _cow_feasible(x, y):
                _, b = _cow_pair_ab(x, y)
                scale += max(0, b)
    base = _cow_max_weight_pairs(side_01, side_10, scale, forced=set(), banned=set())
    if base is None or not base[1]:
        return []
    max_w = base[0]
    # lex-max of the ASCENDING-sorted pair-id tuple == maximize the smallest pair, then
    # the next, ...  Greedy: process candidate pairs ascending by (x_id, y_id); BAN each
    # if the optimum is still reachable without it (pushing the min pair up); else force it.
    edges = sorted(
        (
            (side_01[i].intent.intent_id, side_10[j].intent.intent_id, i, j)
            for i in range(len(side_01))
            for j in range(len(side_10))
            if _cow_feasible(side_01[i], side_10[j])
        ),
        key=lambda t: (t[0], t[1]),
    )
    banned: set = set()
    forced: set = set()
    used_i: set = set()
    used_j: set = set()
    for (_xid, _yid, i, j) in edges:
        if (i, j) in banned or i in used_i or j in used_j:
            continue
        res = _cow_max_weight_pairs(side_01, side_10, scale, forced=forced, banned=banned | {(i, j)})
        if res is not None and res[0] == max_w:
            banned = banned | {(i, j)}
        else:
            forced = forced | {(i, j)}
            used_i.add(i)
            used_j.add(j)
    return [
        (side_01[i], side_10[j])
        for (i, j) in sorted(
            forced,
            key=lambda ij: (
                side_01[ij[0]].intent.intent_id,
                side_10[ij[1]].intent.intent_id,
            ),
        )
    ]


def _cow_exact_match_work_within_cap(
    side_01: List["_CowCandidateExactIn"],
    side_10: List["_CowCandidateExactIn"],
) -> bool:
    """Return true when the exact uncoupled matcher is within the local work cap.

    The exact algorithm's objective is useful, but the lex tie-break calls the
    O(n^3) assignment solver once per feasible edge. This cheap precheck keeps
    the core bounded even if a caller bypasses the integration-layer intent cap.
    """
    if len(side_01) + len(side_10) > _MAX_COW_EXACT_MATCH_TOTAL_CANDIDATES:
        return False
    feasible_edges = 0
    for x in side_01:
        for y in side_10:
            if _cow_feasible(x, y):
                feasible_edges += 1
                if feasible_edges > _MAX_COW_EXACT_MATCH_FEASIBLE_EDGES:
                    return False
    return True


def _cow_uncoupled(
    side_01: List["_CowCandidateExactIn"],
    side_10: List["_CowCandidateExactIn"],
    balances: BalanceTable,
    a0: AssetId,
    a1: AssetId,
) -> bool:
    """True when no per-sender balance constraint can bind: for every sender, the sum of
    ALL their candidate debits (on each side) is within their balance. Then the matching
    is an unconstrained max-weight bipartite matching and the exact poly matcher applies."""
    need0: Dict[PubKey, int] = defaultdict(int)
    need1: Dict[PubKey, int] = defaultdict(int)
    for c in side_01:
        need0[c.sender] += int(c.amount_in)
    for c in side_10:
        need1[c.sender] += int(c.amount_in)
    for sender, need in need0.items():
        if need > int(balances.get(sender, a0)):
            return False
    for sender, need in need1.items():
        if need > int(balances.get(sender, a1)):
            return False
    return True


def _cow_pair_netting_exact_in_v1(
    swap_intents: List[Intent],
    *,
    pool_state: PoolState,
    balances: BalanceTable,
    matching_profile: Literal["legacy_v1", "exact_uncoupled_v2"] = _COW_PAIR_NETTING_MATCH_LEGACY_V1,
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
    if matching_profile not in _COW_PAIR_NETTING_MATCH_CHOICES:
        raise ValueError(f"unsupported CoW matching_profile: {matching_profile!r}")

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

    use_exact_uncoupled = (
        matching_profile == _COW_PAIR_NETTING_MATCH_EXACT_UNCOUPLED_V2
        and _cow_exact_match_work_within_cap(side_01, side_10)
        and _cow_uncoupled(side_01, side_10, balances, a0, a1)
    )
    if use_exact_uncoupled:
        # Uncoupled => the per-sender balance constraint cannot bind, so the matching is
        # an unconstrained max-weight bipartite matching. This is a versioned profile:
        # `cow_pair_netting_v1` keeps its legacy greedy fallback for replay stability.
        best_pairs = _cow_exact_match_uncoupled(side_01, side_10)
    elif use_bruteforce:
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
            except Exception as exc:
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
    pools_copy: Dict[str, PoolState] = {
        pool_id: copy_pool_state(pool) for pool_id, pool in pools.items()
    }
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
    except Exception:
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
        raise ValueError("_ab_ordering_key requires ordering, pool_state, and reserves")
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
        # Invariant: `remaining` is non-empty (while guard) so the inner loops run at
        # least once and the first iteration sets best_order/best_idx. Explicit guard
        # (not `assert`) so it survives `python -O`.
        if best_order is None or best_idx < 0:
            raise AssertionError(
                "internal: ab-ordering search left best_order unset on a non-empty set")
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
