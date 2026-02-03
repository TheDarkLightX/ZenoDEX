"""
Batch clearing algorithm for deterministic settlement.

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
import itertools
from typing import Any, List, Dict, Tuple, Optional
from collections import defaultdict

from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState, PoolStatus
from ..state.balances import BalanceTable, PubKey, AssetId, Amount
from ..state.lp import LPTable
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .cpmm import MIN_LP_LOCK, compute_fee_total
from .liquidity import create_pool, add_liquidity, remove_liquidity
from .settlement import (
    Settlement,
    Fill,
    FillAction,
    BalanceDelta,
    ReserveDelta,
    LPDelta,
)

LP_LOCK_PUBKEY: PubKey = "0x" + "00" * 48

_SWAP_ORDERING_LIMIT_PRICE = "limit_price"
_SWAP_ORDERING_OPTIMAL_AB_BOUNDED = "optimal_ab_bounded"
_SWAP_ORDERING_GREEDY_AB = "greedy_ab"
_SWAP_ORDERING_CHOICES = frozenset({
    _SWAP_ORDERING_LIMIT_PRICE,
    _SWAP_ORDERING_OPTIMAL_AB_BOUNDED,
    _SWAP_ORDERING_GREEDY_AB,
})

# Bounded brute-force safety cap for AB-optimal ordering.
# For N > this limit, greedy_ab should be used instead.
_MAX_SWAP_ORDERING_BRUTE_FORCE_N = 12


def compute_settlement(
    intents: List[Intent],
    pools: Dict[str, PoolState],
    balances: BalanceTable,
    lp_balances: Optional[LPTable] = None,
    *,
    swap_ordering: str = _SWAP_ORDERING_LIMIT_PRICE,
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
    # Work on local copies (functional core / imperative shell).
    pool_states: Dict[str, PoolState] = {pool_id: replace(pool) for pool_id, pool in pools.items()}
    balances_local = _copy_balance_table(balances)
    lp_local = _copy_lp_table(lp_balances) if lp_balances is not None else LPTable()

    events: List[Dict[str, Any]] = []

    # Group intents by pool
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

        assert pool_id is not None and created_pool is not None
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
            )

        pool_states[pool_id] = pool_state
    
    # Process non-pool intents (invalid/malformed)
    for intent in non_pool_intents:
        included_intents.append((intent.intent_id, FillAction.REJECT))
        all_fills.append(Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INVALID_INTENT"))
    
    # Create settlement
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
    return copied


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

    if balances.get(sender, asset0) < amount0 or balances.get(sender, asset1) < amount1:
        return (
            Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="INSUFFICIENT_BALANCE"),
            None,
            None,
            "insufficient balance",
        )

    try:
        pool_id, pool_state, lp_minted = create_pool(
            asset0=asset0,
            asset1=asset1,
            amount0=amount0,
            amount1=amount1,
            fee_bps=fee_bps,
            creator_pubkey=sender,
            created_at=created_at,
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

    assert asset0 is not None and asset1 is not None and amount0 is not None and amount1 is not None

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
) -> None:
    sender = intent.sender_pubkey
    recipient = intent.get_field("recipient", sender)

    if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        asset_in = intent.get_field("asset_in")
        asset_out = intent.get_field("asset_out")
        amount_in = fill.amount_in_filled or 0
        amount_out = fill.amount_out_filled or 0

        balances.subtract(sender, asset_in, amount_in)
        balances.add(recipient, asset_out, amount_out)

        balance_deltas.append(BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=amount_in))
        balance_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=amount_out, delta_sub=0))

        reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_in, delta_add=amount_in, delta_sub=0))
        reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_out, delta_add=0, delta_sub=amount_out))

        if asset_in == pool_state.asset0:
            pool_state.reserve0 += amount_in
            pool_state.reserve1 -= amount_out
        else:
            pool_state.reserve1 += amount_in
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
    swap_ordering: str = _SWAP_ORDERING_LIMIT_PRICE,
) -> List[Fill]:
    """
    Process batch of intents for a single pool.
    
    Deterministic: sort by limit price, process sequentially.
    
    Args:
        intents: List of intents for this pool
        pool_state: Current pool state
        
    Returns:
        List of Fill objects
    """
    if swap_ordering not in _SWAP_ORDERING_CHOICES:
        raise ValueError(f"unsupported swap_ordering: {swap_ordering!r}")
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
    
    # Process swap intents first.
    if swap_ordering == _SWAP_ORDERING_OPTIMAL_AB_BOUNDED:
        sorted_swaps = _order_swaps_optimal_ab_bounded(
            swap_intents,
            pool_state=pool_state,
            balances=balances_scratch,
            reserves=current_reserves,
        )
    elif swap_ordering == _SWAP_ORDERING_GREEDY_AB:
        sorted_swaps = _order_swaps_greedy_ab(
            swap_intents,
            pool_state=pool_state,
            reserves=current_reserves,
        )
    else:
        sorted_swaps = _order_swaps_limit_price(swap_intents)
    
    for intent in sorted_swaps:
        fill = _process_swap_intent(intent, current_reserves, pool_state, balances_scratch)
        fills.append(fill)
        
        if fill.action == FillAction.FILL:
            # Update reserves based on asset mapping
            asset_in = intent.get_field("asset_in")
            if asset_in == pool_state.asset0:
                # Swapping asset0 -> asset1
                if intent.kind == IntentKind.SWAP_EXACT_IN:
                    _, (new_r0, new_r1) = swap_exact_in_for_pool(
                        pool_state,
                        reserve_in=current_reserves[0],
                        reserve_out=current_reserves[1],
                        amount_in=fill.amount_in_filled or 0,
                    )
                else:  # SWAP_EXACT_OUT
                    _, (new_r0, new_r1) = swap_exact_out_for_pool(
                        pool_state,
                        reserve_in=current_reserves[0],
                        reserve_out=current_reserves[1],
                        amount_out=fill.amount_out_filled or 0,
                    )
                current_reserves = (new_r0, new_r1)
            else:  # asset_in == asset1, swapping asset1 -> asset0
                if intent.kind == IntentKind.SWAP_EXACT_IN:
                    _, (new_r1, new_r0) = swap_exact_in_for_pool(
                        pool_state,
                        reserve_in=current_reserves[1],
                        reserve_out=current_reserves[0],
                        amount_in=fill.amount_in_filled or 0,
                    )
                else:  # SWAP_EXACT_OUT
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
        A, B, order_ids = _objective_for_order(perm)
        if best_order is None:
            best_A, best_B, best_order_ids, best_order = A, B, order_ids, perm
            continue

        assert best_order_ids is not None
        if A > best_A or (A == best_A and (B > best_B or (B == best_B and order_ids < best_order_ids))):
            best_A, best_B, best_order_ids, best_order = A, B, order_ids, perm

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
            
            amount_out, _new_reserves = swap_exact_in_for_pool(
                pool_state,
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=amount_in,
            )
            
            # Check slippage constraint
            if amount_out < min_amount_out:
                return _reject("SLIPPAGE")

            fee = compute_fee_total(amount_in, pool_state.fee_bps)
            return Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                amount_in_filled=amount_in,
                amount_out_filled=amount_out,
                fee_paid=fee,
            )
        
        elif intent.kind == IntentKind.SWAP_EXACT_OUT:
            amount_out = intent.get_field("amount_out")
            max_amount_in = intent.get_field("max_amount_in")
            if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
                return _reject("MISSING_PARAMS")
            if not isinstance(max_amount_in, int) or isinstance(max_amount_in, bool) or max_amount_in < 0:
                return _reject("MISSING_PARAMS")
            
            amount_in, _new_reserves = swap_exact_out_for_pool(
                pool_state,
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_out=amount_out,
            )

            if balances.get(sender, asset_in) < amount_in:
                return _reject("INSUFFICIENT_BALANCE")
            
            # Check slippage constraint
            if amount_in > max_amount_in:
                return _reject("SLIPPAGE")

            fee = compute_fee_total(amount_in, pool_state.fee_bps)
            return Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                amount_in_filled=amount_in,
                amount_out_filled=amount_out,
                fee_paid=fee,
            )
    
    except (ValueError, ZeroDivisionError) as e:
        return _reject(f"COMPUTATION_ERROR: {str(e)}")
    
    return _reject("UNKNOWN_INTENT_TYPE")


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

    except (ValueError, ZeroDivisionError) as exc:
        return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason=f"COMPUTATION_ERROR: {exc}")

    return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="UNKNOWN_INTENT_TYPE")


def validate_settlement(
    settlement: Settlement,
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable] = None,
) -> Tuple[bool, Optional[str]]:
    """
    Validate a settlement proposal.
    
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
            pool_id = event.get("pool_id")
            asset0 = event.get("asset0")
            asset1 = event.get("asset1")
            fee_bps = event.get("fee_bps")
            status_str = event.get("status", PoolStatus.ACTIVE.value)
            created_at = event.get("created_at", 0)

            if not isinstance(pool_id, str) or not pool_id:
                return False, "Invalid CREATE_POOL event: missing pool_id"
            if pool_id in pre_pools:
                return False, f"CREATE_POOL conflicts with existing pool: {pool_id}"
            if pool_id in created_pools:
                return False, f"Duplicate CREATE_POOL event for pool: {pool_id}"
            if not isinstance(asset0, str) or not isinstance(asset1, str):
                return False, f"Invalid CREATE_POOL event assets for pool: {pool_id}"
            if not isinstance(fee_bps, int) or isinstance(fee_bps, bool):
                return False, f"Invalid CREATE_POOL fee_bps for pool: {pool_id}"
            if not isinstance(created_at, int) or isinstance(created_at, bool) or created_at < 0:
                return False, f"Invalid CREATE_POOL created_at for pool: {pool_id}"
            try:
                status = PoolStatus(status_str)
            except ValueError:
                return False, f"Invalid CREATE_POOL status for pool: {pool_id}"
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
                )
            except Exception as exc:
                return False, f"Invalid CREATE_POOL event for pool {pool_id}: {exc}"

    pools_view: Dict[str, PoolState] = {**pre_pools, **created_pools}
    lp_view = pre_lp_balances or LPTable()

    # Aggregate balance deltas per (pubkey, asset) and check non-negativity.
    balance_net: Dict[Tuple[PubKey, AssetId], Amount] = defaultdict(int)
    for d in settlement.balance_deltas:
        balance_net[(d.pubkey, d.asset)] += d.net_delta()
    for (pubkey, asset), net in balance_net.items():
        current = pre_balances.get(pubkey, asset)
        if current + net < 0:
            return False, f"Negative balance: {pubkey}, {asset}, {current} + {net}"

    # Aggregate reserve deltas per (pool_id, asset) and check non-negativity.
    reserve_net: Dict[Tuple[str, AssetId], Amount] = defaultdict(int)
    for d in settlement.reserve_deltas:
        reserve_net[(d.pool_id, d.asset)] += d.net_delta()
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
    for d in settlement.lp_deltas:
        lp_net[(d.pubkey, d.pool_id)] += d.net_delta()
    for (pubkey, pool_id), net in lp_net.items():
        current = lp_view.get(pubkey, pool_id)
        if current + net < 0:
            return False, f"Negative LP balance: {pubkey}, {pool_id}, {current} + {net}"

    # Asset conservation (per asset): Σ_account_deltas + Σ_pool_deltas = 0.
    asset_net: Dict[AssetId, Amount] = defaultdict(int)
    for d in settlement.balance_deltas:
        asset_net[d.asset] += d.net_delta()
    for d in settlement.reserve_deltas:
        asset_net[d.asset] += d.net_delta()
    for asset, net in asset_net.items():
        if net != 0:
            return False, f"Asset conservation violation: {asset}, net_delta = {net}"

    # LP supply must remain non-negative; for created pools, supply must be established via lp_deltas.
    supply_net: Dict[str, Amount] = defaultdict(int)
    for d in settlement.lp_deltas:
        supply_net[d.pool_id] += d.net_delta()
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
            pool_id = event.get("pool_id")
            asset0 = event.get("asset0")
            asset1 = event.get("asset1")
            fee_bps = event.get("fee_bps")
            status_str = event.get("status", PoolStatus.ACTIVE.value)
            created_at = event.get("created_at", 0)

            if not isinstance(pool_id, str) or not pool_id:
                raise ValueError("Invalid CREATE_POOL event: missing pool_id")
            if pool_id in pools:
                raise ValueError(f"Pool already exists: {pool_id}")
            if not isinstance(asset0, str) or not isinstance(asset1, str):
                raise ValueError(f"Invalid CREATE_POOL assets for pool: {pool_id}")
            if not isinstance(fee_bps, int) or isinstance(fee_bps, bool):
                raise ValueError(f"Invalid CREATE_POOL fee_bps for pool: {pool_id}")
            if not isinstance(created_at, int) or isinstance(created_at, bool) or created_at < 0:
                raise ValueError(f"Invalid CREATE_POOL created_at for pool: {pool_id}")
            try:
                status = PoolStatus(status_str)
            except ValueError as exc:
                raise ValueError(f"Invalid CREATE_POOL status for pool: {pool_id}") from exc

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
            )

    # Apply balance deltas (order-independent): net per (pubkey, asset).
    balance_net: Dict[Tuple[PubKey, AssetId], Amount] = defaultdict(int)
    for d in settlement.balance_deltas:
        balance_net[(d.pubkey, d.asset)] += d.net_delta()
    for (pubkey, asset), net in sorted(balance_net.items(), key=lambda t: (t[0][0], t[0][1])):
        if net > 0:
            balances.add(pubkey, asset, net)
        elif net < 0:
            balances.subtract(pubkey, asset, -net)

    # Apply reserve deltas (order-independent): net per (pool_id, asset).
    reserve_net: Dict[Tuple[str, AssetId], Amount] = defaultdict(int)
    for d in settlement.reserve_deltas:
        reserve_net[(d.pool_id, d.asset)] += d.net_delta()
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
        elif asset == pool.asset1:
            pool.reserve1 = new_reserve
        else:
            raise ValueError(f"Asset {asset} not in pool {pool_id}")

    # Apply LP deltas (order-independent): net per pool for supply, per (pubkey, pool_id) for balances.
    supply_net: Dict[str, Amount] = defaultdict(int)
    lp_net: Dict[Tuple[PubKey, str], Amount] = defaultdict(int)
    for d in settlement.lp_deltas:
        supply_net[d.pool_id] += d.net_delta()
        lp_net[(d.pubkey, d.pool_id)] += d.net_delta()

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
