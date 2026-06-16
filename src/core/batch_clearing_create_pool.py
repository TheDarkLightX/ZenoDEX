"""Create-pool event and local-state helpers for batch clearing."""

from __future__ import annotations

from typing import Any, Callable, Dict, List, Optional

from ..state.balances import BalanceTable, PubKey
from ..state.intents import Intent
from ..state.lp import LPTable
from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus
from .cpmm import MIN_LP_LOCK
from .domain_limits import DEX_LP_AMOUNT_MAX, is_strict_int
from .settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta

LP_LOCK_PUBKEY: PubKey = "0x" + "00" * 48


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


def _try_create_pool_with_factory(
    intent: Intent,
    pool_states: Dict[str, PoolState],
    balances: BalanceTable,
    *,
    create_pool_fn: Callable[..., tuple[str, PoolState, int]],
) -> tuple[Fill, Optional[str], Optional[PoolState], Optional[str]]:
    """
    Attempt to create a pool from a CREATE_POOL intent.

    The factory is injected by the batch-clearing wrapper so tests and callers
    that patch ``src.core.batch_clearing.create_pool`` still exercise the same
    failure boundary.
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
        pool_id, pool_state, lp_minted = create_pool_fn(
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
    except (TypeError, ValueError, ZeroDivisionError) as exc:
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
        raise RuntimeError("create_pool fill missing required asset or amount fields")

    lp_minted = created_pool.lp_supply - MIN_LP_LOCK

    # Later intents in the same batch must see the pool creation effects.
    balances.subtract(sender, asset0, amount0)
    balances.subtract(sender, asset1, amount1)
    lp_balances.add(sender, pool_id, lp_minted)
    lp_balances.add(LP_LOCK_PUBKEY, pool_id, MIN_LP_LOCK)

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
