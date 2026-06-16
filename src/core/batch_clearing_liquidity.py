"""Liquidity intent admission helper for batch clearing."""

from __future__ import annotations

from typing import Callable

from ..state.balances import BalanceTable
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import PoolState
from .domain_limits import is_strict_int
from .settlement import Fill, FillAction


def _process_liquidity_intent_with_factories(
    intent: Intent,
    pool_state: PoolState,
    lp_balances: LPTable,
    balances: BalanceTable,
    *,
    add_liquidity_fn: Callable[..., tuple[int, int, int]],
    remove_liquidity_fn: Callable[..., tuple[int, int]],
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

            amount0_used, amount1_used, lp_minted = add_liquidity_fn(
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

            amount0_out, amount1_out = remove_liquidity_fn(
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
