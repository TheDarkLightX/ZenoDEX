"""Swap replay helpers for batch clearing."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Optional, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from ..state.balances import Amount, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.pools import CURVE_TAG_CPMM, PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .cpmm import compute_fee_total
from .settlement import Fill, FillAction

_QuoteExactInFn = Callable[..., Any]
_QuoteExactOutFn = Callable[..., Any]
_SwapExactInFn = Callable[..., Any]
_SwapExactOutFn = Callable[..., Any]


@dataclass(frozen=True)
class _SwapIntentFactories:
    quote_exact_in_fn: _QuoteExactInFn
    quote_exact_out_fn: _QuoteExactOutFn
    swap_exact_in_fn: _SwapExactInFn
    swap_exact_out_fn: _SwapExactOutFn


@dataclass(frozen=True)
class _SwapIntentContext:
    pool_state: PoolState
    balances: BalanceTable
    asset_in: str
    reserve_in: Amount
    reserve_out: Amount
    protocol_fee_share_bps: int
    factories: _SwapIntentFactories


def _reject_swap_intent(intent: Intent, reason: str) -> Fill:
    return Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason=reason)


def _resolve_swap_reserves(
    intent: Intent,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> Tuple[str, str, Amount, Amount] | Fill:
    reserve0, reserve1 = reserves
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(asset_in, str) or not isinstance(asset_out, str):
        return _reject_swap_intent(intent, "MISSING_PARAMS")
    if asset_in == asset_out:
        return _reject_swap_intent(intent, "INVALID_ASSET_PAIR")

    # Direction fixes which reserve is charged and which reserve pays out.
    if asset_in == pool_state.asset0 and asset_out == pool_state.asset1:
        return asset_in, asset_out, reserve0, reserve1
    if asset_in == pool_state.asset1 and asset_out == pool_state.asset0:
        return asset_in, asset_out, reserve1, reserve0
    return _reject_swap_intent(intent, "ASSET_NOT_IN_POOL")


def _process_exact_in_swap_intent(
    intent: Intent,
    context: _SwapIntentContext,
) -> Fill:
    amount_in = intent.get_field("amount_in")
    min_amount_out = intent.get_field("min_amount_out", 0)
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return _reject_swap_intent(intent, "MISSING_PARAMS")
    if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool) or min_amount_out < 0:
        return _reject_swap_intent(intent, "MISSING_PARAMS")

    if context.balances.get(intent.sender_pubkey, context.asset_in) < amount_in:
        return _reject_swap_intent(intent, "INSUFFICIENT_BALANCE")

    if context.pool_state.curve_tag == CURVE_TAG_CPMM:
        quote = context.factories.quote_exact_in_fn(
            reserve_in=context.reserve_in,
            reserve_out=context.reserve_out,
            amount_in=amount_in,
            fee_bps=context.pool_state.fee_bps,
            protocol_fee_share_bps=context.protocol_fee_share_bps,
        )
        amount_out = quote.amount_out
        fee = quote.fee_paid
        protocol_fee = quote.protocol_fee_paid
    else:
        if context.protocol_fee_share_bps:
            return _reject_swap_intent(intent, "PROTOCOL_FEE_UNSUPPORTED_CURVE")
        amount_out, _new_reserves = context.factories.swap_exact_in_fn(
            context.pool_state,
            reserve_in=context.reserve_in,
            reserve_out=context.reserve_out,
            amount_in=amount_in,
        )
        fee = compute_fee_total(amount_in, context.pool_state.fee_bps)
        protocol_fee = 0

    if amount_out < min_amount_out:
        return _reject_swap_intent(intent, "SLIPPAGE")
    return Fill(
        intent_id=intent.intent_id,
        action=FillAction.FILL,
        amount_in_filled=amount_in,
        amount_out_filled=amount_out,
        fee_paid=fee,
        protocol_fee_paid=protocol_fee,
        reserve_in_before=int(context.reserve_in),
        reserve_out_before=int(context.reserve_out),
    )


def _process_exact_out_swap_intent(
    intent: Intent,
    context: _SwapIntentContext,
) -> Fill:
    amount_out = intent.get_field("amount_out")
    max_amount_in = intent.get_field("max_amount_in")
    if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
        return _reject_swap_intent(intent, "MISSING_PARAMS")
    if not isinstance(max_amount_in, int) or isinstance(max_amount_in, bool) or max_amount_in < 0:
        return _reject_swap_intent(intent, "MISSING_PARAMS")

    if context.pool_state.curve_tag == CURVE_TAG_CPMM:
        quote = context.factories.quote_exact_out_fn(
            reserve_in=context.reserve_in,
            reserve_out=context.reserve_out,
            amount_out=amount_out,
            fee_bps=context.pool_state.fee_bps,
            protocol_fee_share_bps=context.protocol_fee_share_bps,
        )
        amount_in = quote.amount_in
        fee = quote.fee_paid
        protocol_fee = quote.protocol_fee_paid
    else:
        if context.protocol_fee_share_bps:
            return _reject_swap_intent(intent, "PROTOCOL_FEE_UNSUPPORTED_CURVE")
        amount_in, _new_reserves = context.factories.swap_exact_out_fn(
            context.pool_state,
            reserve_in=context.reserve_in,
            reserve_out=context.reserve_out,
            amount_out=amount_out,
        )
        fee = compute_fee_total(amount_in, context.pool_state.fee_bps)
        protocol_fee = 0

    if context.balances.get(intent.sender_pubkey, context.asset_in) < amount_in:
        return _reject_swap_intent(intent, "INSUFFICIENT_BALANCE")
    if amount_in > max_amount_in:
        return _reject_swap_intent(intent, "SLIPPAGE")
    return Fill(
        intent_id=intent.intent_id,
        action=FillAction.FILL,
        amount_in_filled=amount_in,
        amount_out_filled=amount_out,
        fee_paid=fee,
        protocol_fee_paid=protocol_fee,
        reserve_in_before=int(context.reserve_in),
        reserve_out_before=int(context.reserve_out),
    )


def _process_swap_intent_with_factories(
    intent: Intent,
    reserves: Tuple[Amount, Amount],
    pool_state: PoolState,
    balances: BalanceTable,
    *,
    protocol_fee_share_bps: int,
    factories: _SwapIntentFactories,
) -> Fill:
    """Process a single swap intent against a pool snapshot."""
    resolved = _resolve_swap_reserves(intent, pool_state, reserves)
    if isinstance(resolved, Fill):
        return resolved
    asset_in, _asset_out, reserve_in, reserve_out = resolved
    context = _SwapIntentContext(
        pool_state=pool_state,
        balances=balances,
        asset_in=asset_in,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        protocol_fee_share_bps=protocol_fee_share_bps,
        factories=factories,
    )

    try:
        if intent.kind == IntentKind.SWAP_EXACT_IN:
            return _process_exact_in_swap_intent(
                intent,
                context,
            )
        if intent.kind == IntentKind.SWAP_EXACT_OUT:
            return _process_exact_out_swap_intent(
                intent,
                context,
            )
    except (ValueError, ZeroDivisionError) as e:
        return _reject_swap_intent(intent, f"COMPUTATION_ERROR: {str(e)}")

    return _reject_swap_intent(intent, "UNKNOWN_INTENT_TYPE")


def _reserves_after_swap_fill(
    intent: Intent,
    fill: Fill,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
    *,
    protocol_fee_share_bps: int,
) -> Tuple[Amount, Amount]:
    asset_in = intent.get_field("asset_in")
    if asset_in == pool_state.asset0:
        if intent.kind == IntentKind.SWAP_EXACT_IN:
            if pool_state.curve_tag == CURVE_TAG_CPMM:
                quote = quote_cpmm_swap_exact_in(
                    reserve_in=reserves[0],
                    reserve_out=reserves[1],
                    amount_in=fill.amount_in_filled or 0,
                    fee_bps=pool_state.fee_bps,
                    protocol_fee_share_bps=protocol_fee_share_bps,
                )
                return quote.reserve_in_after, quote.reserve_out_after
            _, next_reserves = swap_exact_in_for_pool(
                pool_state,
                reserve_in=reserves[0],
                reserve_out=reserves[1],
                amount_in=fill.amount_in_filled or 0,
            )
            return next_reserves

        if pool_state.curve_tag == CURVE_TAG_CPMM:
            quote = quote_cpmm_swap_exact_out(
                reserve_in=reserves[0],
                reserve_out=reserves[1],
                amount_out=fill.amount_out_filled or 0,
                fee_bps=pool_state.fee_bps,
                protocol_fee_share_bps=protocol_fee_share_bps,
            )
            return quote.reserve_in_after, quote.reserve_out_after
        _, next_reserves = swap_exact_out_for_pool(
            pool_state,
            reserve_in=reserves[0],
            reserve_out=reserves[1],
            amount_out=fill.amount_out_filled or 0,
        )
        return next_reserves

    if intent.kind == IntentKind.SWAP_EXACT_IN:
        if pool_state.curve_tag == CURVE_TAG_CPMM:
            quote = quote_cpmm_swap_exact_in(
                reserve_in=reserves[1],
                reserve_out=reserves[0],
                amount_in=fill.amount_in_filled or 0,
                fee_bps=pool_state.fee_bps,
                protocol_fee_share_bps=protocol_fee_share_bps,
            )
            return quote.reserve_out_after, quote.reserve_in_after
        _, (new_r1, new_r0) = swap_exact_in_for_pool(
            pool_state,
            reserve_in=reserves[1],
            reserve_out=reserves[0],
            amount_in=fill.amount_in_filled or 0,
        )
        return new_r0, new_r1

    if pool_state.curve_tag == CURVE_TAG_CPMM:
        quote = quote_cpmm_swap_exact_out(
            reserve_in=reserves[1],
            reserve_out=reserves[0],
            amount_out=fill.amount_out_filled or 0,
            fee_bps=pool_state.fee_bps,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )
        return quote.reserve_out_after, quote.reserve_in_after
    _, (new_r1, new_r0) = swap_exact_out_for_pool(
        pool_state,
        reserve_in=reserves[1],
        reserve_out=reserves[0],
        amount_out=fill.amount_out_filled or 0,
    )
    return new_r0, new_r1


def _apply_swap_fill_to_scratch_balances(
    intent: Intent,
    fill: Fill,
    balances: BalanceTable,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> None:
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    recipient = intent.get_field("recipient", intent.sender_pubkey)
    balances.subtract(intent.sender_pubkey, asset_in, fill.amount_in_filled or 0)
    balances.add(recipient, asset_out, fill.amount_out_filled or 0)
    protocol_fee = int(fill.protocol_fee_paid or 0)
    if protocol_fee:
        if not protocol_fee_recipient_pubkey:
            raise ValueError("protocol_fee_recipient_pubkey is required for protocol fee capture")
        balances.add(protocol_fee_recipient_pubkey, asset_in, protocol_fee)
