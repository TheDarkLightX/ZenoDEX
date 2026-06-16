"""Swap replay helpers for batch clearing."""

from __future__ import annotations

from typing import Optional, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from ..state.balances import Amount, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.pools import CURVE_TAG_CPMM, PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .settlement import Fill


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
