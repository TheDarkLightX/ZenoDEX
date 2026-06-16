"""Exact-in swap replay for strong settlement validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from ..state.intents import Intent
from ..state.pools import CURVE_TAG_CPMM
from .amm_dispatch import swap_exact_in_for_pool
from .cpmm import swap_exact_in_with_protocol_fee
from .settlement import Fill
from .settlement_replay_context import ReplayContext
from .settlement_replay_swap_common import (
    ProtocolFeeReplayConfig,
    SwapReplayAmounts,
    SwapReplayTarget,
    apply_swap_replay,
    check_swap_fee_fields,
    record_swap_replay_deltas,
)


@dataclass(frozen=True)
class SwapExactInReplayRequest:
    intent: Intent
    fill: Fill
    target: SwapReplayTarget
    protocol_fee: ProtocolFeeReplayConfig
    replay: ReplayContext


@dataclass(frozen=True)
class _SwapExactInReplayInput:
    amount_in: int
    min_out: int


def replay_swap_exact_in_fill(*, request: SwapExactInReplayRequest) -> Optional[str]:
    replay_input, err = _parse_swap_exact_in_replay_input(request.intent)
    if replay_input is None:
        return err or f"invalid amount_in for intent_id={request.target.intent_id}"
    if int(request.fill.amount_in_filled or 0) != int(replay_input.amount_in):
        return f"swap amount_in_filled mismatch for intent_id={request.target.intent_id}"

    replay_amounts, err = _quote_swap_exact_in_replay(
        target=request.target,
        replay_input=replay_input,
        protocol_fee=request.protocol_fee,
    )
    if replay_amounts is None:
        return err or f"swap_exact_in kernel error for intent_id={request.target.intent_id}"

    err = _check_swap_exact_in_fill(
        fill=request.fill,
        target=request.target,
        replay_input=replay_input,
        replay_amounts=replay_amounts,
    )
    if err is not None:
        return err

    err = apply_swap_replay(
        replay=request.replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )
    if err is not None:
        return err

    return record_swap_replay_deltas(
        replay=request.replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )


def _parse_swap_exact_in_replay_input(intent: Intent) -> Tuple[Optional[_SwapExactInReplayInput], Optional[str]]:
    intent_id = intent.intent_id
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return None, f"invalid amount_in for intent_id={intent_id}"
    if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
        return None, f"invalid min_amount_out for intent_id={intent_id}"
    return _SwapExactInReplayInput(amount_in=amount_in, min_out=min_out), None


def _quote_swap_exact_in_replay(
    *,
    target: SwapReplayTarget,
    replay_input: _SwapExactInReplayInput,
    protocol_fee: ProtocolFeeReplayConfig,
) -> Tuple[Optional[SwapReplayAmounts], Optional[str]]:
    try:
        if int(protocol_fee.share_bps):
            if target.pool.curve_tag != CURVE_TAG_CPMM:
                return None, f"protocol fee unsupported for curve intent_id={target.intent_id}"
            quote = swap_exact_in_with_protocol_fee(
                reserve_in=int(target.reserve_in),
                reserve_out=int(target.reserve_out),
                amount_in=int(replay_input.amount_in),
                fee_bps=int(target.pool.fee_bps),
                protocol_fee_share_bps=int(protocol_fee.share_bps),
            )
            return (
                SwapReplayAmounts(
                    amount_in=int(replay_input.amount_in),
                    amount_out=int(quote.amount_out),
                    new_reserve_in=int(quote.new_reserve_in),
                    new_reserve_out=int(quote.new_reserve_out),
                    protocol_fee=int(quote.protocol_fee),
                ),
                None,
            )

        amount_out, (new_in, new_out) = swap_exact_in_for_pool(
            target.pool,
            reserve_in=int(target.reserve_in),
            reserve_out=int(target.reserve_out),
            amount_in=int(replay_input.amount_in),
        )
        return (
            SwapReplayAmounts(
                amount_in=int(replay_input.amount_in),
                amount_out=int(amount_out),
                new_reserve_in=int(new_in),
                new_reserve_out=int(new_out),
                protocol_fee=0,
            ),
            None,
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return None, f"swap_exact_in kernel error for intent_id={target.intent_id}: {exc}"


def _check_swap_exact_in_fill(
    *,
    fill: Fill,
    target: SwapReplayTarget,
    replay_input: _SwapExactInReplayInput,
    replay_amounts: SwapReplayAmounts,
) -> Optional[str]:
    err = _check_swap_exact_in_amount_fields(
        fill=fill,
        target=target,
        replay_input=replay_input,
        replay_amounts=replay_amounts,
    )
    if err is not None:
        return err
    err = _check_swap_exact_in_slippage(target=target, replay_input=replay_input, replay_amounts=replay_amounts)
    if err is not None:
        return err
    return check_swap_fee_fields(
        fill=fill,
        target=target,
        fee_basis_amount=int(replay_input.amount_in),
        protocol_fee_paid=int(replay_amounts.protocol_fee),
    )


def _check_swap_exact_in_amount_fields(
    *,
    fill: Fill,
    target: SwapReplayTarget,
    replay_input: _SwapExactInReplayInput,
    replay_amounts: SwapReplayAmounts,
) -> Optional[str]:
    if int(fill.amount_in_filled or 0) != int(replay_input.amount_in):
        return f"swap amount_in_filled mismatch for intent_id={target.intent_id}"
    if int(fill.amount_out_filled or 0) != int(replay_amounts.amount_out):
        return f"swap amount_out_filled mismatch for intent_id={target.intent_id}"
    return None


def _check_swap_exact_in_slippage(
    *,
    target: SwapReplayTarget,
    replay_input: _SwapExactInReplayInput,
    replay_amounts: SwapReplayAmounts,
) -> Optional[str]:
    if int(replay_amounts.amount_out) < int(replay_input.min_out):
        return f"swap slippage for intent_id={target.intent_id}"
    return None
