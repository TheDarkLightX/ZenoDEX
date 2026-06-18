"""Exact-out swap replay for strong settlement validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_out
from ..state.intents import Intent
from ..state.pools import CURVE_TAG_CPMM
from .amm_dispatch import swap_exact_out_for_pool
from .settlement import Fill
from .settlement_replay_context import ReplayContext
from .settlement_replay_swap_common import (
    ProtocolFeeReplayConfig,
    SwapReplayAmounts,
    SwapReplayTarget,
    apply_swap_replay,
    check_swap_fee_fields,
    read_optional_fill_int,
    record_swap_replay_deltas,
)


@dataclass(frozen=True)
class SwapExactOutReplayRequest:
    intent: Intent
    fill: Fill
    target: SwapReplayTarget
    protocol_fee: ProtocolFeeReplayConfig
    replay: ReplayContext


@dataclass(frozen=True)
class _SwapExactOutReplayInput:
    amount_out: int
    max_in: int


def replay_swap_exact_out_fill(*, request: SwapExactOutReplayRequest) -> Optional[str]:
    replay_input, err = _parse_swap_exact_out_replay_input(request.intent)
    if replay_input is None:
        return err or f"invalid amount_out for intent_id={request.target.intent_id}"
    amount_out_filled, err = read_optional_fill_int(
        request.fill.amount_out_filled,
        field_name="amount_out_filled",
        intent_id=request.target.intent_id,
    )
    if err is not None:
        return err
    if amount_out_filled != int(replay_input.amount_out):
        return f"swap amount_out_filled mismatch for intent_id={request.target.intent_id}"

    replay_amounts, err = _quote_swap_exact_out_replay(
        target=request.target,
        replay_input=replay_input,
        protocol_fee=request.protocol_fee,
    )
    if replay_amounts is None:
        return err or f"swap_exact_out kernel error for intent_id={request.target.intent_id}"

    err = _check_swap_exact_out_fill(
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


def _parse_swap_exact_out_replay_input(intent: Intent) -> Tuple[Optional[_SwapExactOutReplayInput], Optional[str]]:
    intent_id = intent.intent_id
    amount_out = intent.get_field("amount_out")
    max_in = intent.get_field("max_amount_in")
    if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
        return None, f"invalid amount_out for intent_id={intent_id}"
    if not isinstance(max_in, int) or isinstance(max_in, bool) or max_in < 0:
        return None, f"invalid max_amount_in for intent_id={intent_id}"
    return _SwapExactOutReplayInput(amount_out=amount_out, max_in=max_in), None


def _quote_swap_exact_out_replay(
    *,
    target: SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    protocol_fee: ProtocolFeeReplayConfig,
) -> Tuple[Optional[SwapReplayAmounts], Optional[str]]:
    try:
        if int(protocol_fee.share_bps):
            if target.pool.curve_tag != CURVE_TAG_CPMM:
                return None, f"protocol fee unsupported for curve intent_id={target.intent_id}"
            quote = quote_cpmm_swap_exact_out(
                reserve_in=int(target.reserve_in),
                reserve_out=int(target.reserve_out),
                amount_out=int(replay_input.amount_out),
                fee_bps=int(target.pool.fee_bps),
                protocol_fee_share_bps=int(protocol_fee.share_bps),
            )
            return (
                SwapReplayAmounts(
                    amount_in=int(quote.amount_in),
                    amount_out=int(replay_input.amount_out),
                    new_reserve_in=int(quote.reserve_in_after),
                    new_reserve_out=int(quote.reserve_out_after),
                    protocol_fee=int(quote.protocol_fee_paid),
                ),
                None,
            )

        amount_in, (new_in, new_out) = swap_exact_out_for_pool(
            target.pool,
            reserve_in=int(target.reserve_in),
            reserve_out=int(target.reserve_out),
            amount_out=int(replay_input.amount_out),
        )
        return (
            SwapReplayAmounts(
                amount_in=int(amount_in),
                amount_out=int(replay_input.amount_out),
                new_reserve_in=int(new_in),
                new_reserve_out=int(new_out),
                protocol_fee=0,
            ),
            None,
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return None, f"swap_exact_out kernel error for intent_id={target.intent_id}: {exc}"


def _check_swap_exact_out_fill(
    *,
    fill: Fill,
    target: SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    replay_amounts: SwapReplayAmounts,
) -> Optional[str]:
    err = _check_swap_exact_out_amount_fields(
        fill=fill,
        target=target,
        replay_input=replay_input,
        replay_amounts=replay_amounts,
    )
    if err is not None:
        return err
    err = _check_swap_exact_out_slippage(target=target, replay_input=replay_input, replay_amounts=replay_amounts)
    if err is not None:
        return err
    return check_swap_fee_fields(
        fill=fill,
        target=target,
        fee_basis_amount=int(replay_amounts.amount_in),
        protocol_fee_paid=int(replay_amounts.protocol_fee),
    )


def _check_swap_exact_out_amount_fields(
    *,
    fill: Fill,
    target: SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    replay_amounts: SwapReplayAmounts,
) -> Optional[str]:
    amount_out_filled, err = read_optional_fill_int(
        fill.amount_out_filled,
        field_name="amount_out_filled",
        intent_id=target.intent_id,
    )
    if err is not None:
        return err
    amount_in_filled, err = read_optional_fill_int(
        fill.amount_in_filled,
        field_name="amount_in_filled",
        intent_id=target.intent_id,
    )
    if err is not None:
        return err
    if amount_out_filled != int(replay_input.amount_out):
        return f"swap amount_out_filled mismatch for intent_id={target.intent_id}"
    if amount_in_filled != int(replay_amounts.amount_in):
        return f"swap amount_in_filled mismatch for intent_id={target.intent_id}"
    return None


def _check_swap_exact_out_slippage(
    *,
    target: SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    replay_amounts: SwapReplayAmounts,
) -> Optional[str]:
    if int(replay_amounts.amount_in) > int(replay_input.max_in):
        return f"swap slippage for intent_id={target.intent_id}"
    return None
