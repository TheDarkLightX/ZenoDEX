"""Swap replay for strong settlement validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_out
from ..state.balances import AssetId, PubKey
from ..state.intents import Intent, IntentKind
from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .cpmm import swap_exact_in_with_protocol_fee
from .quote_receipts import pool_state_fingerprint
from .settlement import Fill
from .settlement_quote_binding import quote_binding_context, quote_binding_error
from .settlement_replay_context import ReplayContext
from .settlement_replay_cow_netting import CowNettingReplayRequest, replay_cow_netted_fill
from .settlement_replay_swap_common import (
    ProtocolFeeReplayConfig,
    SwapReplayAmounts,
    SwapReplayTarget,
    apply_swap_replay,
    check_swap_fee_fields,
    record_swap_replay_deltas,
)


@dataclass(frozen=True)
class SwapIntentReplayRequest:
    intent: Intent
    fill: Fill
    pool: PoolState
    pool_id: str
    recipient: PubKey
    quote_pool_fp: object
    require_reserve_witness: bool
    allow_cow_netting: bool
    protocol_fee: ProtocolFeeReplayConfig
    replay: ReplayContext


@dataclass(frozen=True)
class _SwapAssetPair:
    asset_in: AssetId
    asset_out: AssetId


@dataclass(frozen=True)
class _SwapReserveView:
    reserve_in: int
    reserve_out: int
    dir_is_0_to_1: bool


@dataclass(frozen=True)
class _SwapReplayRequest:
    intent: Intent
    fill: Fill
    target: SwapReplayTarget
    protocol_fee: ProtocolFeeReplayConfig


@dataclass(frozen=True)
class _SwapExactInReplayInput:
    amount_in: int
    min_out: int


@dataclass(frozen=True)
class _SwapExactOutReplayInput:
    amount_out: int
    max_in: int


def _parse_swap_asset_pair(intent: Intent) -> Tuple[Optional[_SwapAssetPair], Optional[str]]:
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(asset_in, str) or not isinstance(asset_out, str):
        return None, f"invalid asset_in/out for intent_id={intent.intent_id}"
    return _SwapAssetPair(asset_in=asset_in, asset_out=asset_out), None


def _validate_swap_pool_and_assets(
    *,
    intent_id: str,
    pool: PoolState,
    assets: _SwapAssetPair,
) -> Optional[str]:
    if pool.status != PoolStatus.ACTIVE:
        return f"pool not active for intent_id={intent_id}: {pool.status}"
    if {assets.asset_in, assets.asset_out} != {pool.asset0, pool.asset1} or assets.asset_in == assets.asset_out:
        return f"swap asset mismatch for intent_id={intent_id}"
    return None


def _validate_swap_quote_pool_fingerprint(
    *,
    intent: Intent,
    pool: PoolState,
    quote_pool_fp: object,
) -> Optional[str]:
    if quote_pool_fp is None:
        return None
    actual_pool_fp = pool_state_fingerprint(pool)
    if actual_pool_fp == quote_pool_fp:
        return None
    return quote_binding_error(
        "quote receipt pool snapshot mismatch",
        **quote_binding_context(intent),
        actual_pool_fingerprint=actual_pool_fp,
    )


def _swap_reserve_view(*, pool: PoolState, assets: _SwapAssetPair) -> _SwapReserveView:
    if assets.asset_in == pool.asset0 and assets.asset_out == pool.asset1:
        return _SwapReserveView(reserve_in=int(pool.reserve0), reserve_out=int(pool.reserve1), dir_is_0_to_1=True)
    return _SwapReserveView(reserve_in=int(pool.reserve1), reserve_out=int(pool.reserve0), dir_is_0_to_1=False)


def _build_swap_replay_target(
    *,
    request: SwapIntentReplayRequest,
) -> Tuple[Optional[SwapReplayTarget], Optional[str]]:
    intent_id = request.intent.intent_id
    assets, err = _parse_swap_asset_pair(request.intent)
    if assets is None:
        return None, err
    err = _validate_swap_pool_and_assets(intent_id=intent_id, pool=request.pool, assets=assets)
    if err is not None:
        return None, err
    err = _validate_swap_quote_pool_fingerprint(
        intent=request.intent,
        pool=request.pool,
        quote_pool_fp=request.quote_pool_fp,
    )
    if err is not None:
        return None, err
    reserve_view = _swap_reserve_view(pool=request.pool, assets=assets)

    return (
        SwapReplayTarget(
            intent_id=intent_id,
            sender=request.intent.sender_pubkey,
            recipient=request.recipient,
            pool_id=request.pool_id,
            pool=request.pool,
            asset_in=assets.asset_in,
            asset_out=assets.asset_out,
            reserve_in=reserve_view.reserve_in,
            reserve_out=reserve_view.reserve_out,
            dir_is_0_to_1=reserve_view.dir_is_0_to_1,
        ),
        None,
    )


def _check_swap_reserve_witness(
    *,
    fill: Fill,
    target: SwapReplayTarget,
    require_reserve_witness: bool,
) -> Optional[str]:
    if not require_reserve_witness:
        return None
    if fill.reserve_in_before is None or fill.reserve_out_before is None:
        return f"missing swap witness reserves for intent_id={target.intent_id}"
    if int(fill.reserve_in_before) != int(target.reserve_in) or int(fill.reserve_out_before) != int(target.reserve_out):
        return f"swap witness reserve mismatch for intent_id={target.intent_id}"
    return None


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


def _replay_swap_exact_in_fill(
    *,
    request: _SwapReplayRequest,
    replay: ReplayContext,
) -> Optional[str]:
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
        replay=replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )
    if err is not None:
        return err

    return record_swap_replay_deltas(
        replay=replay,
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


def _check_swap_exact_out_amount_fields(
    *,
    fill: Fill,
    target: SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    replay_amounts: SwapReplayAmounts,
) -> Optional[str]:
    if int(fill.amount_out_filled or 0) != int(replay_input.amount_out):
        return f"swap amount_out_filled mismatch for intent_id={target.intent_id}"
    if int(fill.amount_in_filled or 0) != int(replay_amounts.amount_in):
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


def _replay_swap_exact_out_fill(
    *,
    request: _SwapReplayRequest,
    replay: ReplayContext,
) -> Optional[str]:
    replay_input, err = _parse_swap_exact_out_replay_input(request.intent)
    if replay_input is None:
        return err or f"invalid amount_out for intent_id={request.target.intent_id}"
    if int(request.fill.amount_out_filled or 0) != int(replay_input.amount_out):
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
        replay=replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )
    if err is not None:
        return err

    return record_swap_replay_deltas(
        replay=replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )


def replay_swap_intent(*, request: SwapIntentReplayRequest) -> Optional[str]:
    swap_target, err = _build_swap_replay_target(request=request)
    if swap_target is None:
        return err or f"invalid asset_in/out for intent_id={request.intent.intent_id}"

    if request.fill.reason == "COW_NETTED":
        return replay_cow_netted_fill(
            request=CowNettingReplayRequest(
                intent=request.intent,
                fill=request.fill,
                intent_id=swap_target.intent_id,
                sender=swap_target.sender,
                recipient=swap_target.recipient,
                asset_in=swap_target.asset_in,
                asset_out=swap_target.asset_out,
                allow_cow_netting=request.allow_cow_netting,
            ),
            replay=request.replay,
        )

    err = _check_swap_reserve_witness(
        fill=request.fill,
        target=swap_target,
        require_reserve_witness=request.require_reserve_witness,
    )
    if err is not None:
        return err
    swap_request = _SwapReplayRequest(
        intent=request.intent,
        fill=request.fill,
        target=swap_target,
        protocol_fee=request.protocol_fee,
    )
    if request.intent.kind == IntentKind.SWAP_EXACT_IN:
        return _replay_swap_exact_in_fill(request=swap_request, replay=request.replay)
    return _replay_swap_exact_out_fill(request=swap_request, replay=request.replay)
