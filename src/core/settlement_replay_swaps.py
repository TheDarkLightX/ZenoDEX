"""Swap replay for strong settlement validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from ..state.balances import AssetId, PubKey
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState, PoolStatus
from .domain_limits import is_strict_int
from .quote_receipts import pool_state_fingerprint
from .settlement import Fill
from .settlement_quote_binding import quote_binding_context, quote_binding_error
from .settlement_replay_context import ReplayContext
from .settlement_replay_cow_netting import CowNettingReplayRequest, replay_cow_netted_fill
from .settlement_replay_swap_common import ProtocolFeeReplayConfig, SwapReplayTarget
from .settlement_replay_swap_exact_in import SwapExactInReplayRequest, replay_swap_exact_in_fill
from .settlement_replay_swap_exact_out import SwapExactOutReplayRequest, replay_swap_exact_out_fill


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
    if not is_strict_int(fill.reserve_in_before) or not is_strict_int(fill.reserve_out_before):
        return f"invalid swap witness reserve type for intent_id={target.intent_id}"
    if fill.reserve_in_before < 0 or fill.reserve_out_before < 0:
        return f"invalid swap witness reserve value for intent_id={target.intent_id}"
    if fill.reserve_in_before != target.reserve_in or fill.reserve_out_before != target.reserve_out:
        return f"swap witness reserve mismatch for intent_id={target.intent_id}"
    return None


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
    if request.intent.kind == IntentKind.SWAP_EXACT_IN:
        return replay_swap_exact_in_fill(
            request=SwapExactInReplayRequest(
                intent=request.intent,
                fill=request.fill,
                target=swap_target,
                protocol_fee=request.protocol_fee,
                replay=request.replay,
            )
        )
    return replay_swap_exact_out_fill(
        request=SwapExactOutReplayRequest(
            intent=request.intent,
            fill=request.fill,
            target=swap_target,
            protocol_fee=request.protocol_fee,
            replay=request.replay,
        )
    )
