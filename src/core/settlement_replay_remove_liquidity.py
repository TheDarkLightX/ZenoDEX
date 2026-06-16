"""REMOVE_LIQUIDITY replay for strong settlement validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from ..state.balances import PubKey
from ..state.intents import Intent
from ..state.pools import PoolState, PoolStatus
from .domain_limits import is_strict_int
from .liquidity import remove_liquidity
from .settlement import BalanceDelta, Fill, LPDelta, ReserveDelta
from .settlement_replay_context import ReplayContext


@dataclass(frozen=True)
class _RemoveLiquidityReplayInput:
    intent_id: str
    sender: PubKey
    recipient: PubKey
    pool_id: str
    lp_amount: int
    amount0_min: int
    amount1_min: int


@dataclass(frozen=True)
class _RemoveLiquidityReplayResult:
    amount0_out: int
    amount1_out: int


@dataclass(frozen=True)
class RemoveLiquidityReplayRequest:
    intent: Intent
    fill: Fill
    pool: PoolState
    pool_id: str
    recipient: PubKey
    replay: ReplayContext


def _parse_remove_liquidity_replay_input(
    *,
    intent: Intent,
    recipient: PubKey,
    pool_id: str,
) -> Tuple[Optional[_RemoveLiquidityReplayInput], Optional[str]]:
    intent_id = intent.intent_id
    lp_amount = intent.get_field("lp_amount")
    amount0_min = intent.get_field("amount0_min", 0)
    amount1_min = intent.get_field("amount1_min", 0)
    if lp_amount is None:
        return None, f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent_id}"
    if not is_strict_int(lp_amount) or lp_amount <= 0:
        return None, f"invalid lp_amount for intent_id={intent_id}"
    if not is_strict_int(amount0_min) or amount0_min < 0:
        return None, f"invalid amount0_min for intent_id={intent_id}"
    if not is_strict_int(amount1_min) or amount1_min < 0:
        return None, f"invalid amount1_min for intent_id={intent_id}"
    return (
        _RemoveLiquidityReplayInput(
            intent_id=intent_id,
            sender=intent.sender_pubkey,
            recipient=recipient,
            pool_id=pool_id,
            lp_amount=lp_amount,
            amount0_min=amount0_min,
            amount1_min=amount1_min,
        ),
        None,
    )


def _check_remove_liquidity_fill(
    *,
    fill: Fill,
    replay_input: _RemoveLiquidityReplayInput,
    replay_result: _RemoveLiquidityReplayResult,
) -> Optional[str]:
    if int(fill.lp_burned or 0) != int(replay_input.lp_amount):
        return f"REMOVE_LIQUIDITY fill.lp_burned mismatch for intent_id={replay_input.intent_id}"
    if int(fill.amount0_out or 0) != int(replay_result.amount0_out):
        return f"REMOVE_LIQUIDITY fill.amount0_out mismatch for intent_id={replay_input.intent_id}"
    if int(fill.amount1_out or 0) != int(replay_result.amount1_out):
        return f"REMOVE_LIQUIDITY fill.amount1_out mismatch for intent_id={replay_input.intent_id}"
    return None


def _apply_remove_liquidity_replay(
    *,
    replay: ReplayContext,
    pool: PoolState,
    replay_input: _RemoveLiquidityReplayInput,
    replay_result: _RemoveLiquidityReplayResult,
) -> Optional[str]:
    try:
        replay.lp.subtract(replay_input.sender, replay_input.pool_id, int(replay_input.lp_amount))
        replay.balances.add(replay_input.recipient, pool.asset0, int(replay_result.amount0_out))
        replay.balances.add(replay_input.recipient, pool.asset1, int(replay_result.amount1_out))
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"REMOVE_LIQUIDITY apply error for intent_id={replay_input.intent_id}: {exc}"

    pool.reserve0 -= int(replay_result.amount0_out)
    pool.reserve1 -= int(replay_result.amount1_out)
    pool.lp_supply -= int(replay_input.lp_amount)
    return None


def _record_remove_liquidity_deltas(
    *,
    replay: ReplayContext,
    pool: PoolState,
    replay_input: _RemoveLiquidityReplayInput,
    replay_result: _RemoveLiquidityReplayResult,
) -> None:
    replay.lp_deltas.append(
        LPDelta(
            pubkey=replay_input.sender,
            pool_id=replay_input.pool_id,
            delta_add=0,
            delta_sub=int(replay_input.lp_amount),
        )
    )
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.recipient,
            asset=pool.asset0,
            delta_add=int(replay_result.amount0_out),
            delta_sub=0,
        )
    )
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.recipient,
            asset=pool.asset1,
            delta_add=int(replay_result.amount1_out),
            delta_sub=0,
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_input.pool_id,
            asset=pool.asset0,
            delta_add=0,
            delta_sub=int(replay_result.amount0_out),
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_input.pool_id,
            asset=pool.asset1,
            delta_add=0,
            delta_sub=int(replay_result.amount1_out),
        )
    )


def replay_remove_liquidity_fill(
    *,
    request: RemoveLiquidityReplayRequest,
) -> Optional[str]:
    intent = request.intent
    fill = request.fill
    pool = request.pool
    replay = request.replay
    if pool.status != PoolStatus.ACTIVE:
        return f"pool not active for intent_id={intent.intent_id}: {pool.status}"

    replay_input, err = _parse_remove_liquidity_replay_input(
        intent=intent,
        recipient=request.recipient,
        pool_id=request.pool_id,
    )
    if replay_input is None:
        return err or f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent.intent_id}"

    try:
        amount0_out, amount1_out = remove_liquidity(
            pool_state=pool,
            lp_amount=replay_input.lp_amount,
            amount0_min=replay_input.amount0_min,
            amount1_min=replay_input.amount1_min,
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"REMOVE_LIQUIDITY computation error for intent_id={replay_input.intent_id}: {exc}"

    replay_result = _RemoveLiquidityReplayResult(amount0_out=amount0_out, amount1_out=amount1_out)
    err = _check_remove_liquidity_fill(
        fill=fill,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    err = _apply_remove_liquidity_replay(
        replay=replay,
        pool=pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    _record_remove_liquidity_deltas(
        replay=replay,
        pool=pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    return None
