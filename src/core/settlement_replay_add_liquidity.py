"""ADD_LIQUIDITY replay for strong settlement validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from ..state.balances import PubKey
from ..state.intents import Intent
from ..state.pools import PoolState, PoolStatus
from .domain_limits import is_strict_int
from .liquidity import add_liquidity
from .settlement import BalanceDelta, Fill, LPDelta, ReserveDelta
from .settlement_replay_context import ReplayContext


@dataclass(frozen=True)
class _AddLiquidityReplayInput:
    intent_id: str
    sender: PubKey
    recipient: PubKey
    pool_id: str
    amount0_desired: int
    amount1_desired: int
    amount0_min: int
    amount1_min: int


@dataclass(frozen=True)
class _AddLiquidityIntentFields:
    amount0_desired: object
    amount1_desired: object
    amount0_min: object
    amount1_min: object


@dataclass(frozen=True)
class _AddLiquidityAmounts:
    amount0_desired: int
    amount1_desired: int
    amount0_min: int
    amount1_min: int


@dataclass(frozen=True)
class _AddLiquidityReplayResult:
    amount0_used: int
    amount1_used: int
    lp_minted: int


@dataclass(frozen=True)
class AddLiquidityReplayRequest:
    intent: Intent
    fill: Fill
    pool: PoolState
    pool_id: str
    recipient: PubKey
    replay: ReplayContext


def _add_liquidity_intent_fields(intent: Intent) -> _AddLiquidityIntentFields:
    return _AddLiquidityIntentFields(
        amount0_desired=intent.get_field("amount0_desired"),
        amount1_desired=intent.get_field("amount1_desired"),
        amount0_min=intent.get_field("amount0_min", 0),
        amount1_min=intent.get_field("amount1_min", 0),
    )


def _validate_add_liquidity_required_fields(
    *,
    intent_id: str,
    fields: _AddLiquidityIntentFields,
) -> Optional[str]:
    if any(v is None for v in (fields.amount0_desired, fields.amount1_desired)):
        return f"missing ADD_LIQUIDITY fields for intent_id={intent_id}"
    return None


def _parse_add_liquidity_positive_amount(
    *,
    intent_id: str,
    field_name: str,
    value: object,
) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(value) or value <= 0:
        return None, f"invalid {field_name} for intent_id={intent_id}"
    return value, None


def _parse_add_liquidity_min_amount(
    *,
    intent_id: str,
    field_name: str,
    value: object,
) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(value) or value < 0:
        return None, f"invalid {field_name} for intent_id={intent_id}"
    return value, None


def _parse_add_liquidity_amounts(
    *,
    intent_id: str,
    fields: _AddLiquidityIntentFields,
) -> Tuple[Optional[_AddLiquidityAmounts], Optional[str]]:
    amount0_desired, err = _parse_add_liquidity_positive_amount(
        intent_id=intent_id,
        field_name="amount0_desired",
        value=fields.amount0_desired,
    )
    if amount0_desired is None:
        return None, err
    amount1_desired, err = _parse_add_liquidity_positive_amount(
        intent_id=intent_id,
        field_name="amount1_desired",
        value=fields.amount1_desired,
    )
    if amount1_desired is None:
        return None, err
    amount0_min, err = _parse_add_liquidity_min_amount(
        intent_id=intent_id,
        field_name="amount0_min",
        value=fields.amount0_min,
    )
    if amount0_min is None:
        return None, err
    amount1_min, err = _parse_add_liquidity_min_amount(
        intent_id=intent_id,
        field_name="amount1_min",
        value=fields.amount1_min,
    )
    if amount1_min is None:
        return None, err
    return (
        _AddLiquidityAmounts(
            amount0_desired=amount0_desired,
            amount1_desired=amount1_desired,
            amount0_min=amount0_min,
            amount1_min=amount1_min,
        ),
        None,
    )


def _parse_add_liquidity_replay_input(
    *,
    intent: Intent,
    recipient: PubKey,
    pool_id: str,
) -> Tuple[Optional[_AddLiquidityReplayInput], Optional[str]]:
    intent_id = intent.intent_id
    fields = _add_liquidity_intent_fields(intent)
    err = _validate_add_liquidity_required_fields(intent_id=intent_id, fields=fields)
    if err is not None:
        return None, err
    amounts, err = _parse_add_liquidity_amounts(intent_id=intent_id, fields=fields)
    if amounts is None:
        return None, err
    return (
        _AddLiquidityReplayInput(
            intent_id=intent_id,
            sender=intent.sender_pubkey,
            recipient=recipient,
            pool_id=pool_id,
            amount0_desired=amounts.amount0_desired,
            amount1_desired=amounts.amount1_desired,
            amount0_min=amounts.amount0_min,
            amount1_min=amounts.amount1_min,
        ),
        None,
    )


def _check_add_liquidity_fill(
    *,
    fill: Fill,
    replay_input: _AddLiquidityReplayInput,
    replay_result: _AddLiquidityReplayResult,
) -> Optional[str]:
    if int(fill.amount0_used or 0) != int(replay_result.amount0_used):
        return f"ADD_LIQUIDITY fill.amount0_used mismatch for intent_id={replay_input.intent_id}"
    if int(fill.amount1_used or 0) != int(replay_result.amount1_used):
        return f"ADD_LIQUIDITY fill.amount1_used mismatch for intent_id={replay_input.intent_id}"
    if int(fill.lp_minted or 0) != int(replay_result.lp_minted):
        return f"ADD_LIQUIDITY fill.lp_minted mismatch for intent_id={replay_input.intent_id}"
    return None


def _apply_add_liquidity_replay(
    *,
    replay: ReplayContext,
    pool: PoolState,
    replay_input: _AddLiquidityReplayInput,
    replay_result: _AddLiquidityReplayResult,
) -> Optional[str]:
    try:
        replay.balances.subtract(replay_input.sender, pool.asset0, int(replay_result.amount0_used))
        replay.balances.subtract(replay_input.sender, pool.asset1, int(replay_result.amount1_used))
        replay.lp.add(replay_input.recipient, replay_input.pool_id, int(replay_result.lp_minted))
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"ADD_LIQUIDITY apply error for intent_id={replay_input.intent_id}: {exc}"

    pool.reserve0 += int(replay_result.amount0_used)
    pool.reserve1 += int(replay_result.amount1_used)
    pool.lp_supply += int(replay_result.lp_minted)
    return None


def _record_add_liquidity_deltas(
    *,
    replay: ReplayContext,
    pool: PoolState,
    replay_input: _AddLiquidityReplayInput,
    replay_result: _AddLiquidityReplayResult,
) -> None:
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.sender,
            asset=pool.asset0,
            delta_add=0,
            delta_sub=int(replay_result.amount0_used),
        )
    )
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.sender,
            asset=pool.asset1,
            delta_add=0,
            delta_sub=int(replay_result.amount1_used),
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_input.pool_id,
            asset=pool.asset0,
            delta_add=int(replay_result.amount0_used),
            delta_sub=0,
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_input.pool_id,
            asset=pool.asset1,
            delta_add=int(replay_result.amount1_used),
            delta_sub=0,
        )
    )
    replay.lp_deltas.append(
        LPDelta(
            pubkey=replay_input.recipient,
            pool_id=replay_input.pool_id,
            delta_add=int(replay_result.lp_minted),
            delta_sub=0,
        )
    )


def replay_add_liquidity_fill(
    *,
    request: AddLiquidityReplayRequest,
) -> Optional[str]:
    intent = request.intent
    fill = request.fill
    pool = request.pool
    replay = request.replay
    if pool.status != PoolStatus.ACTIVE:
        return f"pool not active for intent_id={intent.intent_id}: {pool.status}"

    replay_input, err = _parse_add_liquidity_replay_input(
        intent=intent,
        recipient=request.recipient,
        pool_id=request.pool_id,
    )
    if replay_input is None:
        return err or f"missing ADD_LIQUIDITY fields for intent_id={intent.intent_id}"

    try:
        amount0_used, amount1_used, lp_minted = add_liquidity(
            pool_state=pool,
            amount0_desired=replay_input.amount0_desired,
            amount1_desired=replay_input.amount1_desired,
            amount0_min=replay_input.amount0_min,
            amount1_min=replay_input.amount1_min,
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"ADD_LIQUIDITY computation error for intent_id={replay_input.intent_id}: {exc}"

    replay_result = _AddLiquidityReplayResult(
        amount0_used=amount0_used,
        amount1_used=amount1_used,
        lp_minted=lp_minted,
    )
    err = _check_add_liquidity_fill(
        fill=fill,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    err = _apply_add_liquidity_replay(
        replay=replay,
        pool=pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    _record_add_liquidity_deltas(
        replay=replay,
        pool=pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    return None
