"""CREATE_POOL replay for strong settlement validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from ..state.balances import AssetId, PubKey
from ..state.intents import Intent
from ..state.pools import PoolState, PoolStatus
from .cpmm import MIN_LP_LOCK
from .domain_limits import is_strict_int
from .liquidity import create_pool
from .settlement import BalanceDelta, Fill, LPDelta, ReserveDelta
from .settlement_fill_fields import read_optional_non_negative_fill_int
from .settlement_replay_context import ReplayContext

LP_LOCK_PUBKEY: PubKey = "0x" + "00" * 48


@dataclass(frozen=True)
class _CreatePoolIntentFields:
    asset0: object
    asset1: object
    fee_bps: object
    amount0: object
    amount1: object
    created_at: object
    curve_tag: object
    curve_params: object


@dataclass(frozen=True)
class _CreatePoolAssetIds:
    asset0: AssetId
    asset1: AssetId


@dataclass(frozen=True)
class _CreatePoolScalars:
    fee_bps: int
    amount0: int
    amount1: int
    created_at: int


@dataclass(frozen=True)
class _CreatePoolReplayInput:
    intent_id: str
    sender: PubKey
    asset0: AssetId
    asset1: AssetId
    fee_bps: int
    amount0: int
    amount1: int
    created_at: int
    curve_tag: object
    curve_params: object


@dataclass(frozen=True)
class _CreatePoolReplayResult:
    pool_id: str
    created_pool: PoolState
    lp_minted: int


def _create_pool_intent_fields(intent: Intent) -> _CreatePoolIntentFields:
    return _CreatePoolIntentFields(
        asset0=intent.get_field("asset0"),
        asset1=intent.get_field("asset1"),
        fee_bps=intent.get_field("fee_bps"),
        amount0=intent.get_field("amount0"),
        amount1=intent.get_field("amount1"),
        created_at=intent.get_field("created_at", 0),
        curve_tag=intent.get_field("curve_tag", None),
        curve_params=intent.get_wire_field("curve_params", None),
    )


def _validate_create_pool_required_fields(
    *,
    intent_id: str,
    fields: _CreatePoolIntentFields,
) -> Optional[str]:
    if any(v is None for v in (fields.asset0, fields.asset1, fields.fee_bps, fields.amount0, fields.amount1)):
        return f"missing CREATE_POOL fields for intent_id={intent_id}"
    return None


def _parse_create_pool_asset_ids(
    *,
    intent_id: str,
    fields: _CreatePoolIntentFields,
) -> Tuple[Optional[_CreatePoolAssetIds], Optional[str]]:
    if not isinstance(fields.asset0, str) or not isinstance(fields.asset1, str):
        return None, f"invalid CREATE_POOL asset ids for intent_id={intent_id}"
    return _CreatePoolAssetIds(asset0=fields.asset0, asset1=fields.asset1), None


def _parse_create_pool_fee_bps(*, intent_id: str, value: object) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(value) or not (0 <= value <= 10000):
        return None, f"invalid CREATE_POOL fee_bps for intent_id={intent_id}"
    return value, None


def _parse_create_pool_positive_amount(
    *,
    intent_id: str,
    field_name: str,
    value: object,
) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(value) or value <= 0:
        return None, f"invalid CREATE_POOL {field_name} for intent_id={intent_id}"
    return value, None


def _parse_create_pool_created_at(*, intent_id: str, value: object) -> Tuple[Optional[int], Optional[str]]:
    if value is not None and (not is_strict_int(value) or value < 0):
        return None, f"invalid CREATE_POOL created_at for intent_id={intent_id}"
    return 0 if value is None else value, None


def _parse_create_pool_scalars(
    *,
    intent_id: str,
    fields: _CreatePoolIntentFields,
) -> Tuple[Optional[_CreatePoolScalars], Optional[str]]:
    fee_bps, err = _parse_create_pool_fee_bps(intent_id=intent_id, value=fields.fee_bps)
    if fee_bps is None:
        return None, err
    amount0, err = _parse_create_pool_positive_amount(intent_id=intent_id, field_name="amount0", value=fields.amount0)
    if amount0 is None:
        return None, err
    amount1, err = _parse_create_pool_positive_amount(intent_id=intent_id, field_name="amount1", value=fields.amount1)
    if amount1 is None:
        return None, err
    created_at, err = _parse_create_pool_created_at(intent_id=intent_id, value=fields.created_at)
    if created_at is None:
        return None, err
    return (
        _CreatePoolScalars(
            fee_bps=fee_bps,
            amount0=amount0,
            amount1=amount1,
            created_at=created_at,
        ),
        None,
    )


def _parse_create_pool_replay_input(
    intent: Intent,
) -> Tuple[Optional[_CreatePoolReplayInput], Optional[str]]:
    intent_id = intent.intent_id
    fields = _create_pool_intent_fields(intent)
    err = _validate_create_pool_required_fields(intent_id=intent_id, fields=fields)
    if err is not None:
        return None, err
    asset_ids, err = _parse_create_pool_asset_ids(intent_id=intent_id, fields=fields)
    if asset_ids is None:
        return None, err
    scalars, err = _parse_create_pool_scalars(intent_id=intent_id, fields=fields)
    if scalars is None:
        return None, err
    return (
        _CreatePoolReplayInput(
            intent_id=intent_id,
            sender=intent.sender_pubkey,
            asset0=asset_ids.asset0,
            asset1=asset_ids.asset1,
            fee_bps=scalars.fee_bps,
            amount0=scalars.amount0,
            amount1=scalars.amount1,
            created_at=scalars.created_at,
            curve_tag=fields.curve_tag,
            curve_params=fields.curve_params,
        ),
        None,
    )


def _check_create_pool_fill(
    *,
    fill: Fill,
    replay_input: _CreatePoolReplayInput,
    replay_result: _CreatePoolReplayResult,
) -> Optional[str]:
    amount0_used, err = read_optional_non_negative_fill_int(
        fill.amount0_used,
        operation="CREATE_POOL",
        field_name="amount0_used",
        intent_id=replay_input.intent_id,
    )
    if err is not None:
        return err
    amount1_used, err = read_optional_non_negative_fill_int(
        fill.amount1_used,
        operation="CREATE_POOL",
        field_name="amount1_used",
        intent_id=replay_input.intent_id,
    )
    if err is not None:
        return err
    lp_minted, err = read_optional_non_negative_fill_int(
        fill.lp_minted,
        operation="CREATE_POOL",
        field_name="lp_minted",
        intent_id=replay_input.intent_id,
    )
    if err is not None:
        return err
    if amount0_used != int(replay_input.amount0):
        return f"CREATE_POOL fill.amount0_used mismatch for intent_id={replay_input.intent_id}"
    if amount1_used != int(replay_input.amount1):
        return f"CREATE_POOL fill.amount1_used mismatch for intent_id={replay_input.intent_id}"
    if lp_minted != int(replay_result.lp_minted):
        return f"CREATE_POOL fill.lp_minted mismatch for intent_id={replay_input.intent_id}"
    return None


def _apply_create_pool_replay(
    *,
    replay: ReplayContext,
    replay_input: _CreatePoolReplayInput,
    replay_result: _CreatePoolReplayResult,
) -> Optional[str]:
    try:
        replay.balances.subtract(replay_input.sender, replay_input.asset0, int(replay_input.amount0))
        replay.balances.subtract(replay_input.sender, replay_input.asset1, int(replay_input.amount1))
        replay.lp.add(replay_input.sender, replay_result.pool_id, int(replay_result.lp_minted))
        replay.lp.add(LP_LOCK_PUBKEY, replay_result.pool_id, int(MIN_LP_LOCK))
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"CREATE_POOL balance/LP apply error for intent_id={replay_input.intent_id}: {exc}"
    return None


def _record_create_pool_replay(
    *,
    replay: ReplayContext,
    replay_input: _CreatePoolReplayInput,
    replay_result: _CreatePoolReplayResult,
) -> None:
    replay.pools[replay_result.pool_id] = replay_result.created_pool
    _record_create_pool_event(
        replay=replay,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    _record_create_pool_deltas(
        replay=replay,
        replay_input=replay_input,
        replay_result=replay_result,
    )


def _record_create_pool_event(
    *,
    replay: ReplayContext,
    replay_input: _CreatePoolReplayInput,
    replay_result: _CreatePoolReplayResult,
) -> None:
    replay.expected_events.append(
        {
            "type": "CREATE_POOL",
            "pool_id": replay_result.pool_id,
            "asset0": replay_input.asset0,
            "asset1": replay_input.asset1,
            "fee_bps": int(replay_input.fee_bps),
            "curve_tag": replay_result.created_pool.curve_tag,
            "curve_params": replay_result.created_pool.curve_params,
            "status": PoolStatus.ACTIVE.value,
            "created_at": int(replay_result.created_pool.created_at),
        }
    )


def _record_create_pool_deltas(
    *,
    replay: ReplayContext,
    replay_input: _CreatePoolReplayInput,
    replay_result: _CreatePoolReplayResult,
) -> None:
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.sender,
            asset=replay_input.asset0,
            delta_add=0,
            delta_sub=int(replay_input.amount0),
        )
    )
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.sender,
            asset=replay_input.asset1,
            delta_add=0,
            delta_sub=int(replay_input.amount1),
        )
    )

    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_result.pool_id,
            asset=replay_input.asset0,
            delta_add=int(replay_input.amount0),
            delta_sub=0,
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_result.pool_id,
            asset=replay_input.asset1,
            delta_add=int(replay_input.amount1),
            delta_sub=0,
        )
    )

    replay.lp_deltas.append(
        LPDelta(
            pubkey=replay_input.sender,
            pool_id=replay_result.pool_id,
            delta_add=int(replay_result.lp_minted),
            delta_sub=0,
        )
    )
    replay.lp_deltas.append(
        LPDelta(
            pubkey=LP_LOCK_PUBKEY,
            pool_id=replay_result.pool_id,
            delta_add=int(MIN_LP_LOCK),
            delta_sub=0,
        )
    )


def replay_create_pool_fill(
    *,
    intent: Intent,
    fill: Fill,
    replay: ReplayContext,
) -> Optional[str]:
    intent_id = intent.intent_id

    replay_input, err = _parse_create_pool_replay_input(intent)
    if replay_input is None:
        return err or f"missing CREATE_POOL fields for intent_id={intent_id}"

    try:
        pool_id, created_pool, lp_minted = create_pool(
            asset0=replay_input.asset0,
            asset1=replay_input.asset1,
            amount0=replay_input.amount0,
            amount1=replay_input.amount1,
            fee_bps=replay_input.fee_bps,
            creator_pubkey=replay_input.sender,
            created_at=replay_input.created_at,
            curve_tag=replay_input.curve_tag,
            curve_params=replay_input.curve_params,
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"CREATE_POOL computation error for intent_id={intent_id}: {exc}"

    if pool_id in replay.pools:
        return f"CREATE_POOL duplicates existing pool_id={pool_id}"

    replay_result = _CreatePoolReplayResult(
        pool_id=pool_id,
        created_pool=created_pool,
        lp_minted=lp_minted,
    )
    err = _check_create_pool_fill(
        fill=fill,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    err = _apply_create_pool_replay(
        replay=replay,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    _record_create_pool_replay(
        replay=replay,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    return None
