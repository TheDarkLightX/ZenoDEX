"""
Strong settlement validation (proof-carrying friendly).

The legacy validator in `src/core/batch_clearing.py` checks conservation and
non-negativity of the *net* deltas, but it does not bind those deltas to:
  - the user intents (min_out / max_in constraints, recipient rules, etc.)
  - the verified swap kernels (no "k decreases" / free value leaks)

This module treats the settlement as an *untrusted certificate* and replay-
verifies the batch by re-executing each filled intent against local copies of
state using the verified kernels (`amm_dispatch`, `lp_math_v7`, etc). It then
recomputes canonical deltas/events and requires exact match.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_out
from ..state.balances import AssetId, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .batch_clearing import validate_settlement as validate_settlement_legacy
from .cpmm import compute_fee_total, swap_exact_in_with_protocol_fee
from .domain_limits import is_strict_int
from .liquidity import add_liquidity, remove_liquidity
from .quote_receipts import pool_state_fingerprint
from .settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement
from .settlement_canonical_deltas import aggregate_balance_deltas as _aggregate_balance_deltas
from .settlement_canonical_deltas import aggregate_lp_deltas as _aggregate_lp_deltas
from .settlement_canonical_deltas import aggregate_reserve_deltas as _aggregate_reserve_deltas
from .settlement_canonical_deltas import check_canonical_deltas as _check_canonical_deltas
from .settlement_cow_pairs import (
    validate_cow_pair_index as _validate_cow_pair_index,
)
from .settlement_quote_binding import (
    quote_binding_context as _quote_binding_context,
)
from .settlement_quote_binding import (
    quote_binding_error as _quote_binding_error,
)
from .settlement_quote_binding import (
    validate_quote_binding_transport as _validate_quote_binding_transport,
)
from .settlement_replay_context import ReplayContext as _ReplayContext
from .settlement_replay_context import SettlementPreState as _SettlementPreState
from .settlement_replay_context import build_replay_context as _build_replay_context
from .settlement_replay_create_pool import replay_create_pool_fill as _replay_create_pool_fill
from .settlement_replay_index import SettlementIndex as _SettlementIndex
from .settlement_replay_index import (
    build_settlement_index as _build_settlement_index,
)

_MODE_STRONG_REPLAY = "strong_replay"
_MODE_STRONG_PROOF_CARRYING = "strong_proof_carrying"
_VALIDATION_MODES = frozenset({_MODE_STRONG_REPLAY, _MODE_STRONG_PROOF_CARRYING})
_FAIL_CLOSED_VALIDATOR_ERRORS = (
    TypeError,
    ValueError,
    ArithmeticError,
    LookupError,
    AttributeError,
    RuntimeError,
    AssertionError,
)


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
class _SwapReplayTarget:
    intent_id: str
    sender: PubKey
    recipient: PubKey
    pool_id: str
    pool: PoolState
    asset_in: AssetId
    asset_out: AssetId
    reserve_in: int
    reserve_out: int
    dir_is_0_to_1: bool


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
class _CowNettingReplayRequest:
    intent: Intent
    fill: Fill
    target: _SwapReplayTarget
    allow_cow_netting: bool


@dataclass(frozen=True)
class _CowNettingReplayAmounts:
    amount_in: int
    amount_out: int


@dataclass(frozen=True)
class _CowNettingIntentAmounts:
    amount_in: int
    min_out: int


@dataclass(frozen=True)
class _ProtocolFeeReplayConfig:
    share_bps: int
    recipient_pubkey: Optional[PubKey]


@dataclass(frozen=True)
class _StrongValidationRequest:
    settlement: Settlement
    intents: List[Intent]
    pre_state: _SettlementPreState
    mode: str
    allow_cow_netting: bool
    allow_snapshot_bound_quote_bindings: bool
    protocol_fee_share_bps: int
    protocol_fee_recipient_pubkey: Optional[PubKey]


@dataclass(frozen=True)
class _IntentReplayEnvironment:
    request: _StrongValidationRequest
    settlement_index: _SettlementIndex
    replay: _ReplayContext
    protocol_fee: _ProtocolFeeReplayConfig


@dataclass(frozen=True)
class _PoolIntentReplayRequest:
    intent: Intent
    fill: Fill
    pool_target: _PoolReplayTarget
    quote_pool_fp: object
    env: _IntentReplayEnvironment


@dataclass(frozen=True)
class _SwapReplayRequest:
    intent: Intent
    fill: Fill
    target: _SwapReplayTarget
    protocol_fee: _ProtocolFeeReplayConfig


@dataclass(frozen=True)
class _SwapExactInReplayInput:
    amount_in: int
    min_out: int


@dataclass(frozen=True)
class _SwapExactOutReplayInput:
    amount_out: int
    max_in: int


@dataclass(frozen=True)
class _SwapReplayAmounts:
    amount_in: int
    amount_out: int
    new_reserve_in: int
    new_reserve_out: int
    protocol_fee: int


@dataclass(frozen=True)
class _PoolReplayTarget:
    pool_id: str
    pool: PoolState
    recipient: PubKey


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
    replay: _ReplayContext,
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
    replay: _ReplayContext,
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


def _replay_add_liquidity_fill(
    *,
    intent: Intent,
    fill: Fill,
    target: _PoolReplayTarget,
    replay: _ReplayContext,
) -> Optional[str]:
    if target.pool.status != PoolStatus.ACTIVE:
        return f"pool not active for intent_id={intent.intent_id}: {target.pool.status}"

    replay_input, err = _parse_add_liquidity_replay_input(
        intent=intent,
        recipient=target.recipient,
        pool_id=target.pool_id,
    )
    if replay_input is None:
        return err or f"missing ADD_LIQUIDITY fields for intent_id={intent.intent_id}"

    try:
        amount0_used, amount1_used, lp_minted = add_liquidity(
            pool_state=target.pool,
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
        pool=target.pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    _record_add_liquidity_deltas(
        replay=replay,
        pool=target.pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    return None


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
    replay: _ReplayContext,
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
    replay: _ReplayContext,
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


def _replay_remove_liquidity_fill(
    *,
    intent: Intent,
    fill: Fill,
    target: _PoolReplayTarget,
    replay: _ReplayContext,
) -> Optional[str]:
    if target.pool.status != PoolStatus.ACTIVE:
        return f"pool not active for intent_id={intent.intent_id}: {target.pool.status}"

    replay_input, err = _parse_remove_liquidity_replay_input(
        intent=intent,
        recipient=target.recipient,
        pool_id=target.pool_id,
    )
    if replay_input is None:
        return err or f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent.intent_id}"

    try:
        amount0_out, amount1_out = remove_liquidity(
            pool_state=target.pool,
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
        pool=target.pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    _record_remove_liquidity_deltas(
        replay=replay,
        pool=target.pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    return None


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
    return _quote_binding_error(
        "quote receipt pool snapshot mismatch",
        **_quote_binding_context(intent),
        actual_pool_fingerprint=actual_pool_fp,
    )


def _swap_reserve_view(*, pool: PoolState, assets: _SwapAssetPair) -> _SwapReserveView:
    if assets.asset_in == pool.asset0 and assets.asset_out == pool.asset1:
        return _SwapReserveView(reserve_in=int(pool.reserve0), reserve_out=int(pool.reserve1), dir_is_0_to_1=True)
    return _SwapReserveView(reserve_in=int(pool.reserve1), reserve_out=int(pool.reserve0), dir_is_0_to_1=False)


def _build_swap_replay_target(
    *,
    intent: Intent,
    target: _PoolReplayTarget,
    quote_pool_fp: object,
) -> Tuple[Optional[_SwapReplayTarget], Optional[str]]:
    intent_id = intent.intent_id
    pool = target.pool
    assets, err = _parse_swap_asset_pair(intent)
    if assets is None:
        return None, err
    err = _validate_swap_pool_and_assets(intent_id=intent_id, pool=pool, assets=assets)
    if err is not None:
        return None, err
    err = _validate_swap_quote_pool_fingerprint(intent=intent, pool=pool, quote_pool_fp=quote_pool_fp)
    if err is not None:
        return None, err
    reserve_view = _swap_reserve_view(pool=pool, assets=assets)

    return (
        _SwapReplayTarget(
            intent_id=intent_id,
            sender=intent.sender_pubkey,
            recipient=target.recipient,
            pool_id=target.pool_id,
            pool=pool,
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
    target: _SwapReplayTarget,
    mode: str,
) -> Optional[str]:
    if mode != _MODE_STRONG_PROOF_CARRYING:
        return None
    if fill.reserve_in_before is None or fill.reserve_out_before is None:
        return f"missing swap witness reserves for intent_id={target.intent_id}"
    if int(fill.reserve_in_before) != int(target.reserve_in) or int(fill.reserve_out_before) != int(target.reserve_out):
        return f"swap witness reserve mismatch for intent_id={target.intent_id}"
    return None


def _replay_cow_netted_fill(
    *,
    request: _CowNettingReplayRequest,
    replay: _ReplayContext,
) -> Optional[str]:
    err = _validate_cow_netted_replay_preconditions(request)
    if err is not None:
        return err
    amounts, err = _parse_cow_netted_replay_amounts(request)
    if amounts is None:
        return err
    err = _apply_cow_netted_balance_replay(replay=replay, target=request.target, amounts=amounts)
    if err is not None:
        return err
    _record_cow_netted_balance_deltas(replay=replay, target=request.target, amounts=amounts)
    return None


def _validate_cow_netted_replay_preconditions(request: _CowNettingReplayRequest) -> Optional[str]:
    target = request.target
    if not request.allow_cow_netting:
        return f"COW_NETTED not allowed for intent_id={target.intent_id}"
    if request.intent.kind != IntentKind.SWAP_EXACT_IN:
        return f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={target.intent_id}"
    return None


def _parse_cow_netted_replay_amounts(
    request: _CowNettingReplayRequest,
) -> Tuple[Optional[_CowNettingReplayAmounts], Optional[str]]:
    intent_amounts, err = _parse_cow_netted_intent_amounts(request)
    if intent_amounts is None:
        return None, err
    return _parse_cow_netted_fill_amounts(request=request, intent_amounts=intent_amounts)


def _parse_cow_netted_intent_amounts(
    request: _CowNettingReplayRequest,
) -> Tuple[Optional[_CowNettingIntentAmounts], Optional[str]]:
    intent = request.intent
    target = request.target
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return None, f"invalid amount_in for intent_id={target.intent_id}"
    if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
        return None, f"invalid min_amount_out for intent_id={target.intent_id}"
    return _CowNettingIntentAmounts(amount_in=int(amount_in), min_out=int(min_out)), None


def _parse_cow_netted_fill_amounts(
    *,
    request: _CowNettingReplayRequest,
    intent_amounts: _CowNettingIntentAmounts,
) -> Tuple[Optional[_CowNettingReplayAmounts], Optional[str]]:
    fill = request.fill
    target = request.target
    if int(fill.fee_paid or 0) != 0:
        return None, f"COW_NETTED fee_paid must be 0: intent_id={target.intent_id}"
    if int(fill.amount_in_filled or 0) != intent_amounts.amount_in:
        return None, f"COW_NETTED amount_in_filled mismatch: intent_id={target.intent_id}"
    out_amt = int(fill.amount_out_filled or 0)
    if out_amt < intent_amounts.min_out:
        return None, f"COW_NETTED slippage: intent_id={target.intent_id}"
    return _CowNettingReplayAmounts(amount_in=intent_amounts.amount_in, amount_out=out_amt), None


def _apply_cow_netted_balance_replay(
    *,
    replay: _ReplayContext,
    target: _SwapReplayTarget,
    amounts: _CowNettingReplayAmounts,
) -> Optional[str]:
    try:
        replay.balances.subtract(target.sender, target.asset_in, amounts.amount_in)
        replay.balances.add(target.recipient, target.asset_out, amounts.amount_out)
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"COW_NETTED apply error for intent_id={target.intent_id}: {exc}"
    return None


def _record_cow_netted_balance_deltas(
    *,
    replay: _ReplayContext,
    target: _SwapReplayTarget,
    amounts: _CowNettingReplayAmounts,
) -> None:
    replay.bal_deltas.append(
        BalanceDelta(pubkey=target.sender, asset=target.asset_in, delta_add=0, delta_sub=amounts.amount_in)
    )
    replay.bal_deltas.append(
        BalanceDelta(pubkey=target.recipient, asset=target.asset_out, delta_add=amounts.amount_out, delta_sub=0)
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
    target: _SwapReplayTarget,
    replay_input: _SwapExactInReplayInput,
    protocol_fee: _ProtocolFeeReplayConfig,
) -> Tuple[Optional[_SwapReplayAmounts], Optional[str]]:
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
                _SwapReplayAmounts(
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
            _SwapReplayAmounts(
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
    target: _SwapReplayTarget,
    replay_input: _SwapExactInReplayInput,
    replay_amounts: _SwapReplayAmounts,
) -> Optional[str]:
    if int(fill.amount_in_filled or 0) != int(replay_input.amount_in):
        return f"swap amount_in_filled mismatch for intent_id={target.intent_id}"
    if int(fill.amount_out_filled or 0) != int(replay_amounts.amount_out):
        return f"swap amount_out_filled mismatch for intent_id={target.intent_id}"
    return None


def _check_swap_exact_in_slippage(
    *,
    target: _SwapReplayTarget,
    replay_input: _SwapExactInReplayInput,
    replay_amounts: _SwapReplayAmounts,
) -> Optional[str]:
    if int(replay_amounts.amount_out) < int(replay_input.min_out):
        return f"swap slippage for intent_id={target.intent_id}"
    return None


def _check_swap_fee_fields(
    *,
    fill: Fill,
    target: _SwapReplayTarget,
    fee_basis_amount: int,
    protocol_fee_paid: int,
) -> Optional[str]:
    fee = compute_fee_total(int(fee_basis_amount), int(target.pool.fee_bps))
    if int(fill.fee_paid or 0) != int(fee):
        return f"swap fee_paid mismatch for intent_id={target.intent_id}"
    if int(fill.protocol_fee_paid or 0) != int(protocol_fee_paid):
        return f"swap protocol_fee_paid mismatch for intent_id={target.intent_id}"
    return None


def _check_swap_exact_in_fill(
    *,
    fill: Fill,
    target: _SwapReplayTarget,
    replay_input: _SwapExactInReplayInput,
    replay_amounts: _SwapReplayAmounts,
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
    return _check_swap_fee_fields(
        fill=fill,
        target=target,
        fee_basis_amount=int(replay_input.amount_in),
        protocol_fee_paid=int(replay_amounts.protocol_fee),
    )


def _apply_swap_replay(
    *,
    replay: _ReplayContext,
    target: _SwapReplayTarget,
    replay_amounts: _SwapReplayAmounts,
    protocol_fee: _ProtocolFeeReplayConfig,
) -> Optional[str]:
    try:
        replay.balances.subtract(target.sender, target.asset_in, int(replay_amounts.amount_in))
        replay.balances.add(target.recipient, target.asset_out, int(replay_amounts.amount_out))
        if replay_amounts.protocol_fee:
            if protocol_fee.recipient_pubkey is None:
                return f"protocol fee recipient missing during replay for intent_id={target.intent_id}"
            replay.balances.add(protocol_fee.recipient_pubkey, target.asset_in, int(replay_amounts.protocol_fee))
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"swap apply error for intent_id={target.intent_id}: {exc}"

    if target.dir_is_0_to_1:
        target.pool.reserve0 = int(replay_amounts.new_reserve_in)
        target.pool.reserve1 = int(replay_amounts.new_reserve_out)
    else:
        target.pool.reserve1 = int(replay_amounts.new_reserve_in)
        target.pool.reserve0 = int(replay_amounts.new_reserve_out)
    return None


def _record_swap_replay_deltas(
    *,
    replay: _ReplayContext,
    target: _SwapReplayTarget,
    replay_amounts: _SwapReplayAmounts,
    protocol_fee: _ProtocolFeeReplayConfig,
) -> Optional[str]:
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=target.sender,
            asset=target.asset_in,
            delta_add=0,
            delta_sub=int(replay_amounts.amount_in),
        )
    )
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=target.recipient,
            asset=target.asset_out,
            delta_add=int(replay_amounts.amount_out),
            delta_sub=0,
        )
    )
    if replay_amounts.protocol_fee:
        if protocol_fee.recipient_pubkey is None:
            return f"protocol fee recipient missing during replay for intent_id={target.intent_id}"
        replay.bal_deltas.append(
            BalanceDelta(
                pubkey=protocol_fee.recipient_pubkey,
                asset=target.asset_in,
                delta_add=int(replay_amounts.protocol_fee),
                delta_sub=0,
            )
        )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=target.pool_id,
            asset=target.asset_in,
            delta_add=int(replay_amounts.amount_in) - int(replay_amounts.protocol_fee),
            delta_sub=0,
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=target.pool_id,
            asset=target.asset_out,
            delta_add=0,
            delta_sub=int(replay_amounts.amount_out),
        )
    )
    return None


def _replay_swap_exact_in_fill(
    *,
    request: _SwapReplayRequest,
    replay: _ReplayContext,
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

    err = _apply_swap_replay(
        replay=replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )
    if err is not None:
        return err

    return _record_swap_replay_deltas(
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
    target: _SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    protocol_fee: _ProtocolFeeReplayConfig,
) -> Tuple[Optional[_SwapReplayAmounts], Optional[str]]:
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
                _SwapReplayAmounts(
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
            _SwapReplayAmounts(
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
    target: _SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    replay_amounts: _SwapReplayAmounts,
) -> Optional[str]:
    if int(fill.amount_out_filled or 0) != int(replay_input.amount_out):
        return f"swap amount_out_filled mismatch for intent_id={target.intent_id}"
    if int(fill.amount_in_filled or 0) != int(replay_amounts.amount_in):
        return f"swap amount_in_filled mismatch for intent_id={target.intent_id}"
    return None


def _check_swap_exact_out_slippage(
    *,
    target: _SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    replay_amounts: _SwapReplayAmounts,
) -> Optional[str]:
    if int(replay_amounts.amount_in) > int(replay_input.max_in):
        return f"swap slippage for intent_id={target.intent_id}"
    return None


def _check_swap_exact_out_fill(
    *,
    fill: Fill,
    target: _SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    replay_amounts: _SwapReplayAmounts,
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
    return _check_swap_fee_fields(
        fill=fill,
        target=target,
        fee_basis_amount=int(replay_amounts.amount_in),
        protocol_fee_paid=int(replay_amounts.protocol_fee),
    )


def _replay_swap_exact_out_fill(
    *,
    request: _SwapReplayRequest,
    replay: _ReplayContext,
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

    err = _apply_swap_replay(
        replay=replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )
    if err is not None:
        return err

    return _record_swap_replay_deltas(
        replay=replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )


def _validate_replayed_payload(
    *,
    settlement: Settlement,
    replay: _ReplayContext,
    pre_state: _SettlementPreState,
) -> Tuple[bool, Optional[str]]:
    expected_balance = _aggregate_balance_deltas(replay.bal_deltas)
    expected_reserve = _aggregate_reserve_deltas(replay.res_deltas)
    expected_lp = _aggregate_lp_deltas(replay.lp_deltas)

    ok, err = _check_canonical_deltas(settlement)
    if not ok:
        return False, err

    if settlement.balance_deltas != expected_balance:
        return False, "balance_deltas mismatch vs replay"
    if settlement.reserve_deltas != expected_reserve:
        return False, "reserve_deltas mismatch vs replay"
    if settlement.lp_deltas != expected_lp:
        return False, "lp_deltas mismatch vs replay"

    got_events_norm = settlement.events or []
    if got_events_norm != replay.expected_events:
        return False, "events mismatch vs replay"

    # Defense-in-depth: ensure basic conservation/non-negativity in addition to replay checks.
    # This is essential when a fill type does not touch pool reserves (e.g. COW_NETTED),
    # where conservation must be enforced globally across balance deltas.
    ok_legacy, err_legacy = validate_settlement_legacy(
        settlement=settlement,
        pre_balances=pre_state.balances,
        pre_pools=pre_state.pools,
        pre_lp_balances=pre_state.lp_balances,
    )
    if not ok_legacy:
        return False, f"legacy validation failed: {err_legacy}"

    return True, None


def _replay_included_intents(env: _IntentReplayEnvironment) -> Tuple[bool, Optional[str]]:
    for intent_id, action in env.request.settlement.included_intents:
        err = _replay_included_intent(intent_id=intent_id, action=action, env=env)
        if err is not None:
            return False, err
    return True, None


def _replay_included_intent(
    *,
    intent_id: str,
    action: FillAction,
    env: _IntentReplayEnvironment,
) -> Optional[str]:
    intent = env.settlement_index.intents_by_id[intent_id]
    quote_binding_error = _validate_quote_binding_transport(
        intent,
        allow_snapshot_bound_quote_bindings=env.request.allow_snapshot_bound_quote_bindings,
    )
    if quote_binding_error is not None:
        return quote_binding_error
    if action == FillAction.REJECT:
        return None

    fill = env.settlement_index.fill_by_id[intent_id]
    recipient: PubKey = intent.get_field("recipient", intent.sender_pubkey)
    if not isinstance(recipient, str) or not recipient:
        return f"invalid recipient for intent_id={intent_id}"

    if intent.kind == IntentKind.CREATE_POOL:
        return _replay_create_pool_fill(intent=intent, fill=fill, replay=env.replay)

    pool_id = intent.get_field("pool_id")
    if not isinstance(pool_id, str) or not pool_id:
        return f"missing pool_id for intent_id={intent_id}"
    if pool_id not in env.replay.pools:
        return f"pool not found for intent_id={intent_id}: {pool_id}"

    pool_target = _PoolReplayTarget(pool_id=pool_id, pool=env.replay.pools[pool_id], recipient=recipient)
    return _replay_pool_intent(
        request=_PoolIntentReplayRequest(
            intent=intent,
            fill=fill,
            pool_target=pool_target,
            quote_pool_fp=intent.get_field("quote_pool_fingerprint"),
            env=env,
        ),
    )


def _replay_pool_intent(*, request: _PoolIntentReplayRequest) -> Optional[str]:
    if request.intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        return _replay_swap_intent(request=request)
    if request.intent.kind == IntentKind.ADD_LIQUIDITY:
        return _replay_add_liquidity_fill(
            intent=request.intent,
            fill=request.fill,
            target=request.pool_target,
            replay=request.env.replay,
        )
    if request.intent.kind == IntentKind.REMOVE_LIQUIDITY:
        return _replay_remove_liquidity_fill(
            intent=request.intent,
            fill=request.fill,
            target=request.pool_target,
            replay=request.env.replay,
        )
    return f"unsupported intent kind for strong validation: {request.intent.kind}"


def _replay_swap_intent(*, request: _PoolIntentReplayRequest) -> Optional[str]:
    swap_target, err = _build_swap_replay_target(
        intent=request.intent,
        target=request.pool_target,
        quote_pool_fp=request.quote_pool_fp,
    )
    if swap_target is None:
        return err or f"invalid asset_in/out for intent_id={request.intent.intent_id}"

    if request.fill.reason == "COW_NETTED":
        return _replay_cow_netted_fill(
            request=_CowNettingReplayRequest(
                intent=request.intent,
                fill=request.fill,
                target=swap_target,
                allow_cow_netting=request.env.request.allow_cow_netting,
            ),
            replay=request.env.replay,
        )

    err = _check_swap_reserve_witness(fill=request.fill, target=swap_target, mode=request.env.request.mode)
    if err is not None:
        return err
    swap_request = _SwapReplayRequest(
        intent=request.intent,
        fill=request.fill,
        target=swap_target,
        protocol_fee=request.env.protocol_fee,
    )
    if request.intent.kind == IntentKind.SWAP_EXACT_IN:
        return _replay_swap_exact_in_fill(request=swap_request, replay=request.env.replay)
    return _replay_swap_exact_out_fill(request=swap_request, replay=request.env.replay)


def _validate_strong_request_preflight(request: _StrongValidationRequest) -> Optional[str]:
    if request.mode not in _VALIDATION_MODES:
        return f"unsupported validation mode: {request.mode!r}"
    if not is_strict_int(request.protocol_fee_share_bps) or not (0 <= request.protocol_fee_share_bps <= 10000):
        return "protocol_fee_share_bps must be an int in [0, 10000]"
    if request.protocol_fee_share_bps > 0 and not request.protocol_fee_recipient_pubkey:
        return "protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0"
    return None


def _build_validated_settlement_index(
    request: _StrongValidationRequest,
) -> Tuple[Optional[_SettlementIndex], Optional[str]]:
    settlement_index, err_index = _build_settlement_index(
        settlement=request.settlement,
        intents=request.intents,
    )
    if settlement_index is None:
        return None, err_index or "settlement index construction failed"

    ok_cow, err_cow = _validate_cow_pair_index(
        settlement=request.settlement,
        intents_by_id=settlement_index.intents_by_id,
        fill_by_id=settlement_index.fill_by_id,
        allow_cow_netting=request.allow_cow_netting,
    )
    if not ok_cow:
        return None, err_cow
    return settlement_index, None


def _build_intent_replay_environment(
    *,
    request: _StrongValidationRequest,
    settlement_index: _SettlementIndex,
) -> _IntentReplayEnvironment:
    replay = _build_replay_context(
        pre_balances=request.pre_state.balances,
        pre_pools=request.pre_state.pools,
        pre_lp_balances=request.pre_state.lp_balances,
    )
    return _IntentReplayEnvironment(
        request=request,
        settlement_index=settlement_index,
        replay=replay,
        protocol_fee=_ProtocolFeeReplayConfig(
            share_bps=int(request.protocol_fee_share_bps),
            recipient_pubkey=request.protocol_fee_recipient_pubkey,
        ),
    )


def validate_settlement_strong(
    *,
    settlement: Settlement,
    intents: List[Intent],
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable] = None,
    mode: str = _MODE_STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> Tuple[bool, Optional[str]]:
    """
    Fail-closed wrapper around the strong validator implementation.

    This validator is used on untrusted settlement proposals; it must return `(False, reason)`
    rather than crash on malformed inputs.
    """
    try:
        request = _StrongValidationRequest(
            settlement=settlement,
            intents=intents,
            pre_state=_SettlementPreState(
                balances=pre_balances,
                pools=pre_pools,
                lp_balances=pre_lp_balances,
            ),
            mode=mode,
            allow_cow_netting=allow_cow_netting,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        )
        return _validate_settlement_strong_impl(request=request)
    except _FAIL_CLOSED_VALIDATOR_ERRORS as exc:
        detail = str(exc).strip()
        if "\n" in detail or "\r" in detail:
            detail = " ".join(detail.split())
        if len(detail) > 200:
            detail = detail[:200]
        if detail:
            return False, f"strong validator crashed: {type(exc).__name__}: {detail}"
        return False, f"strong validator crashed: {type(exc).__name__}"


def _validate_settlement_strong_impl(
    *,
    request: _StrongValidationRequest,
) -> Tuple[bool, Optional[str]]:
    """
    Strong settlement validation.

    This is intended to be used in `dex.step` as a fail-closed acceptance gate.
    """
    err = _validate_strong_request_preflight(request)
    if err is not None:
        return False, err
    settlement_index, err = _build_validated_settlement_index(request)
    if settlement_index is None:
        return False, err
    env = _build_intent_replay_environment(request=request, settlement_index=settlement_index)
    ok_replay, err_replay = _replay_included_intents(env)
    if not ok_replay:
        return False, err_replay

    return _validate_replayed_payload(
        settlement=request.settlement,
        replay=env.replay,
        pre_state=request.pre_state,
    )

