"""Shared swap replay accounting for strong settlement validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from ..state.balances import AssetId, PubKey
from ..state.pools import PoolState
from .cpmm import compute_fee_total
from .settlement import BalanceDelta, Fill, ReserveDelta
from .settlement_replay_context import ReplayContext


@dataclass(frozen=True)
class ProtocolFeeReplayConfig:
    share_bps: int
    recipient_pubkey: Optional[PubKey]


@dataclass(frozen=True)
class SwapReplayTarget:
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
class SwapReplayAmounts:
    amount_in: int
    amount_out: int
    new_reserve_in: int
    new_reserve_out: int
    protocol_fee: int


def read_optional_fill_int(
    value: object,
    *,
    field_name: str,
    intent_id: str,
) -> tuple[Optional[int], Optional[str]]:
    if value is None:
        return 0, None
    if not isinstance(value, int) or isinstance(value, bool):
        return None, f"swap {field_name} must be int for intent_id={intent_id}"
    if value < 0:
        return None, f"swap {field_name} must be non-negative for intent_id={intent_id}"
    return int(value), None


def check_swap_fee_fields(
    *,
    fill: Fill,
    target: SwapReplayTarget,
    fee_basis_amount: int,
    protocol_fee_paid: int,
) -> Optional[str]:
    fee = compute_fee_total(int(fee_basis_amount), int(target.pool.fee_bps))
    fee_paid, err = read_optional_fill_int(
        fill.fee_paid,
        field_name="fee_paid",
        intent_id=target.intent_id,
    )
    if err is not None:
        return err
    protocol_fee_paid_fill, err = read_optional_fill_int(
        fill.protocol_fee_paid,
        field_name="protocol_fee_paid",
        intent_id=target.intent_id,
    )
    if err is not None:
        return err
    if fee_paid != int(fee):
        return f"swap fee_paid mismatch for intent_id={target.intent_id}"
    if protocol_fee_paid_fill != int(protocol_fee_paid):
        return f"swap protocol_fee_paid mismatch for intent_id={target.intent_id}"
    return None


def apply_swap_replay(
    *,
    replay: ReplayContext,
    target: SwapReplayTarget,
    replay_amounts: SwapReplayAmounts,
    protocol_fee: ProtocolFeeReplayConfig,
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


def record_swap_replay_deltas(
    *,
    replay: ReplayContext,
    target: SwapReplayTarget,
    replay_amounts: SwapReplayAmounts,
    protocol_fee: ProtocolFeeReplayConfig,
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
