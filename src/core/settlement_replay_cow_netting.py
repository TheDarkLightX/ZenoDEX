"""COW-netted balance replay for strong settlement validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from ..state.balances import AssetId, PubKey
from ..state.intents import Intent, IntentKind
from .settlement import BalanceDelta, Fill
from .settlement_replay_context import ReplayContext


@dataclass(frozen=True)
class CowNettingReplayRequest:
    intent: Intent
    fill: Fill
    intent_id: str
    sender: PubKey
    recipient: PubKey
    asset_in: AssetId
    asset_out: AssetId
    allow_cow_netting: bool


@dataclass(frozen=True)
class _CowNettingReplayAmounts:
    amount_in: int
    amount_out: int


@dataclass(frozen=True)
class _CowNettingIntentAmounts:
    amount_in: int
    min_out: int


def replay_cow_netted_fill(
    *,
    request: CowNettingReplayRequest,
    replay: ReplayContext,
) -> Optional[str]:
    err = _validate_cow_netted_replay_preconditions(request)
    if err is not None:
        return err
    amounts, err = _parse_cow_netted_replay_amounts(request)
    if amounts is None:
        return err
    err = _apply_cow_netted_balance_replay(replay=replay, request=request, amounts=amounts)
    if err is not None:
        return err
    _record_cow_netted_balance_deltas(replay=replay, request=request, amounts=amounts)
    return None


def _validate_cow_netted_replay_preconditions(request: CowNettingReplayRequest) -> Optional[str]:
    if not request.allow_cow_netting:
        return f"COW_NETTED not allowed for intent_id={request.intent_id}"
    if request.intent.kind != IntentKind.SWAP_EXACT_IN:
        return f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={request.intent_id}"
    return None


def _parse_cow_netted_replay_amounts(
    request: CowNettingReplayRequest,
) -> Tuple[Optional[_CowNettingReplayAmounts], Optional[str]]:
    intent_amounts, err = _parse_cow_netted_intent_amounts(request)
    if intent_amounts is None:
        return None, err
    return _parse_cow_netted_fill_amounts(request=request, intent_amounts=intent_amounts)


def _parse_cow_netted_intent_amounts(
    request: CowNettingReplayRequest,
) -> Tuple[Optional[_CowNettingIntentAmounts], Optional[str]]:
    amount_in = request.intent.get_field("amount_in")
    min_out = request.intent.get_field("min_amount_out", 0)
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return None, f"invalid amount_in for intent_id={request.intent_id}"
    if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
        return None, f"invalid min_amount_out for intent_id={request.intent_id}"
    return _CowNettingIntentAmounts(amount_in=int(amount_in), min_out=int(min_out)), None


def _parse_cow_netted_fill_amounts(
    *,
    request: CowNettingReplayRequest,
    intent_amounts: _CowNettingIntentAmounts,
) -> Tuple[Optional[_CowNettingReplayAmounts], Optional[str]]:
    fill = request.fill
    if int(fill.fee_paid or 0) != 0:
        return None, f"COW_NETTED fee_paid must be 0: intent_id={request.intent_id}"
    if int(fill.amount_in_filled or 0) != intent_amounts.amount_in:
        return None, f"COW_NETTED amount_in_filled mismatch: intent_id={request.intent_id}"
    out_amt = int(fill.amount_out_filled or 0)
    if out_amt < intent_amounts.min_out:
        return None, f"COW_NETTED slippage: intent_id={request.intent_id}"
    return _CowNettingReplayAmounts(amount_in=intent_amounts.amount_in, amount_out=out_amt), None


def _apply_cow_netted_balance_replay(
    *,
    replay: ReplayContext,
    request: CowNettingReplayRequest,
    amounts: _CowNettingReplayAmounts,
) -> Optional[str]:
    try:
        replay.balances.subtract(request.sender, request.asset_in, amounts.amount_in)
        replay.balances.add(request.recipient, request.asset_out, amounts.amount_out)
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"COW_NETTED apply error for intent_id={request.intent_id}: {exc}"
    return None


def _record_cow_netted_balance_deltas(
    *,
    replay: ReplayContext,
    request: CowNettingReplayRequest,
    amounts: _CowNettingReplayAmounts,
) -> None:
    replay.bal_deltas.append(
        BalanceDelta(pubkey=request.sender, asset=request.asset_in, delta_add=0, delta_sub=amounts.amount_in)
    )
    replay.bal_deltas.append(
        BalanceDelta(pubkey=request.recipient, asset=request.asset_out, delta_add=amounts.amount_out, delta_sub=0)
    )
