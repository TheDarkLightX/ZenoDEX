"""Local state application helpers for accepted batch-clearing fills."""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional

from ..state.balances import BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import PoolState
from .settlement import BalanceDelta, Fill, LPDelta, ReserveDelta
from .settlement_fill_fields import read_optional_non_negative_fill_int


@dataclass(frozen=True)
class _FilledIntentLocalContext:
    pool_id: str
    pool_state: PoolState
    balances: BalanceTable
    lp_balances: LPTable
    balance_deltas: List[BalanceDelta]
    reserve_deltas: List[ReserveDelta]
    lp_deltas: List[LPDelta]
    protocol_fee_recipient_pubkey: Optional[PubKey] = None


@dataclass(frozen=True)
class _FilledIntentLocalApplyRequest:
    intent: Intent
    fill: Fill
    context: _FilledIntentLocalContext


@dataclass(frozen=True)
class _SwapFillAmounts:
    asset_in: str
    asset_out: str
    amount_in: int
    amount_out: int
    protocol_fee: int

    @property
    def reserve_amount_in(self) -> int:
        return int(self.amount_in - self.protocol_fee)


@dataclass(frozen=True)
class _SwapBalanceActors:
    sender: PubKey
    recipient: PubKey
    fee_recipient: PubKey | None = None


@dataclass(frozen=True)
class _SwapLocalApplyRequest:
    intent: Intent
    fill: Fill
    context: _FilledIntentLocalContext
    sender: PubKey
    recipient: PubKey


def _apply_swap_fill_to_locals(
    request: _SwapLocalApplyRequest,
) -> None:
    amounts = _read_swap_fill_amounts(intent=request.intent, fill=request.fill)
    actors = _apply_swap_balance_mutations(amounts=amounts, request=request)
    _append_swap_balance_deltas(
        amounts=amounts,
        context=request.context,
        actors=actors,
    )

    # CoW-style netting transfers balances directly and leaves pool reserves unchanged.
    if request.fill.reason == "COW_NETTED":
        return
    _apply_swap_reserve_mutations(amounts=amounts, context=request.context)


def _read_swap_fill_amounts(*, intent: Intent, fill: Fill) -> _SwapFillAmounts:
    return _SwapFillAmounts(
        asset_in=intent.get_field("asset_in"),
        asset_out=intent.get_field("asset_out"),
        amount_in=_read_local_fill_int(
            fill.amount_in_filled,
            operation="SWAP",
            field_name="amount_in_filled",
            fill=fill,
        ),
        amount_out=_read_local_fill_int(
            fill.amount_out_filled,
            operation="SWAP",
            field_name="amount_out_filled",
            fill=fill,
        ),
        protocol_fee=_read_local_fill_int(
            fill.protocol_fee_paid,
            operation="SWAP",
            field_name="protocol_fee_paid",
            fill=fill,
        ),
    )


def _apply_swap_balance_mutations(
    *,
    amounts: _SwapFillAmounts,
    request: _SwapLocalApplyRequest,
) -> _SwapBalanceActors:
    context = request.context
    sender = request.sender
    recipient = request.recipient
    context.balances.subtract(sender, amounts.asset_in, amounts.amount_in)
    context.balances.add(recipient, amounts.asset_out, amounts.amount_out)
    if not amounts.protocol_fee:
        return _SwapBalanceActors(sender=sender, recipient=recipient)
    if not context.protocol_fee_recipient_pubkey:
        raise ValueError("protocol_fee_recipient_pubkey is required for protocol fee capture")
    fee_recipient = context.protocol_fee_recipient_pubkey
    context.balances.add(fee_recipient, amounts.asset_in, amounts.protocol_fee)
    return _SwapBalanceActors(sender=sender, recipient=recipient, fee_recipient=fee_recipient)


def _append_swap_balance_deltas(
    *,
    amounts: _SwapFillAmounts,
    context: _FilledIntentLocalContext,
    actors: _SwapBalanceActors,
) -> None:
    context.balance_deltas.append(
        BalanceDelta(pubkey=actors.sender, asset=amounts.asset_in, delta_add=0, delta_sub=amounts.amount_in)
    )
    context.balance_deltas.append(
        BalanceDelta(pubkey=actors.recipient, asset=amounts.asset_out, delta_add=amounts.amount_out, delta_sub=0)
    )
    if amounts.protocol_fee:
        if actors.fee_recipient is None:
            raise ValueError("protocol_fee_recipient_pubkey is required for protocol fee delta")
        context.balance_deltas.append(
            BalanceDelta(
                pubkey=actors.fee_recipient,
                asset=amounts.asset_in,
                delta_add=amounts.protocol_fee,
                delta_sub=0,
            )
        )


def _apply_swap_reserve_mutations(
    *,
    amounts: _SwapFillAmounts,
    context: _FilledIntentLocalContext,
) -> None:
    context.reserve_deltas.append(
        ReserveDelta(pool_id=context.pool_id, asset=amounts.asset_in, delta_add=amounts.reserve_amount_in, delta_sub=0)
    )
    context.reserve_deltas.append(
        ReserveDelta(pool_id=context.pool_id, asset=amounts.asset_out, delta_add=0, delta_sub=amounts.amount_out)
    )

    if amounts.asset_in == context.pool_state.asset0:
        context.pool_state.reserve0 += amounts.reserve_amount_in
        context.pool_state.reserve1 -= amounts.amount_out
    else:
        context.pool_state.reserve1 += amounts.reserve_amount_in
        context.pool_state.reserve0 -= amounts.amount_out


def _apply_add_liquidity_fill_to_locals(
    fill: Fill,
    context: _FilledIntentLocalContext,
    *,
    sender: PubKey,
    recipient: PubKey,
) -> None:
    amount0_used = _read_local_fill_int(
        fill.amount0_used,
        operation="ADD_LIQUIDITY",
        field_name="amount0_used",
        fill=fill,
    )
    amount1_used = _read_local_fill_int(
        fill.amount1_used,
        operation="ADD_LIQUIDITY",
        field_name="amount1_used",
        fill=fill,
    )
    lp_minted = _read_local_fill_int(
        fill.lp_minted,
        operation="ADD_LIQUIDITY",
        field_name="lp_minted",
        fill=fill,
    )

    context.balances.subtract(sender, context.pool_state.asset0, amount0_used)
    context.balances.subtract(sender, context.pool_state.asset1, amount1_used)
    context.lp_balances.add(recipient, context.pool_id, lp_minted)

    context.balance_deltas.append(
        BalanceDelta(pubkey=sender, asset=context.pool_state.asset0, delta_add=0, delta_sub=amount0_used)
    )
    context.balance_deltas.append(
        BalanceDelta(pubkey=sender, asset=context.pool_state.asset1, delta_add=0, delta_sub=amount1_used)
    )
    context.reserve_deltas.append(
        ReserveDelta(pool_id=context.pool_id, asset=context.pool_state.asset0, delta_add=amount0_used, delta_sub=0)
    )
    context.reserve_deltas.append(
        ReserveDelta(pool_id=context.pool_id, asset=context.pool_state.asset1, delta_add=amount1_used, delta_sub=0)
    )
    context.lp_deltas.append(LPDelta(pubkey=recipient, pool_id=context.pool_id, delta_add=lp_minted, delta_sub=0))

    context.pool_state.reserve0 += amount0_used
    context.pool_state.reserve1 += amount1_used
    context.pool_state.lp_supply += lp_minted


def _apply_remove_liquidity_fill_to_locals(
    fill: Fill,
    context: _FilledIntentLocalContext,
    *,
    sender: PubKey,
    recipient: PubKey,
) -> None:
    lp_burned = _read_local_fill_int(
        fill.lp_burned,
        operation="REMOVE_LIQUIDITY",
        field_name="lp_burned",
        fill=fill,
    )
    amount0_out = _read_local_fill_int(
        fill.amount0_out,
        operation="REMOVE_LIQUIDITY",
        field_name="amount0_out",
        fill=fill,
    )
    amount1_out = _read_local_fill_int(
        fill.amount1_out,
        operation="REMOVE_LIQUIDITY",
        field_name="amount1_out",
        fill=fill,
    )

    context.lp_balances.subtract(sender, context.pool_id, lp_burned)
    context.balances.add(recipient, context.pool_state.asset0, amount0_out)
    context.balances.add(recipient, context.pool_state.asset1, amount1_out)

    context.lp_deltas.append(LPDelta(pubkey=sender, pool_id=context.pool_id, delta_add=0, delta_sub=lp_burned))
    context.balance_deltas.append(
        BalanceDelta(pubkey=recipient, asset=context.pool_state.asset0, delta_add=amount0_out, delta_sub=0)
    )
    context.balance_deltas.append(
        BalanceDelta(pubkey=recipient, asset=context.pool_state.asset1, delta_add=amount1_out, delta_sub=0)
    )
    context.reserve_deltas.append(
        ReserveDelta(pool_id=context.pool_id, asset=context.pool_state.asset0, delta_add=0, delta_sub=amount0_out)
    )
    context.reserve_deltas.append(
        ReserveDelta(pool_id=context.pool_id, asset=context.pool_state.asset1, delta_add=0, delta_sub=amount1_out)
    )

    context.pool_state.reserve0 -= amount0_out
    context.pool_state.reserve1 -= amount1_out
    context.pool_state.lp_supply -= lp_burned


def _read_local_fill_int(value: object, *, operation: str, field_name: str, fill: Fill) -> int:
    parsed, err = read_optional_non_negative_fill_int(
        value,
        operation=operation,
        field_name=field_name,
        intent_id=fill.intent_id,
    )
    if err is not None:
        raise TypeError(err)
    return int(parsed)


def _apply_filled_intent_to_locals_with_context(
    intent: Intent,
    fill: Fill,
    context: _FilledIntentLocalContext,
) -> None:
    sender = intent.sender_pubkey
    recipient = intent.get_field("recipient", sender)

    if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        _apply_swap_fill_to_locals(
            _SwapLocalApplyRequest(
                intent=intent,
                fill=fill,
                context=context,
                sender=sender,
                recipient=recipient,
            )
        )
        return

    if intent.kind == IntentKind.ADD_LIQUIDITY:
        _apply_add_liquidity_fill_to_locals(fill, context, sender=sender, recipient=recipient)
        return

    if intent.kind == IntentKind.REMOVE_LIQUIDITY:
        _apply_remove_liquidity_fill_to_locals(fill, context, sender=sender, recipient=recipient)
        return

    raise ValueError(f"Unsupported intent kind for fill application: {intent.kind}")
