"""Hop replay engine for route quote receipt verification."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Callable, Tuple

from ..core.quote_receipt_gate_contract import route_quote_receipt_hop_replay_error
from ..core.quote_receipt_gates import evaluate_route_quote_receipt_hop_replay_gate
from ..state.pools import PoolState

ReserveLookup = Callable[..., Tuple[int, int] | None]
SwapQuote = Callable[..., tuple[int, tuple[int, int]]]


@dataclass(frozen=True)
class _ReceiptHopData:
    pool_id: str
    pool: PoolState
    asset_in: str
    asset_out: str
    amount_in: int
    amount_out: int


@dataclass(frozen=True)
class _HopDirection:
    forward_direction: bool
    direction_ok: bool
    reserve_in: int
    reserve_out: int


@dataclass(frozen=True)
class _HopSwapReplay:
    swap_ok: bool
    quote_matches: bool
    next_reserve_in: int
    next_reserve_out: int


def _resolve_hop_direction(
    hop_data: _ReceiptHopData,
    *,
    reserve_lookup: ReserveLookup,
) -> _HopDirection:
    pool = hop_data.pool
    forward_direction = bool(hop_data.asset_in == pool.asset0 and hop_data.asset_out == pool.asset1)
    reverse_direction = bool(hop_data.asset_in == pool.asset1 and hop_data.asset_out == pool.asset0)
    reserves = reserve_lookup(pool, asset_in=hop_data.asset_in, asset_out=hop_data.asset_out)
    if not (forward_direction or reverse_direction) or reserves is None:
        return _HopDirection(
            forward_direction=forward_direction,
            direction_ok=False,
            reserve_in=0,
            reserve_out=0,
        )
    reserve_in, reserve_out = reserves
    return _HopDirection(
        forward_direction=forward_direction,
        direction_ok=True,
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
    )


def _replay_hop_swap(
    *,
    kind: str,
    direction: _HopDirection,
    hop_data: _ReceiptHopData,
    swap_exact_in: SwapQuote,
    swap_exact_out: SwapQuote,
) -> _HopSwapReplay:
    if not direction.direction_ok:
        return _HopSwapReplay(
            swap_ok=False,
            quote_matches=False,
            next_reserve_in=0,
            next_reserve_out=0,
        )
    try:
        if kind == "exact_in":
            quoted_out, next_reserves = swap_exact_in(
                hop_data.pool,
                reserve_in=int(direction.reserve_in),
                reserve_out=int(direction.reserve_out),
                amount_in=int(hop_data.amount_in),
            )
            quote_matches = int(quoted_out) == int(hop_data.amount_out)
        else:
            quoted_in, next_reserves = swap_exact_out(
                hop_data.pool,
                reserve_in=int(direction.reserve_in),
                reserve_out=int(direction.reserve_out),
                amount_out=int(hop_data.amount_out),
            )
            quote_matches = int(quoted_in) == int(hop_data.amount_in)
    except (TypeError, ValueError, OverflowError):
        return _HopSwapReplay(
            swap_ok=False,
            quote_matches=False,
            next_reserve_in=0,
            next_reserve_out=0,
        )
    next_reserve_in, next_reserve_out = next_reserves
    return _HopSwapReplay(
        swap_ok=True,
        quote_matches=bool(quote_matches),
        next_reserve_in=int(next_reserve_in),
        next_reserve_out=int(next_reserve_out),
    )


def replay_and_apply_hop(
    *,
    kind: str,
    hop_data: _ReceiptHopData,
    reserve_lookup: ReserveLookup,
    swap_exact_in: SwapQuote,
    swap_exact_out: SwapQuote,
) -> Tuple[bool, str, PoolState | None]:
    direction = _resolve_hop_direction(hop_data, reserve_lookup=reserve_lookup)
    swap = _replay_hop_swap(
        kind=kind,
        direction=direction,
        hop_data=hop_data,
        swap_exact_in=swap_exact_in,
        swap_exact_out=swap_exact_out,
    )

    replay = evaluate_route_quote_receipt_hop_replay_gate(
        direction_ok=direction.direction_ok,
        forward_direction=direction.forward_direction,
        swap_ok=swap.swap_ok,
        quote_matches=swap.quote_matches,
        next_reserve_in=swap.next_reserve_in,
        next_reserve_out=swap.next_reserve_out,
    )
    if not replay.replay_ok:
        return False, route_quote_receipt_hop_replay_error(replay), None
    return True, "ok", replace(hop_data.pool, reserve0=int(replay.next_reserve0), reserve1=int(replay.next_reserve1))
