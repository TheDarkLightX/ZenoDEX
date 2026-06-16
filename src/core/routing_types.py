"""Shared route quote data model and deterministic ordering key."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple

from ..state.balances import Amount, AssetId


@dataclass(frozen=True)
class RouteHop:
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    amount_out: Amount


@dataclass(frozen=True)
class RouteLeg:
    hops: Tuple[RouteHop, ...]
    amount_in: Amount
    amount_out: Amount


@dataclass(frozen=True)
class RouteQuote:
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    amount_out: Amount
    legs: Tuple[RouteLeg, ...]


def quote_key(quote: RouteQuote) -> Tuple[int, int, str, str, str]:
    """Canonical route tie-break key used by exact-in and exact-out routing."""
    hop_count = sum(len(leg.hops) for leg in quote.legs)
    leg_count = len(quote.legs)
    pool_seq = ";".join(",".join(hop.pool_id for hop in leg.hops) for leg in quote.legs)
    mid = ""
    if leg_count == 1 and hop_count == 2:
        mid = quote.legs[0].hops[0].asset_out
    return (int(hop_count), int(leg_count), pool_seq, mid, quote.asset_out)
