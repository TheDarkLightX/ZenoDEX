from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from ...core.split_routing_dispatch import (
    ExactOutRouteCanonicalKey,
    SplitManyPoolsExactOutQuote,
    exact_out_route_canonical_key,
)


@dataclass(frozen=True)
class ExactOutRouteCanonicalSelectionCandidate:
    candidate_index: int
    quote: SplitManyPoolsExactOutQuote
    route_key: ExactOutRouteCanonicalKey
    route_key_rank_u64: int

    def __post_init__(self) -> None:
        if not isinstance(self.candidate_index, int) or isinstance(self.candidate_index, bool):
            raise TypeError("candidate_index must be an int")
        if self.candidate_index < 0:
            raise ValueError("candidate_index must be non-negative")
        if not isinstance(self.quote, SplitManyPoolsExactOutQuote):
            raise TypeError("quote must be a SplitManyPoolsExactOutQuote")
        if not isinstance(self.route_key, ExactOutRouteCanonicalKey):
            raise TypeError("route_key must be an ExactOutRouteCanonicalKey")
        if not isinstance(self.route_key_rank_u64, int) or isinstance(self.route_key_rank_u64, bool):
            raise TypeError("route_key_rank_u64 must be an int")
        if self.route_key_rank_u64 < 0 or self.route_key_rank_u64 > 0xFFFFFFFFFFFFFFFF:
            raise ValueError("route_key_rank_u64 out of range")


@dataclass(frozen=True)
class ExactOutRouteCanonicalSelection:
    candidates: tuple[ExactOutRouteCanonicalSelectionCandidate, ...]
    winner: ExactOutRouteCanonicalSelectionCandidate

    def __post_init__(self) -> None:
        if not self.candidates:
            raise ValueError("candidates must be non-empty")
        if not isinstance(self.winner, ExactOutRouteCanonicalSelectionCandidate):
            raise TypeError("winner must be an ExactOutRouteCanonicalSelectionCandidate")


def select_exact_out_route_canonical_winner(
    quotes: Sequence[SplitManyPoolsExactOutQuote],
) -> ExactOutRouteCanonicalSelection:
    if not isinstance(quotes, Sequence):
        raise TypeError("quotes must be a sequence")
    if not quotes:
        raise ValueError("quotes must be non-empty")

    indexed_keys = [
        (int(index), quote, exact_out_route_canonical_key(quote))
        for index, quote in enumerate(quotes)
    ]
    unique_keys = sorted({route_key for _index, _quote, route_key in indexed_keys})
    rank_by_key = {route_key: rank for rank, route_key in enumerate(unique_keys)}

    candidates = tuple(
        ExactOutRouteCanonicalSelectionCandidate(
            candidate_index=index,
            quote=quote,
            route_key=route_key,
            route_key_rank_u64=int(rank_by_key[route_key]),
        )
        for index, quote, route_key in indexed_keys
    )
    winner = min(candidates, key=lambda candidate: (candidate.route_key_rank_u64, candidate.candidate_index))
    return ExactOutRouteCanonicalSelection(candidates=candidates, winner=winner)
