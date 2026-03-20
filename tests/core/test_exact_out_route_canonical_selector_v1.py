from __future__ import annotations

import pytest

from src.core.split_routing_dispatch import SplitLegExactOutQuote, SplitManyPoolsExactOutQuote
from src.kernels.python.exact_out_route_canonical_selector_v1 import (
    select_exact_out_route_canonical_winner,
)


def _quote_one_leg() -> SplitManyPoolsExactOutQuote:
    return SplitManyPoolsExactOutQuote(
        amount_out_total=10,
        amount_in_total=11,
        legs=(SplitLegExactOutQuote(pool_id="pool_b", amount_out=10, amount_in=11),),
    )


def _quote_two_legs_lex_low() -> SplitManyPoolsExactOutQuote:
    return SplitManyPoolsExactOutQuote(
        amount_out_total=10,
        amount_in_total=11,
        legs=(
            SplitLegExactOutQuote(pool_id="pool_a", amount_out=4, amount_in=4),
            SplitLegExactOutQuote(pool_id="pool_c", amount_out=6, amount_in=7),
        ),
    )


def _quote_two_legs_lex_high() -> SplitManyPoolsExactOutQuote:
    return SplitManyPoolsExactOutQuote(
        amount_out_total=10,
        amount_in_total=11,
        legs=(
            SplitLegExactOutQuote(pool_id="pool_b", amount_out=4, amount_in=4),
            SplitLegExactOutQuote(pool_id="pool_c", amount_out=6, amount_in=7),
        ),
    )


def test_exact_out_route_canonical_selector_picks_argmin_under_route_key() -> None:
    selection = select_exact_out_route_canonical_winner(
        [_quote_two_legs_lex_high(), _quote_one_leg(), _quote_two_legs_lex_low()]
    )

    assert selection.winner.candidate_index == 1
    assert selection.winner.quote == _quote_one_leg()
    assert selection.winner.route_key_rank_u64 == 0
    assert [candidate.route_key_rank_u64 for candidate in selection.candidates] == [2, 0, 1]


def test_exact_out_route_canonical_selector_breaks_duplicate_key_ties_by_candidate_index() -> None:
    duplicate_a = _quote_one_leg()
    duplicate_b = _quote_one_leg()

    selection = select_exact_out_route_canonical_winner([duplicate_b, duplicate_a])

    assert selection.winner.candidate_index == 0
    assert selection.winner.route_key_rank_u64 == 0
    assert [candidate.route_key_rank_u64 for candidate in selection.candidates] == [0, 0]


def test_exact_out_route_canonical_selector_requires_nonempty_sequence() -> None:
    with pytest.raises(ValueError, match="quotes must be non-empty"):
        select_exact_out_route_canonical_winner([])
