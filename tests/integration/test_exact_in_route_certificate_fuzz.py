from __future__ import annotations

import importlib.util

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import given, settings

from src.core.routing import RouteHop, RouteLeg, RouteQuote
from src.integration.exact_in_route_certificate import (
    build_exact_in_route_canonical_certificate,
    build_exact_in_route_rank_projection_packet,
    compute_exact_in_route_rank_projection,
    exact_in_route_canonical_key,
    verify_exact_in_route_canonical_certificate,
)


ASSET = st.sampled_from(["A", "B", "C", "D"])
POOL = st.sampled_from(["p0", "p1", "p2", "p3", "p4"])
AMOUNT_IN = 100


@st.composite
def _route_quote(draw) -> RouteQuote:
    route_kind = draw(st.sampled_from(["direct", "twohop", "split2"]))
    amount_out = draw(st.integers(min_value=1, max_value=500))
    asset_out = draw(ASSET.filter(lambda a: a != "A"))

    if route_kind == "direct":
        hop = RouteHop(
            pool_id=draw(POOL),
            asset_in="A",
            asset_out=asset_out,
            amount_in=AMOUNT_IN,
            amount_out=amount_out,
        )
        leg = RouteLeg(hops=(hop,), amount_in=AMOUNT_IN, amount_out=amount_out)
        return RouteQuote(asset_in="A", asset_out=asset_out, amount_in=AMOUNT_IN, amount_out=amount_out, legs=(leg,))

    if route_kind == "twohop":
        mid = draw(ASSET.filter(lambda a: a not in {"A", asset_out}))
        amt_mid = draw(st.integers(min_value=1, max_value=max(1, amount_out + 50)))
        hop0 = RouteHop(
            pool_id=draw(POOL),
            asset_in="A",
            asset_out=mid,
            amount_in=AMOUNT_IN,
            amount_out=amt_mid,
        )
        hop1 = RouteHop(
            pool_id=draw(POOL),
            asset_in=mid,
            asset_out=asset_out,
            amount_in=amt_mid,
            amount_out=amount_out,
        )
        leg = RouteLeg(hops=(hop0, hop1), amount_in=AMOUNT_IN, amount_out=amount_out)
        return RouteQuote(asset_in="A", asset_out=asset_out, amount_in=AMOUNT_IN, amount_out=amount_out, legs=(leg,))

    amount_in_0 = draw(st.integers(min_value=1, max_value=AMOUNT_IN - 1))
    amount_in_1 = AMOUNT_IN - amount_in_0
    amount_out_0 = draw(st.integers(min_value=1, max_value=max(1, amount_out - 1)))
    amount_out_1 = amount_out - amount_out_0
    leg0 = RouteLeg(
        hops=(
            RouteHop(
                pool_id=draw(POOL),
                asset_in="A",
                asset_out=asset_out,
                amount_in=amount_in_0,
                amount_out=amount_out_0,
            ),
        ),
        amount_in=amount_in_0,
        amount_out=amount_out_0,
    )
    leg1 = RouteLeg(
        hops=(
            RouteHop(
                pool_id=draw(POOL),
                asset_in="A",
                asset_out=asset_out,
                amount_in=amount_in_1,
                amount_out=amount_out_1,
            ),
        ),
        amount_in=amount_in_1,
        amount_out=amount_out_1,
    )
    return RouteQuote(asset_in="A", asset_out=asset_out, amount_in=AMOUNT_IN, amount_out=amount_out, legs=(leg0, leg1))


@st.composite
def _route_quote_list(draw) -> list[RouteQuote]:
    asset_out = draw(ASSET.filter(lambda a: a != "A"))
    size = draw(st.integers(min_value=1, max_value=6))
    quotes: list[RouteQuote] = []
    for _ in range(size):
        quote = draw(_route_quote())
        # Normalize the final asset so the certificate domain is coherent.
        if quote.asset_out != asset_out:
            if len(quote.legs) == 1 and len(quote.legs[0].hops) == 1:
                hop = quote.legs[0].hops[0]
                quote = RouteQuote(
                    asset_in="A",
                    asset_out=asset_out,
                    amount_in=quote.amount_in,
                    amount_out=quote.amount_out,
                    legs=(
                        RouteLeg(
                            hops=(
                                RouteHop(
                                    pool_id=hop.pool_id,
                                    asset_in="A",
                                    asset_out=asset_out,
                                    amount_in=hop.amount_in,
                                    amount_out=hop.amount_out,
                                ),
                            ),
                            amount_in=quote.amount_in,
                            amount_out=quote.amount_out,
                        ),
                    ),
                )
            else:
                rebuilt_legs: list[RouteLeg] = []
                for leg in quote.legs:
                    rebuilt_hops = list(leg.hops)
                    last = rebuilt_hops[-1]
                    rebuilt_hops[-1] = RouteHop(
                        pool_id=last.pool_id,
                        asset_in=last.asset_in,
                        asset_out=asset_out,
                        amount_in=last.amount_in,
                        amount_out=last.amount_out,
                    )
                    rebuilt_legs.append(RouteLeg(hops=tuple(rebuilt_hops), amount_in=leg.amount_in, amount_out=leg.amount_out))
                quote = RouteQuote(
                    asset_in="A",
                    asset_out=asset_out,
                    amount_in=quote.amount_in,
                    amount_out=quote.amount_out,
                    legs=tuple(rebuilt_legs),
                )
        quotes.append(quote)
    return quotes


@given(quotes=_route_quote_list())
@settings(max_examples=100, deadline=None)
def test_exact_in_rank_projection_preserves_true_key_order(quotes: list[RouteQuote]) -> None:
    ordered_unique_keys, rank_by_key = compute_exact_in_route_rank_projection(quotes)
    packet = build_exact_in_route_rank_projection_packet(quotes)
    assert ordered_unique_keys
    assert packet.packet_ok is True
    assert packet.ordered_unique_keys_sorted_unique is True
    assert packet.candidate_ranks_match_projection is True
    assert packet.rank_order_preserves_true_key_order is True

    for key_index, route_key in enumerate(ordered_unique_keys):
        assert rank_by_key[route_key] == key_index

    for left in quotes:
        for right in quotes:
            left_key = exact_in_route_canonical_key(left)
            right_key = exact_in_route_canonical_key(right)
            left_rank = rank_by_key[left_key]
            right_rank = rank_by_key[right_key]
            if left_key < right_key:
                assert left_rank < right_rank
            elif left_key == right_key:
                assert left_rank == right_rank


@given(quotes=_route_quote_list())
@settings(max_examples=100, deadline=None)
def test_exact_in_certificate_winner_matches_true_key_minimum(quotes: list[RouteQuote]) -> None:
    certificate = build_exact_in_route_canonical_certificate(quotes)
    true_winner_index, true_winner = min(
        enumerate(quotes),
        key=lambda item: (exact_in_route_canonical_key(item[1]), item[0]),
    )

    assert certificate.winner_index == true_winner_index
    assert certificate.winner_quote == true_winner

    ok, err = verify_exact_in_route_canonical_certificate(quotes, certificate=certificate)
    assert ok, err
