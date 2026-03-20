from __future__ import annotations

import importlib.util

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import assume, given, settings

from src.core.split_routing_dispatch import (
    best_split_two_pools_exact_out_for_pools,
    exact_out_route_canonical_key,
    SplitLegExactOutQuote,
)
from src.integration.exact_out_route_certificate import (
    audit_exact_out_many_pool_runtime_canonicality,
    build_exact_out_route_canonical_certificate,
    enumerate_exact_out_many_pool_candidates,
    enumerate_exact_out_two_pool_candidates,
    split_two_pools_exact_out_quote_to_many,
    verify_exact_out_route_canonical_certificate,
)
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _mk_pool(*, pool_id: str, reserve0: int, reserve1: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=int(fee_bps),
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
        curve_params=None,
    )


@st.composite
def _three_pool_case(draw) -> tuple[tuple[PoolState, PoolState, PoolState], int]:
    reserve0_a = draw(st.integers(min_value=40, max_value=180))
    reserve1_a = draw(st.integers(min_value=20, max_value=70))
    reserve0_b = draw(st.integers(min_value=40, max_value=180))
    reserve1_b = draw(st.integers(min_value=20, max_value=70))
    reserve0_c = draw(st.integers(min_value=40, max_value=180))
    reserve1_c = draw(st.integers(min_value=20, max_value=70))
    fee_a = draw(st.integers(min_value=0, max_value=50))
    fee_b = draw(st.integers(min_value=0, max_value=50))
    fee_c = draw(st.integers(min_value=0, max_value=50))
    amount_out_total = draw(st.integers(min_value=1, max_value=10))
    pools = (
        _mk_pool(pool_id="pool_a", reserve0=reserve0_a, reserve1=reserve1_a, fee_bps=fee_a),
        _mk_pool(pool_id="pool_b", reserve0=reserve0_b, reserve1=reserve1_b, fee_bps=fee_b),
        _mk_pool(pool_id="pool_c", reserve0=reserve0_c, reserve1=reserve1_c, fee_bps=fee_c),
    )
    return pools, amount_out_total

@st.composite
def _two_pool_case(draw) -> tuple[PoolState, PoolState, int]:
    reserve0_a = draw(st.integers(min_value=40, max_value=300))
    reserve1_a = draw(st.integers(min_value=15, max_value=120))
    reserve0_b = draw(st.integers(min_value=40, max_value=300))
    reserve1_b = draw(st.integers(min_value=15, max_value=120))
    fee_a = draw(st.integers(min_value=0, max_value=100))
    fee_b = draw(st.integers(min_value=0, max_value=100))
    amount_out_total = draw(st.integers(min_value=1, max_value=40))
    pool_a = _mk_pool(pool_id="pool_a", reserve0=reserve0_a, reserve1=reserve1_a, fee_bps=fee_a)
    pool_b = _mk_pool(pool_id="pool_b", reserve0=reserve0_b, reserve1=reserve1_b, fee_bps=fee_b)
    return pool_a, pool_b, amount_out_total


@given(case=_two_pool_case())
@settings(max_examples=80, deadline=None)
def test_exact_out_certificate_winner_matches_bruteforce_canonical_minimum(
    case: tuple[PoolState, PoolState, int]
) -> None:
    pool_a, pool_b, amount_out_total = case
    try:
        candidates = enumerate_exact_out_two_pool_candidates(
            pool_a, pool_b, asset_in=ASSET0, asset_out=ASSET1, amount_out_total=int(amount_out_total)
        )
    except ValueError:
        assume(False)

    true_winner_index, true_winner = min(
        enumerate(candidates),
        key=lambda item: (exact_out_route_canonical_key(item[1]), item[0]),
    )

    certificate = build_exact_out_route_canonical_certificate(candidates)
    ok, err = verify_exact_out_route_canonical_certificate(candidates, certificate=certificate)
    assert ok, err

    assert certificate.winner_index == true_winner_index
    assert certificate.winner_quote == true_winner


@given(case=_two_pool_case())
@settings(max_examples=80, deadline=None)
def test_exact_out_runtime_winner_matches_bruteforce_canonical_minimum(
    case: tuple[PoolState, PoolState, int]
) -> None:
    pool_a, pool_b, amount_out_total = case
    try:
        candidates = enumerate_exact_out_two_pool_candidates(
            pool_a, pool_b, asset_in=ASSET0, asset_out=ASSET1, amount_out_total=int(amount_out_total)
        )
    except ValueError:
        assume(False)

    runtime_quote = best_split_two_pools_exact_out_for_pools(
        pool_b,
        pool_a,
        asset_in=ASSET0,
        asset_out=ASSET1,
        amount_out_total=int(amount_out_total),
        brute_force_max=max(1, int(amount_out_total)),
    )
    runtime_many = split_two_pools_exact_out_quote_to_many(runtime_quote)
    true_winner = min(
        candidates,
        key=lambda quote: exact_out_route_canonical_key(quote),
    )

    assert runtime_many == true_winner


def test_exact_out_runtime_prefers_lex_smaller_single_leg_on_symmetric_plateau() -> None:
    pool_a = _mk_pool(pool_id="pool_a", reserve0=40, reserve1=15, fee_bps=0)
    pool_b = _mk_pool(pool_id="pool_b", reserve0=40, reserve1=15, fee_bps=0)
    candidates = enumerate_exact_out_two_pool_candidates(
        pool_a, pool_b, asset_in=ASSET0, asset_out=ASSET1, amount_out_total=1
    )

    runtime_quote = best_split_two_pools_exact_out_for_pools(
        pool_b,
        pool_a,
        asset_in=ASSET0,
        asset_out=ASSET1,
        amount_out_total=1,
        brute_force_max=1,
    )
    runtime_many = split_two_pools_exact_out_quote_to_many(runtime_quote)
    true_winner = min(
        candidates,
        key=lambda quote: exact_out_route_canonical_key(quote),
    )

    assert runtime_many == true_winner
    assert runtime_many.legs[0].pool_id == "pool_a"


@given(case=_three_pool_case())
@settings(max_examples=40, deadline=None)
def test_exact_out_many_pool_bounded_audit_recovers_canonical_minimum_on_small_domains(
    case: tuple[tuple[PoolState, PoolState, PoolState], int]
) -> None:
    pools, amount_out_total = case
    try:
        candidates = enumerate_exact_out_many_pool_candidates(
            pools,
            asset_in=ASSET0,
            asset_out=ASSET1,
            amount_out_total=int(amount_out_total),
            max_legs=3,
            max_candidate_pools=3,
            max_enumerated_candidates=8_000,
        )
    except ValueError:
        assume(False)

    true_winner = min(candidates, key=exact_out_route_canonical_key)
    audit = audit_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in=ASSET0,
        asset_out=ASSET1,
        amount_out_total=int(amount_out_total),
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    )

    assert audit.canonical_winner_quote == true_winner
    assert audit.runtime_quote in candidates


def test_exact_out_many_pool_runtime_known_counterexample_is_now_canonically_aligned() -> None:
    pools = (
        _mk_pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _mk_pool(pool_id="pool_b", reserve0=40, reserve1=63, fee_bps=0),
        _mk_pool(pool_id="pool_c", reserve0=40, reserve1=20, fee_bps=0),
    )
    audit = audit_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in=ASSET0,
        asset_out=ASSET1,
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    )

    assert audit.runtime_matches_canonical is True
    assert audit.runtime_quote.amount_in_total == 2
    assert audit.canonical_winner_quote.amount_in_total == 2
    assert audit.runtime_quote.legs == (
        SplitLegExactOutQuote(pool_id="pool_b", amount_out=3, amount_in=2),
    )
    assert audit.canonical_winner_quote.legs == (
        SplitLegExactOutQuote(pool_id="pool_b", amount_out=3, amount_in=2),
    )
