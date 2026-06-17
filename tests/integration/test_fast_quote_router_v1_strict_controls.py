from __future__ import annotations

import pytest

from src.integration.fast_quote_router_v1 import (
    FastQuoteRouterV1,
    _quote_exact_in_onehop,
    _quote_exact_out_onehop,
)
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


def _mk_pool(*, pool_id: str = "p_ab") -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0="A",
        asset1="B",
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=0,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
        curve_params="",
    )


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"max_cache_pairs": True}, "max_cache_pairs must be an int"),
        ({"max_cache_pairs": "8"}, "max_cache_pairs must be an int"),
    ],
)
def test_fast_router_constructor_rejects_non_strict_cache_controls(
    kwargs: dict[str, object],
    message: str,
) -> None:
    with pytest.raises(ValueError, match=message):
        FastQuoteRouterV1(**kwargs)


def test_fast_router_constructor_preserves_nonpositive_integer_cache_floor() -> None:
    router = FastQuoteRouterV1(max_cache_pairs=0)

    assert router._max_cache_pairs == 1


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"amount_in": True}, "amount_in must be an int"),
        ({"amount_in": "10"}, "amount_in must be an int"),
        ({"amount_in": 10, "topk_max": True}, "topk_max must be an int"),
        ({"amount_in": 10, "topk_max": "32"}, "topk_max must be an int"),
        ({"amount_in": 10, "max_pairs_per_mid": False}, "max_pairs_per_mid must be an int"),
        ({"amount_in": 10, "max_union_candidates": False}, "max_union_candidates must be an int"),
    ],
)
def test_fast_exact_in_rejects_non_strict_controls(
    kwargs: dict[str, object],
    message: str,
) -> None:
    router = FastQuoteRouterV1()
    pools = {"p_ab": _mk_pool()}
    values: dict[str, object] = {"amount_in": 10}
    values.update(kwargs)

    with pytest.raises(ValueError, match=message):
        router.quote_exact_in_2hop_fast_v1(pools_by_id=pools, asset_in="A", asset_out="B", **values)


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"amount_out": True}, "amount_out must be an int"),
        ({"amount_out": "10"}, "amount_out must be an int"),
        ({"amount_out": 10, "topk_max": True}, "topk_max must be an int"),
        ({"amount_out": 10, "apply_two_hop_gate": 1}, "apply_two_hop_gate must be a bool"),
        ({"amount_out": 10, "max_pairs_per_mid": False}, "max_pairs_per_mid must be an int"),
        ({"amount_out": 10, "max_union_candidates": False}, "max_union_candidates must be an int"),
    ],
)
def test_fast_exact_out_rejects_non_strict_controls(
    kwargs: dict[str, object],
    message: str,
) -> None:
    router = FastQuoteRouterV1()
    pools = {"p_ab": _mk_pool()}
    values: dict[str, object] = {"amount_out": 10}
    values.update(kwargs)

    with pytest.raises(ValueError, match=message):
        router.quote_exact_out_2hop_fast_v1(pools_by_id=pools, asset_in="A", asset_out="B", **values)


def test_fast_router_preserves_zero_amount_as_no_quote() -> None:
    router = FastQuoteRouterV1()
    pools = {"p_ab": _mk_pool()}

    assert router.quote_exact_in_2hop_fast_v1(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=0) is None
    assert router.quote_exact_out_2hop_fast_v1(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=0) is None


def test_fast_router_preserves_nonpositive_integer_search_defaults() -> None:
    pytest.importorskip("numpy")
    router = FastQuoteRouterV1()
    pools = {"p_ab": _mk_pool()}

    exact_in = router.quote_exact_in_2hop_fast_v1(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=10,
        topk_max=0,
        max_pairs_per_mid=0,
        max_union_candidates=0,
    )
    exact_out = router.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_out=10,
        topk_max=0,
        max_pairs_per_mid=0,
        max_union_candidates=0,
    )

    assert exact_in is not None
    assert exact_out is not None


@pytest.mark.parametrize(
    ("quote", "kwargs", "message"),
    [
        (_quote_exact_in_onehop, {"amount_in": True}, "amount_in must be an int"),
        (_quote_exact_in_onehop, {"amount_in": "10"}, "amount_in must be an int"),
        (_quote_exact_out_onehop, {"amount_out": True}, "amount_out must be an int"),
        (_quote_exact_out_onehop, {"amount_out": "10"}, "amount_out must be an int"),
    ],
)
def test_fast_router_private_quote_helpers_reject_non_strict_amounts(
    quote,
    kwargs: dict[str, object],
    message: str,
) -> None:
    with pytest.raises(ValueError, match=message):
        quote(_mk_pool(), asset_in="A", asset_out="B", **kwargs)
