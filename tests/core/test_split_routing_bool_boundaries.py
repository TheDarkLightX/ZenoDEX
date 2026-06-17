from __future__ import annotations

import pytest

from src.core.split_routing import (
    PoolXY,
    best_split_two_pools_exact_in,
    brute_force_best_split_two_pools_exact_in,
    exact_out_for_pool_exact_in,
    resolve_two_pool_split_search_params,
    staircase_jump_best_split_two_pools_exact_in,
)
from src.core.split_routing_dispatch import (
    best_split_many_pools_exact_in_for_pools,
    best_split_many_pools_exact_out_for_pools,
    best_split_two_pools_exact_in_for_pools,
    best_split_two_pools_exact_out_for_pools,
    exact_out_capacity_guard_for_pools,
)
from src.core.split_routing_generic_exact_in import (
    GenericExactInSplitRequest,
    best_generic_two_pool_exact_in,
)
from src.core.split_routing_many_exact_in import (
    ManyPoolExactInRequest,
    best_many_pool_exact_in_split,
)
from src.core.split_routing_many_exact_in_small import best_small_domain_many_pool_exact_in
from src.core.split_routing_many_exact_out import (
    ManyPoolExactOutRequest,
    best_many_pool_exact_out_split,
    build_exact_out_capacity_guard_from_caps,
)
from src.core.split_routing_pool_quotes import quote_exact_in_for_pool, quote_exact_out_for_pool
from src.core.split_routing_staircase import (
    staircase_jump_best_split_two_pools_exact_in as staircase_jump_impl,
)
from src.core.split_routing_two_exact_out import (
    TwoPoolExactOutRequest,
    best_two_pool_exact_out_split,
)
from src.core.split_routing_types import (
    ExactOutCapacityGuard,
    SplitLegExactOutQuote,
    SplitLegQuote,
    exact_out_route_canonical_key_for_legs,
)
from src.core.split_routing_windowed import WindowSearchPlan, search_windowed_both_valid
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


def _pool(pid: str = "pool-a") -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0="A",
        asset1="B",
        reserve0=100,
        reserve1=100,
        fee_bps=0,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
        curve_params=None,
    )


def _window_plan(**overrides: object) -> WindowSearchPlan:
    values = {
        "pool0": PoolXY(x=100, y=100, fee_bps=0),
        "pool1": PoolXY(x=100, y=100, fee_bps=0),
        "amount_in": 10,
        "bounds": (0, 10),
        "profile": "baseline",
        "grid_n": 8,
        "force_dense_grid": False,
        "left_sweep_k": 0,
        "window": 2,
        "total_out": lambda split: int(split),
    }
    values.update(overrides)
    return WindowSearchPlan(**values)


def _exact_in_request(**overrides: object) -> ManyPoolExactInRequest:
    values = {
        "pools": (),
        "asset_in": "A",
        "asset_out": "B",
        "amount_in_total": 10,
        "max_legs": 2,
        "max_candidates": 2,
        "max_iters": 4,
        "reserves_for": lambda _pool: None,
        "quote_exact_in": lambda _pool, _amount_in: 1,
    }
    values.update(overrides)
    return ManyPoolExactInRequest(**values)  # type: ignore[arg-type]


def _exact_out_request(**overrides: object) -> ManyPoolExactOutRequest:
    values = {
        "pools": (),
        "asset_in": "A",
        "asset_out": "B",
        "amount_out_total": 10,
        "max_legs": 2,
        "max_candidates": 2,
        "max_iters": 4,
        "window": 0,
        "brute_force_max": 0,
        "max_full_domain_pools": 2,
        "reserves_for": lambda _pool: None,
        "quote_exact_out": lambda _pool, _amount_out: 1,
    }
    values.update(overrides)
    return ManyPoolExactOutRequest(**values)  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("field", "message"),
    [
        ("amount_in_total", "amount_in_total must be positive"),
        ("max_legs", "max_legs must be positive"),
        ("max_candidates", "max_candidates must be positive"),
        ("max_iters", "max_iters must be positive"),
    ],
)
def test_many_pool_exact_in_request_rejects_bool_controls(field: str, message: str) -> None:
    with pytest.raises(ValueError, match=message):
        best_many_pool_exact_in_split(_exact_in_request(**{field: True}))


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("amount_out_total", True, "amount_out_total must be positive"),
        ("max_legs", True, "max_legs must be positive"),
        ("max_candidates", True, "max_candidates must be positive"),
        ("max_iters", True, "max_iters must be positive"),
        ("window", False, "window must be non-negative"),
        ("brute_force_max", False, "brute_force_max must be non-negative"),
        ("max_full_domain_pools", True, "max_full_domain_pools must be positive"),
    ],
)
def test_many_pool_exact_out_request_rejects_bool_controls(field: str, value: bool, message: str) -> None:
    with pytest.raises(ValueError, match=message):
        best_many_pool_exact_out_split(_exact_out_request(**{field: value}))


def test_many_pool_exact_out_property_rejects_bool_budget_controls() -> None:
    with pytest.raises(ValueError, match="max_iters must be positive"):
        _ = _exact_out_request(max_iters=True).max_enumerated_candidates
    with pytest.raises(ValueError, match="max_legs must be positive"):
        _ = _exact_out_request(max_legs=True).max_enumerated_candidates


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("amount_out_total", True, "amount_out_total must be positive"),
        ("amount_out_total", "10", "amount_out_total must be positive"),
        ("window", False, "window must be non-negative"),
        ("brute_force_max", False, "brute_force_max must be non-negative"),
    ],
)
def test_two_pool_exact_out_request_rejects_non_strict_controls(
    field: str,
    value: object,
    message: str,
) -> None:
    kwargs = {
        "amount_out_total": 10,
        "window": 0,
        "brute_force_max": 0,
    }
    kwargs[field] = value
    with pytest.raises(ValueError, match=message):
        best_two_pool_exact_out_split(
            TwoPoolExactOutRequest(
                pool0=_pool("pool-a"),
                pool1=_pool("pool-b"),
                asset_in="A",
                asset_out="B",
                reserves_for=lambda _pool: (100, 100),
                quote_exact_out=lambda _pool, amount_out: int(amount_out),
                **kwargs,
            )
        )


@pytest.mark.parametrize(
    ("builder", "message"),
    [
        (
            lambda: exact_out_for_pool_exact_in(PoolXY(x=True, y=100, fee_bps=0), 10),
            "reserve_in must be an int",
        ),
        (
            lambda: exact_out_for_pool_exact_in(PoolXY(x=100, y=100, fee_bps=False), 10),
            "fee_bps must be an int",
        ),
        (
            lambda: exact_out_for_pool_exact_in(PoolXY(x=100, y=100, fee_bps=0), True),
            "amount_in must be positive",
        ),
        (
            lambda: brute_force_best_split_two_pools_exact_in(
                PoolXY(x=100, y=100, fee_bps=0),
                PoolXY(x=100, y=100, fee_bps=0),
                "10",
            ),
            "amount_in must be positive",
        ),
        (
            lambda: best_split_two_pools_exact_in(
                PoolXY(x=100, y=100, fee_bps=0),
                PoolXY(x=100, y=100, fee_bps=0),
                10,
                window=False,
            ),
            "window must be non-negative",
        ),
        (
            lambda: staircase_jump_best_split_two_pools_exact_in(
                PoolXY(x=100, y=100, fee_bps=0),
                PoolXY(x=100, y=100, fee_bps=0),
                True,
            ),
            "amount_in must be positive",
        ),
        (
            lambda: staircase_jump_impl(
                PoolXY(x=100, y=100, fee_bps=0),
                PoolXY(x=100, y=100, fee_bps=0),
                True,
                quote_exact_in=exact_out_for_pool_exact_in,
            ),
            "amount_in must be positive",
        ),
        (
            lambda: staircase_jump_impl(
                PoolXY(x=100, y=100, fee_bps=0),
                PoolXY(x=100, y=100, fee_bps=0),
                "10",
                quote_exact_in=exact_out_for_pool_exact_in,
            ),
            "amount_in must be positive",
        ),
    ],
)
def test_cpmm_exact_in_split_rejects_non_strict_controls(builder, message: str) -> None:
    with pytest.raises(ValueError, match=message):
        builder()


@pytest.mark.parametrize(
    ("quote", "kwargs", "message"),
    [
        (quote_exact_in_for_pool, {"amount_in": True}, "amount_in must be positive"),
        (quote_exact_in_for_pool, {"amount_in": "10"}, "amount_in must be positive"),
        (quote_exact_out_for_pool, {"amount_out": True}, "amount_out must be positive"),
        (quote_exact_out_for_pool, {"amount_out": "10"}, "amount_out must be positive"),
    ],
)
def test_live_pool_quote_adapters_reject_non_strict_amounts(
    quote,
    kwargs: dict[str, object],
    message: str,
) -> None:
    with pytest.raises(ValueError, match=message):
        quote(_pool(), asset_in="A", asset_out="B", **kwargs)


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"amount_in": True, "window": 64}, "amount_in must be an int"),
        ({"amount_in": "10", "window": 64}, "amount_in must be an int"),
        ({"amount_in": 10, "window": False}, "window must be non-negative"),
        ({"amount_in": 10, "window": -1}, "window must be non-negative"),
    ],
)
def test_split_profile_resolution_rejects_non_strict_controls(
    kwargs: dict[str, object],
    message: str,
) -> None:
    p0 = PoolXY(x=100, y=100, fee_bps=0)
    p1 = PoolXY(x=100, y=100, fee_bps=0)
    with pytest.raises(ValueError, match=message):
        resolve_two_pool_split_search_params(
            p0,
            p1,
            kwargs["amount_in"],
            search_profile="adaptive_v6",
            window=kwargs["window"],
        )


def test_split_profile_resolution_preserves_nonpositive_integer_fallback() -> None:
    p0 = PoolXY(x=100, y=100, fee_bps=0)
    p1 = PoolXY(x=100, y=100, fee_bps=0)

    assert resolve_two_pool_split_search_params(p0, p1, 0, search_profile="adaptive_v6", window=64) == (
        64,
        "baseline",
    )


@pytest.mark.parametrize(
    ("overrides", "message"),
    [
        ({"amount_in": True}, "amount_in must be positive"),
        ({"amount_in": "10"}, "amount_in must be positive"),
        ({"bounds": [0, 10]}, "bounds must contain two endpoints"),
        ({"bounds": (True, 10)}, "bounds.lo must be non-negative"),
        ({"bounds": (5, 4)}, "bounds must be ordered"),
        ({"bounds": (0, 11)}, "bounds.hi must be <= amount_in"),
        ({"grid_n": False}, "grid_n must be positive"),
        ({"window": False}, "window must be non-negative"),
        ({"force_dense_grid": 1}, "force_dense_grid must be a bool"),
        ({"left_sweep_k": False}, "left_sweep_k must be non-negative"),
        ({"profile": True}, "profile must be a string"),
    ],
)
def test_windowed_split_plan_rejects_non_strict_controls(
    overrides: dict[str, object],
    message: str,
) -> None:
    with pytest.raises(ValueError, match=message):
        search_windowed_both_valid(_window_plan(**overrides))


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("amount_in_total", True, "amount_in_total must be positive"),
        ("amount_in_total", "10", "amount_in_total must be positive"),
        ("window", False, "window must be non-negative"),
        ("brute_force_max", False, "brute_force_max must be non-negative"),
    ],
)
def test_generic_exact_in_split_rejects_non_strict_controls(
    field: str,
    value: object,
    message: str,
) -> None:
    kwargs = {
        "amount_in_total": 10,
        "window": 0,
        "brute_force_max": 10,
    }
    kwargs[field] = value
    with pytest.raises(ValueError, match=message):
        best_generic_two_pool_exact_in(
            GenericExactInSplitRequest(
                quote0=lambda amount_in: int(amount_in),
                quote1=lambda amount_in: int(amount_in),
                **kwargs,
            )
        )


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"amount_in_total": True, "max_legs": 1}, "amount_in_total must be positive"),
        ({"amount_in_total": "10", "max_legs": 1}, "amount_in_total must be positive"),
        ({"amount_in_total": 10, "max_legs": True}, "max_legs must be positive"),
        ({"amount_in_total": 10, "max_legs": 1, "pool_ids": ()}, "pool_ids must be non-empty"),
        ({"amount_in_total": 10, "max_legs": 1, "pool_ids": ("pool-a", "pool-a")}, "pool_ids must not repeat"),
        ({"amount_in_total": 10, "max_legs": 1, "pool_ids": ("pool-a", 7)}, "pool_ids must be strings"),
    ],
)
def test_small_domain_exact_in_split_rejects_invalid_controls_and_pool_ids(
    kwargs: dict[str, object],
    message: str,
) -> None:
    values: dict[str, object] = {
        "pool_ids": ("pool-a",),
        "amount_in_total": 10,
        "max_legs": 1,
    }
    values.update(kwargs)
    with pytest.raises(ValueError, match=message):
        best_small_domain_many_pool_exact_in(
            quote_for_pool_id=lambda _pool_id, amount_in: int(amount_in),
            **values,
        )


@pytest.mark.parametrize(
    "builder",
    [
        lambda: SplitLegQuote(pool_id="pool-a", amount_in=True, amount_out=1),
        lambda: SplitLegExactOutQuote(pool_id="pool-a", amount_out=True, amount_in=1),
        lambda: ExactOutCapacityGuard(
            amount_out_total=1,
            max_legs=True,
            top_caps=(("pool-a", 1),),
            capacity_upper_bound=1,
        ),
        lambda: ExactOutCapacityGuard(
            amount_out_total=1,
            max_legs=1,
            top_caps=(("pool-a", True),),
            capacity_upper_bound=1,
        ),
        lambda: ExactOutCapacityGuard(
            amount_out_total=1,
            max_legs=1,
            top_caps=(("pool-a", 1),),
            capacity_upper_bound=True,
        ),
        lambda: exact_out_route_canonical_key_for_legs(amount_in_total=True, legs=(("pool-a", 1),)),
        lambda: exact_out_route_canonical_key_for_legs(amount_in_total=1, legs=(("pool-a", True),)),
        lambda: build_exact_out_capacity_guard_from_caps(
            (("pool-a", True),),
            amount_out_total=1,
            max_legs=1,
        ),
    ],
)
def test_split_route_contracts_reject_bool_amounts_and_caps(builder) -> None:
    with pytest.raises(ValueError):
        builder()


@pytest.mark.parametrize(
    ("builder", "message"),
    [
        (
            lambda: exact_out_capacity_guard_for_pools(
                (),
                asset_in="A",
                asset_out="B",
                amount_out_total=True,
                max_legs=1,
            ),
            "amount_out_total must be positive",
        ),
        (
            lambda: best_split_two_pools_exact_in_for_pools(
                _pool("pool-a"),
                _pool("pool-b"),
                asset_in="A",
                asset_out="B",
                amount_in_total=True,
            ),
            "amount_in_total must be positive",
        ),
        (
            lambda: best_split_two_pools_exact_out_for_pools(
                _pool("pool-a"),
                _pool("pool-b"),
                asset_in="A",
                asset_out="B",
                amount_out_total=True,
            ),
            "amount_out_total must be positive",
        ),
        (
            lambda: best_split_many_pools_exact_in_for_pools(
                (),
                asset_in="A",
                asset_out="B",
                amount_in_total=10,
                max_iters=True,
            ),
            "max_iters must be positive",
        ),
        (
            lambda: best_split_many_pools_exact_out_for_pools(
                (),
                asset_in="A",
                asset_out="B",
                amount_out_total=10,
                window=False,
            ),
            "window must be non-negative",
        ),
    ],
)
def test_split_routing_dispatch_rejects_bool_controls(builder, message: str) -> None:
    with pytest.raises(ValueError, match=message):
        builder()
