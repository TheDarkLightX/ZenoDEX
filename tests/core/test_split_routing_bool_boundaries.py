from __future__ import annotations

import pytest

from src.core.split_routing_many_exact_in import (
    ManyPoolExactInRequest,
    best_many_pool_exact_in_split,
)
from src.core.split_routing_many_exact_out import (
    ManyPoolExactOutRequest,
    best_many_pool_exact_out_split,
    build_exact_out_capacity_guard_from_caps,
)
from src.core.split_routing_types import (
    ExactOutCapacityGuard,
    SplitLegExactOutQuote,
    SplitLegQuote,
    exact_out_route_canonical_key_for_legs,
)


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
