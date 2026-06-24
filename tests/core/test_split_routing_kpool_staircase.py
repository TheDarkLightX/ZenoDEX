"""Parity tests for the k-pool staircase exact-in split optimizer.

Validates that `staircase_k_pool_best_split` matches the brute-force oracle on
a hostile corpus: skewed reserves, high fees, dust edges, zero-output gaps, and
tie-heavy plateaus. These are the same stress regimes used for the two-pool
staircase promotion evidence.
"""

from __future__ import annotations

import pytest

from src.core.split_routing_kpool_staircase import (
    _PoolSpec,
    staircase_k_pool_best_split,
)
from src.core.split_routing_kpool_brute import _brute_force_k_pool_split
from src.core.split_routing import PoolXY, exact_out_for_pool_exact_in


def _spec(pool_id: str, pool: PoolXY, min_valid: int) -> _PoolSpec:
    return _PoolSpec(pool_id=pool_id, pool=pool, min_valid=int(min_valid))


def _min_valid(pool: PoolXY, amount_in_total: int) -> int:
    """Smallest positive amount that quotes successfully for this pool."""
    for a in range(1, int(amount_in_total) + 1):
        try:
            exact_out_for_pool_exact_in(pool, int(a))
            return int(a)
        except ValueError:
            continue
    return int(amount_in_total) + 1  # infeasible


def _run_both(
    pools: list[tuple[str, PoolXY]],
    amount_in: int,
    max_legs: int,
) -> tuple[dict[str, int], dict[str, int]]:
    specs = [_spec(pid, p, _min_valid(p, int(amount_in))) for pid, p in pools]
    got = staircase_k_pool_best_split(
        pool_specs=specs,
        amount_in_total=int(amount_in),
        max_legs=int(max_legs),
        quote_exact_in=exact_out_for_pool_exact_in,
    )
    brute_pools = [(pid, p, _min_valid(p, int(amount_in))) for pid, p in pools]
    expected = _brute_force_k_pool_split(
        pools=brute_pools,
        amount_in_total=int(amount_in),
        max_legs=int(max_legs),
        quote_exact_in=exact_out_for_pool_exact_in,
    )
    return got, expected


def _assert_allocations_match(
    got: dict[str, int],
    expected: dict[str, int],
    pools: list[tuple[str, PoolXY]],
) -> None:
    # Both must agree on every pool's allocation.
    for pid, _p in pools:
        assert int(got.get(pid, 0)) == int(expected.get(pid, 0)), (
            f"pool {pid}: staircase={got.get(pid, 0)} brute={expected.get(pid, 0)}"
        )
    # Verify the total output matches (the canonical tie-break check).
    def total_out(alloc: dict[str, int]) -> int:
        total = 0
        for pid, p in pools:
            amt = int(alloc.get(pid, 0))
            if amt <= 0:
                continue
            total += int(exact_out_for_pool_exact_in(p, amt))
        return total
    assert total_out(got) == total_out(expected), (
        f"output mismatch: staircase={total_out(got)} brute={total_out(expected)}"
    )


# ---------------------------------------------------------------------------
# Two-pool parity (should match the existing two-pool staircase exactly).
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("amount_in", [10, 50, 100, 500, 1000, 4096])
def test_kpool_staircase_matches_brute_two_pools_balanced(amount_in: int) -> None:
    pools = [
        ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=30)),
    ]
    got, expected = _run_both(pools, amount_in, max_legs=2)
    _assert_allocations_match(got, expected, pools)


def test_kpool_staircase_matches_brute_two_pools_skewed() -> None:
    pools = [
        ("pool-a", PoolXY(x=1, y=1_000_000, fee_bps=0)),
        ("pool-b", PoolXY(x=1_000_000, y=1_000_000, fee_bps=0)),
    ]
    got, expected = _run_both(pools, amount_in=800, max_legs=2)
    _assert_allocations_match(got, expected, pools)


def test_kpool_staircase_matches_brute_two_pools_high_fee() -> None:
    pools = [
        ("pool-a", PoolXY(x=7, y=31, fee_bps=9_900)),
        ("pool-b", PoolXY(x=11, y=37, fee_bps=9_800)),
    ]
    got, expected = _run_both(pools, amount_in=200, max_legs=2)
    _assert_allocations_match(got, expected, pools)


def test_kpool_staircase_matches_brute_two_pools_known_gap() -> None:
    pools = [
        ("pool-a", PoolXY(x=87, y=80, fee_bps=75)),
        ("pool-b", PoolXY(x=46, y=66, fee_bps=11)),
    ]
    got, expected = _run_both(pools, amount_in=500, max_legs=2)
    _assert_allocations_match(got, expected, pools)


# ---------------------------------------------------------------------------
# Three-pool parity.
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("amount_in", [30, 100, 300, 600])
def test_kpool_staircase_matches_brute_three_pools_balanced(amount_in: int) -> None:
    pools = [
        ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=50)),
        ("pool-c", PoolXY(x=12_000, y=8_000, fee_bps=30)),
    ]
    got, expected = _run_both(pools, amount_in, max_legs=3)
    _assert_allocations_match(got, expected, pools)


def test_kpool_staircase_matches_brute_three_pools_skewed() -> None:
    pools = [
        ("pool-a", PoolXY(x=1, y=100_000, fee_bps=0)),
        ("pool-b", PoolXY(x=100_000, y=100_000, fee_bps=0)),
        ("pool-c", PoolXY(x=50_000, y=200_000, fee_bps=10)),
    ]
    got, expected = _run_both(pools, amount_in=500, max_legs=3)
    _assert_allocations_match(got, expected, pools)


def test_kpool_staircase_matches_brute_three_pools_high_fee_plateau() -> None:
    pools = [
        ("pool-a", PoolXY(x=7, y=31, fee_bps=9_900)),
        ("pool-b", PoolXY(x=11, y=37, fee_bps=9_800)),
        ("pool-c", PoolXY(x=13, y=41, fee_bps=9_700)),
    ]
    got, expected = _run_both(pools, amount_in=300, max_legs=3)
    _assert_allocations_match(got, expected, pools)


def test_kpool_staircase_matches_brute_three_pools_dust_edges() -> None:
    pools = [
        ("pool-a", PoolXY(x=100, y=10, fee_bps=100)),
        ("pool-b", PoolXY(x=200, y=20, fee_bps=200)),
        ("pool-c", PoolXY(x=300, y=30, fee_bps=300)),
    ]
    got, expected = _run_both(pools, amount_in=400, max_legs=3)
    _assert_allocations_match(got, expected, pools)


# ---------------------------------------------------------------------------
# Four-pool parity (smaller D to keep brute force tractable).
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("amount_in", [40, 80, 160])
def test_kpool_staircase_matches_brute_four_pools_balanced(amount_in: int) -> None:
    pools = [
        ("pool-a", PoolXY(x=5_000, y=5_000, fee_bps=30)),
        ("pool-b", PoolXY(x=4_000, y=6_000, fee_bps=50)),
        ("pool-c", PoolXY(x=6_000, y=4_000, fee_bps=30)),
        ("pool-d", PoolXY(x=5_500, y=5_500, fee_bps=70)),
    ]
    got, expected = _run_both(pools, amount_in, max_legs=4)
    _assert_allocations_match(got, expected, pools)


def test_kpool_staircase_matches_brute_four_pools_skewed() -> None:
    pools = [
        ("pool-a", PoolXY(x=1, y=50_000, fee_bps=0)),
        ("pool-b", PoolXY(x=50_000, y=50_000, fee_bps=0)),
        ("pool-c", PoolXY(x=25_000, y=100_000, fee_bps=10)),
        ("pool-d", PoolXY(x=10_000, y=10_000, fee_bps=100)),
    ]
    got, expected = _run_both(pools, amount_in=300, max_legs=4)
    _assert_allocations_match(got, expected, pools)


# ---------------------------------------------------------------------------
# Edge cases.
# ---------------------------------------------------------------------------


def test_kpool_staircase_single_pool_all_input() -> None:
    pools = [("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30))]
    got, expected = _run_both(pools, amount_in=100, max_legs=1)
    _assert_allocations_match(got, expected, pools)


def test_kpool_staircase_max_legs_one_forces_single_pool() -> None:
    pools = [
        ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=30)),
        ("pool-c", PoolXY(x=12_000, y=8_000, fee_bps=30)),
    ]
    got, expected = _run_both(pools, amount_in=500, max_legs=1)
    _assert_allocations_match(got, expected, pools)


def test_kpool_staircase_rejects_when_no_feasible_split() -> None:
    # Both pools require more input than amount_in provides.
    pools = [
        ("pool-a", PoolXY(x=1_000_000, y=1_000_000, fee_bps=9_999)),
        ("pool-b", PoolXY(x=1_000_000, y=1_000_000, fee_bps=9_999)),
    ]
    specs = [_spec(pid, p, _min_valid(p, 5)) for pid, p in pools]
    with pytest.raises(ValueError):
        staircase_k_pool_best_split(
            pool_specs=specs,
            amount_in_total=5,
            max_legs=2,
            quote_exact_in=exact_out_for_pool_exact_in,
        )


def test_kpool_staircase_rejects_empty_pools() -> None:
    with pytest.raises(ValueError):
        staircase_k_pool_best_split(
            pool_specs=[],
            amount_in_total=100,
            max_legs=2,
            quote_exact_in=exact_out_for_pool_exact_in,
        )


def test_kpool_staircase_rejects_nonpositive_amount() -> None:
    pools = [("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30))]
    specs = [_spec(pid, p, 1) for pid, p in pools]
    with pytest.raises(ValueError):
        staircase_k_pool_best_split(
            pool_specs=specs,
            amount_in_total=0,
            max_legs=1,
            quote_exact_in=exact_out_for_pool_exact_in,
        )


def test_kpool_staircase_rejects_nonpositive_max_legs() -> None:
    pools = [("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30))]
    specs = [_spec(pid, p, 1) for pid, p in pools]
    with pytest.raises(ValueError):
        staircase_k_pool_best_split(
            pool_specs=specs,
            amount_in_total=100,
            max_legs=0,
            quote_exact_in=exact_out_for_pool_exact_in,
        )
