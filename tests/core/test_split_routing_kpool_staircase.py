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
    best_k_pool_exact_in_split,
)
from src.core.split_routing_kpool_brute import _brute_force_k_pool_split
from src.core.split_routing import PoolXY, exact_out_for_pool_exact_in
from src.core.split_routing_many_exact_in_small import (
    best_small_domain_many_pool_exact_in,
)


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


# ---------------------------------------------------------------------------
# DP compression correctness: Pareto-optimal state retention.
#
# The prefix/suffix DP combination must keep states with fewer legs even when
# they have lower output at the same spent value. A state with fewer legs can
# enable a valid prefix+suffix+interior combination that a higher-output state
# with more legs cannot (the legs budget constraint excludes the latter).
#
# This test constructs a 4-pool case where the optimal split requires using a
# lower-output prefix state to leave room for the suffix and interior pool.
# ---------------------------------------------------------------------------


def test_kpool_staircase_dp_compression_pareto_retention() -> None:
    """Verify the Pareto-optimal state retention fixes the DP compression bug.

    Uses 4 pools with max_legs=3 so that the optimal split requires choosing a
    prefix state with fewer legs (but lower output) to leave room for the
    suffix and interior pool within the legs budget.
    """
    pools = [
        ("pool-a", PoolXY(x=100, y=200, fee_bps=100)),
        ("pool-b", PoolXY(x=200, y=100, fee_bps=100)),
        ("pool-c", PoolXY(x=150, y=150, fee_bps=50)),
        ("pool-d", PoolXY(x=300, y=300, fee_bps=30)),
    ]
    got, expected = _run_both(pools, amount_in=250, max_legs=3)
    _assert_allocations_match(got, expected, pools)


def test_kpool_staircase_dp_compression_pareto_retention_skewed() -> None:
    """Another DP compression test with skewed reserves and high fees."""
    pools = [
        ("pool-a", PoolXY(x=50, y=500, fee_bps=500)),
        ("pool-b", PoolXY(x=500, y=50, fee_bps=500)),
        ("pool-c", PoolXY(x=10, y=1000, fee_bps=9900)),
        ("pool-d", PoolXY(x=1000, y=10, fee_bps=9900)),
    ]
    got, expected = _run_both(pools, amount_in=180, max_legs=3)
    _assert_allocations_match(got, expected, pools)


# ---------------------------------------------------------------------------
# Fail-closed validation: duplicate pool_ids must be rejected.
# ---------------------------------------------------------------------------


def test_kpool_staircase_rejects_duplicate_pool_ids() -> None:
    """Duplicate pool_ids would corrupt quote caches and allocations. Must reject."""
    pools = [
        ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-a", PoolXY(x=8_000, y=12_000, fee_bps=30)),
    ]
    specs = [_spec(pid, p, 1) for pid, p in pools]
    with pytest.raises(ValueError, match="duplicate pool_id"):
        staircase_k_pool_best_split(
            pool_specs=specs,
            amount_in_total=100,
            max_legs=2,
            quote_exact_in=exact_out_for_pool_exact_in,
        )


def test_kpool_staircase_rejects_duplicate_pool_ids_three_pools() -> None:
    """Duplicate at position 2 of 3 must also be caught."""
    pools = [
        ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=30)),
        ("pool-a", PoolXY(x=12_000, y=8_000, fee_bps=30)),
    ]
    specs = [_spec(pid, p, 1) for pid, p in pools]
    with pytest.raises(ValueError, match="duplicate pool_id"):
        staircase_k_pool_best_split(
            pool_specs=specs,
            amount_in_total=100,
            max_legs=3,
            quote_exact_in=exact_out_for_pool_exact_in,
        )


# ---------------------------------------------------------------------------
# Adaptive fallback: best_k_pool_exact_in_split must pick the cheaper solver.
# ---------------------------------------------------------------------------


def _small_dp_fn(*, pool_ids, amount_in_total, max_legs, quote_for_pool_id):
    """Inject the existing small-domain DP for adaptive fallback tests."""
    return best_small_domain_many_pool_exact_in(
        pool_ids=pool_ids,
        amount_in_total=int(amount_in_total),
        max_legs=int(max_legs),
        quote_for_pool_id=quote_for_pool_id,
    )


def test_adaptive_fallback_matches_staircase_on_sparse_pools() -> None:
    """Sparse breakpoints: adaptive should use staircase, matching direct call."""
    pools = [
        ("pool-a", PoolXY(x=1, y=100_000, fee_bps=0)),
        ("pool-b", PoolXY(x=100_000, y=100_000, fee_bps=0)),
        ("pool-c", PoolXY(x=50_000, y=200_000, fee_bps=10)),
    ]
    specs = [_spec(pid, p, _min_valid(p, 500)) for pid, p in pools]
    direct = staircase_k_pool_best_split(
        pool_specs=specs,
        amount_in_total=500,
        max_legs=3,
        quote_exact_in=exact_out_for_pool_exact_in,
    )
    adaptive = best_k_pool_exact_in_split(
        pool_specs=specs,
        amount_in_total=500,
        max_legs=3,
        quote_exact_in=exact_out_for_pool_exact_in,
        small_domain_dp_fn=_small_dp_fn,
    )
    assert direct == adaptive


def test_adaptive_fallback_matches_small_dp_on_dense_pools() -> None:
    """Dense breakpoints: adaptive should fall back to small-domain DP."""
    pools = [
        ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-b", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-c", PoolXY(x=10_000, y=10_000, fee_bps=30)),
    ]
    specs = [_spec(pid, p, _min_valid(p, 200)) for pid, p in pools]
    # Direct small-domain DP result.
    pool_ids = [pid for pid, _ in pools]
    pools_dict = {pid: p for pid, p in pools}
    min_valids = {pid: _min_valid(p, 200) for pid, p in pools}

    def quote_for_pid(pool_id: str, amount: int) -> int | None:
        if int(amount) < int(min_valids[pool_id]):
            return None
        if int(amount) <= 0:
            return 0
        try:
            return int(exact_out_for_pool_exact_in(pools_dict[pool_id], int(amount)))
        except ValueError:
            return None

    small_dp_result = best_small_domain_many_pool_exact_in(
        pool_ids=pool_ids,
        amount_in_total=200,
        max_legs=3,
        quote_for_pool_id=quote_for_pid,
    )
    # Adaptive should match (it falls back to the same DP).
    adaptive = best_k_pool_exact_in_split(
        pool_specs=specs,
        amount_in_total=200,
        max_legs=3,
        quote_exact_in=exact_out_for_pool_exact_in,
        small_domain_dp_fn=_small_dp_fn,
    )
    assert adaptive == small_dp_result


def test_adaptive_fallback_matches_brute_on_sparse() -> None:
    """Adaptive on sparse pools must match brute force (exactness check)."""
    pools = [
        ("pool-a", PoolXY(x=1, y=50_000, fee_bps=0)),
        ("pool-b", PoolXY(x=50_000, y=50_000, fee_bps=0)),
        ("pool-c", PoolXY(x=25_000, y=100_000, fee_bps=10)),
    ]
    specs = [_spec(pid, p, _min_valid(p, 300)) for pid, p in pools]
    brute_pools = [(pid, p, _min_valid(p, 300)) for pid, p in pools]
    expected = _brute_force_k_pool_split(
        pools=brute_pools,
        amount_in_total=300,
        max_legs=3,
        quote_exact_in=exact_out_for_pool_exact_in,
    )
    got = best_k_pool_exact_in_split(
        pool_specs=specs,
        amount_in_total=300,
        max_legs=3,
        quote_exact_in=exact_out_for_pool_exact_in,
        small_domain_dp_fn=_small_dp_fn,
    )
    _assert_allocations_match(got, expected, pools)


def test_adaptive_no_fallback_when_dp_fn_none() -> None:
    """When small_domain_dp_fn is None, adaptive must use staircase always."""
    pools = [
        ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=30)),
    ]
    specs = [_spec(pid, p, _min_valid(p, 100)) for pid, p in pools]
    direct = staircase_k_pool_best_split(
        pool_specs=specs,
        amount_in_total=100,
        max_legs=2,
        quote_exact_in=exact_out_for_pool_exact_in,
    )
    adaptive = best_k_pool_exact_in_split(
        pool_specs=specs,
        amount_in_total=100,
        max_legs=2,
        quote_exact_in=exact_out_for_pool_exact_in,
        small_domain_dp_fn=None,
    )
    assert direct == adaptive


def test_adaptive_rejects_duplicate_pool_ids() -> None:
    """Adaptive entry point must also reject duplicate pool_ids."""
    pools = [
        ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-a", PoolXY(x=8_000, y=12_000, fee_bps=30)),
    ]
    specs = [_spec(pid, p, 1) for pid, p in pools]
    with pytest.raises(ValueError, match="duplicate pool_id"):
        best_k_pool_exact_in_split(
            pool_specs=specs,
            amount_in_total=100,
            max_legs=2,
            quote_exact_in=exact_out_for_pool_exact_in,
            small_domain_dp_fn=_small_dp_fn,
        )


# ---------------------------------------------------------------------------
# Drift fail-closed: jump enumeration must raise on quote/formula drift.
#
# Matches the two-pool staircase behavior: an "exact" solver must not silently
# lose optimality by returning a partial candidate set. The adaptive entry
# point catches the drift ValueError and falls back to the existing DP.
# ---------------------------------------------------------------------------


def _drift_quote(pool: PoolXY, amount: int) -> int:
    """A quote function that drifts: rejects amounts above 50, causing
    the closed-form jump estimate to request an output level that the quote
    cannot reach."""
    if int(amount) > 50:
        raise ValueError("drift: amount exceeds quotable range")
    return int(exact_out_for_pool_exact_in(pool, int(amount)))


def test_kpool_staircase_raises_on_drift_no_fallback() -> None:
    """Direct staircase must raise ValueError on quote/formula drift."""
    pools = [
        ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=30)),
    ]
    specs = [_spec(pid, p, 1) for pid, p in pools]
    with pytest.raises(ValueError, match="output level"):
        staircase_k_pool_best_split(
            pool_specs=specs,
            amount_in_total=500,
            max_legs=2,
            quote_exact_in=_drift_quote,
        )


def test_kpool_adaptive_falls_back_on_drift() -> None:
    """Adaptive entry point must fall back to small-domain DP on drift.

    Uses sparse pools (skewed reserves, zero fee) so the Phase 1 density
    estimate is below threshold and enumeration runs. The drift quote then
    raises ValueError during enumeration, triggering the fallback path.

    The result must match the small-domain DP run directly with a
    None-returning quote wrapper (so the DP sees the same feasible set).
    """
    pools = [
        ("pool-a", PoolXY(x=1, y=100_000, fee_bps=0)),
        ("pool-b", PoolXY(x=100_000, y=100_000, fee_bps=0)),
    ]
    specs = [_spec(pid, p, 1) for pid, p in pools]
    pools_dict = {pid: p for pid, p in pools}
    min_valids = {pid: 1 for pid, _ in pools}

    def quote_for_pid(pool_id: str, amount: int) -> int | None:
        if int(amount) < int(min_valids[pool_id]):
            return None
        if int(amount) <= 0:
            return 0
        if int(amount) > 50:
            return None
        try:
            return int(exact_out_for_pool_exact_in(pools_dict[pool_id], int(amount)))
        except ValueError:
            return None

    # Direct small-domain DP result with the None-returning wrapper.
    pool_ids = [pid for pid, _ in pools]
    small_dp_result = best_small_domain_many_pool_exact_in(
        pool_ids=pool_ids,
        amount_in_total=80,
        max_legs=2,
        quote_for_pool_id=quote_for_pid,
    )

    # The adaptive entry point should catch the drift and fall back.
    result = best_k_pool_exact_in_split(
        pool_specs=specs,
        amount_in_total=80,
        max_legs=2,
        quote_exact_in=_drift_quote,
        small_domain_dp_fn=_small_dp_fn,
    )
    # The result must match the direct small-domain DP result.
    assert result == small_dp_result
