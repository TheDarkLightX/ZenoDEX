from __future__ import annotations

from src.core.split_routing import (
    PoolXY,
    best_split_two_pools_exact_in,
    brute_force_best_split_two_pools_exact_in,
    exact_out_for_pool_exact_in,
)


def test_split_matches_bruteforce_small():
    p0 = PoolXY(x=1000, y=1000, fee_bps=0)
    p1 = PoolXY(x=1000, y=1000, fee_bps=0)
    # amt=1 yields zero output in both pools (kernel rejects), so start at 2.
    for amt in [2, 3, 5, 10, 25, 50]:
        best_out_bf, best_a_bf = brute_force_best_split_two_pools_exact_in(p0, p1, amt)
        best_out, best_a = best_split_two_pools_exact_in(p0, p1, amt, window=64)
        assert best_out == best_out_bf
        assert best_a == best_a_bf


def test_split_can_beat_single_pool():
    # One pool is shallow on y, the other deep; splitting should not be worse than best single.
    p0 = PoolXY(x=1000, y=100, fee_bps=0)
    p1 = PoolXY(x=1000, y=1000, fee_bps=0)
    amt = 50
    best_out, _ = best_split_two_pools_exact_in(p0, p1, amt, window=64)
    # Sanity: best_split includes endpoints, so it cannot be worse than the best single-pool route.
    best_single = max(exact_out_for_pool_exact_in(p0, amt), exact_out_for_pool_exact_in(p1, amt))
    assert best_out >= best_single


def test_split_regression_counterexample_output_gap():
    # Previously: heuristic missed the true optimum (window too narrow).
    p0 = PoolXY(x=378, y=5, fee_bps=50)
    p1 = PoolXY(x=1, y=336, fee_bps=438)
    amt = 429
    best_out_bf, best_a_bf = brute_force_best_split_two_pools_exact_in(p0, p1, amt)
    best_out, best_a = best_split_two_pools_exact_in(p0, p1, amt, window=64)
    assert best_out == best_out_bf
    assert best_a == best_a_bf


def test_split_regression_counterexample_tie_break():
    # Previously: heuristic found an optimal output but violated the canonical tie-break (smallest a).
    p0 = PoolXY(x=2, y=115, fee_bps=424)
    p1 = PoolXY(x=189, y=3, fee_bps=157)
    amt = 199
    best_out_bf, best_a_bf = brute_force_best_split_two_pools_exact_in(p0, p1, amt)
    best_out, best_a = best_split_two_pools_exact_in(p0, p1, amt, window=64)
    assert best_out == best_out_bf
    assert best_a == best_a_bf
