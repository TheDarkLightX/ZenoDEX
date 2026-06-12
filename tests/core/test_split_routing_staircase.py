"""
Differential and efficiency tests for the staircase jump-enumeration split
optimizer (`staircase_jump_best_split_two_pools_exact_in`).

Mathematical basis: lean-mathlib/Proofs/SplitRoutingStaircase.lean
- `two_pool_split_candidate_complete` (candidate-set completeness)
- `le_feeOut_iff` (closed-form jump points)

The optimizer must be bit-identical to the brute-force reference (including
the leftmost tie-break) while evaluating only one quote pair per distinct
pool-0 output level.
"""

from __future__ import annotations

import random

from src.core import split_routing as split_routing_mod
from src.core.split_routing import (
    PoolXY,
    brute_force_best_split_two_pools_exact_in,
    staircase_jump_best_split_two_pools_exact_in,
)


def _random_cases(seed: int, n: int) -> list[tuple[PoolXY, PoolXY, int]]:
    rng = random.Random(seed)
    cases: list[tuple[PoolXY, PoolXY, int]] = []
    for _ in range(n):
        regime = rng.randrange(6)
        if regime == 0:  # balanced
            x0, y0 = rng.randint(50, 5000), rng.randint(50, 5000)
            x1, y1 = rng.randint(50, 5000), rng.randint(50, 5000)
            d = rng.randint(1, 3000)
        elif regime == 1:  # high fee gap (hard manifold for heuristics)
            x0, y0 = rng.randint(100, 2000), rng.randint(100, 2000)
            x1, y1 = rng.randint(100, 2000), rng.randint(100, 2000)
            d = rng.randint(100, 2500)
        elif regime == 2:  # deep amount vs thin reserve_in (amt_very_hi)
            x0, y0 = rng.randint(5, 60), rng.randint(100, 4000)
            x1, y1 = rng.randint(5, 60), rng.randint(100, 4000)
            d = rng.randint(100 * max(x0, x1), 200 * max(x0, x1))
        elif regime == 3:  # imbalanced reserves
            x0, y0 = rng.randint(20, 100), rng.randint(2000, 9000)
            x1, y1 = rng.randint(1000, 9000), rng.randint(20, 100)
            d = rng.randint(50, 2500)
        elif regime == 4:  # thin output reserve (plateau-heavy)
            x0, y0 = rng.randint(200, 3000), rng.randint(2, 40)
            x1, y1 = rng.randint(200, 3000), rng.randint(2, 40)
            d = rng.randint(100, 3000)
        else:  # tiny everything (degenerate windows)
            x0, y0 = rng.randint(1, 12), rng.randint(1, 12)
            x1, y1 = rng.randint(1, 12), rng.randint(1, 12)
            d = rng.randint(1, 40)
        f0 = rng.choice([0, 1, 5, 30, 100, 250, 999, 2500])
        f1 = rng.choice([0, 1, 5, 30, 100, 250, 999, 2500])
        cases.append((PoolXY(x0, y0, f0), PoolXY(x1, y1, f1), d))
    return cases


def test_staircase_matches_brute_force_exactly() -> None:
    """Bit-exact agreement (output AND canonical leftmost split) across regimes."""
    mismatches: list[str] = []
    for pool0, pool1, d in _random_cases(seed=20260612, n=400):
        try:
            expected = brute_force_best_split_two_pools_exact_in(pool0, pool1, d)
            expected_err = None
        except ValueError as exc:
            expected, expected_err = None, str(exc)
        try:
            got = staircase_jump_best_split_two_pools_exact_in(pool0, pool1, d)
            got_err = None
        except ValueError as exc:
            got, got_err = None, str(exc)
        if expected != got or (expected_err is None) != (got_err is None):
            mismatches.append(f"{pool0} {pool1} D={d}: brute={expected or expected_err} staircase={got or got_err}")
    assert not mismatches, "\n".join(mismatches[:10])


def test_staircase_quote_efficiency() -> None:
    """The staircase optimizer issues far fewer quotes than brute force.

    Quote count is bounded by ~2 per distinct pool-0 output level; in the
    deep-amount regime (D >> reserves) this is a large reduction versus the
    O(D) brute-force scan.
    """
    pool0 = PoolXY(x=40, y=900, fee_bps=30)
    pool1 = PoolXY(x=55, y=1100, fee_bps=100)
    d = 8000  # deep-amount regime: brute force would issue ~2*8001 quotes

    calls = {"n": 0}
    original = split_routing_mod.exact_out_for_pool_exact_in

    def counting(pool: PoolXY, amount_in: int) -> int:
        calls["n"] += 1
        return original(pool, amount_in)

    split_routing_mod.exact_out_for_pool_exact_in = counting
    try:
        got = staircase_jump_best_split_two_pools_exact_in(pool0, pool1, d)
    finally:
        split_routing_mod.exact_out_for_pool_exact_in = original

    expected = brute_force_best_split_two_pools_exact_in(pool0, pool1, d)
    assert got == expected
    # out0 is bounded by y0 = 900, so levels <= 900 and quotes <= ~2*900 + 4;
    # in practice far fewer levels are reachable within [lo, hi].
    assert calls["n"] <= 2 * 900 + 4, calls["n"]
    assert calls["n"] < (d + 1), f"no better than brute force: {calls['n']}"


def test_staircase_v1_profile_wiring() -> None:
    """`search_profile="staircase_v1"` routes to the exact optimizer through the
    standard entrypoint (and hence through the dispatch layer, which passes
    non-adaptive profiles through unchanged)."""
    from src.core.split_routing import best_split_two_pools_exact_in

    for pool0, pool1, d in _random_cases(seed=777, n=60):
        try:
            expected = brute_force_best_split_two_pools_exact_in(pool0, pool1, d)
            expected_err = None
        except ValueError:
            expected, expected_err = None, "err"
        try:
            got = best_split_two_pools_exact_in(
                pool0, pool1, d, search_profile="staircase_v1"
            )
            got_err = None
        except ValueError:
            got, got_err = None, "err"
        assert (expected, expected_err) == (got, got_err), (pool0, pool1, d)


def test_staircase_single_pool_endpoints() -> None:
    """Cases where one pool is unusable must fall back to the endpoints."""
    # pool1 can never produce output (y=1, x>0): best split sends all to pool0.
    pool0 = PoolXY(x=100, y=1000, fee_bps=30)
    pool1 = PoolXY(x=100, y=1, fee_bps=30)
    d = 500
    assert staircase_jump_best_split_two_pools_exact_in(pool0, pool1, d) == \
        brute_force_best_split_two_pools_exact_in(pool0, pool1, d)

    # fee 100% on pool0: net is never positive there.
    pool0_dead = PoolXY(x=100, y=1000, fee_bps=10_000)
    assert staircase_jump_best_split_two_pools_exact_in(pool0_dead, pool0, d) == \
        brute_force_best_split_two_pools_exact_in(pool0_dead, pool0, d)
