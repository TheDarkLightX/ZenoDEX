from __future__ import annotations

import pytest

from src.core import split_routing as split_routing_mod
from src.core.split_routing import (
    PoolXY,
    best_split_two_pools_exact_in,
    brute_force_best_split_two_pools_exact_in,
    exact_out_for_pool_exact_in,
    resolve_two_pool_split_search_params,
)
from tools.metamuse_split_routing_lane import DGSTR_CURATED_CASES


def _count_profile_calls(
    pool0: PoolXY,
    pool1: PoolXY,
    amount_in: int,
    *,
    search_profile: str,
) -> tuple[tuple[int, int], int]:
    orig = split_routing_mod.exact_out_for_pool_exact_in
    calls = {"n": 0}

    def wrapped(pool: PoolXY, amount: int) -> int:
        calls["n"] = int(calls["n"]) + 1
        return orig(pool, amount)

    split_routing_mod.exact_out_for_pool_exact_in = wrapped  # type: ignore[assignment]
    try:
        result = best_split_two_pools_exact_in(
            pool0,
            pool1,
            amount_in,
            window=64,
            search_profile=search_profile,
        )
    finally:
        split_routing_mod.exact_out_for_pool_exact_in = orig  # type: ignore[assignment]
    return result, int(calls["n"])


def test_split_matches_bruteforce_small():
    p0 = PoolXY(x=1000, y=1000, fee_bps=0)
    p1 = PoolXY(x=1000, y=1000, fee_bps=0)
    # amt=1 yields zero output in both pools (kernel rejects), so start at 2.
    for amt in [2, 3, 5, 10, 25, 50]:
        best_out_bf, best_a_bf = brute_force_best_split_two_pools_exact_in(p0, p1, amt)
        best_out, best_a = best_split_two_pools_exact_in(p0, p1, amt, window=64)
        assert best_out == best_out_bf
        assert best_a == best_a_bf


def test_bruteforce_propagates_internal_quote_fault(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken(_pool: PoolXY, _amount_in: int) -> int:
        raise RuntimeError("internal split quote fault")

    monkeypatch.setattr(split_routing_mod, "exact_out_for_pool_exact_in", broken)

    with pytest.raises(RuntimeError, match="internal split quote fault"):
        brute_force_best_split_two_pools_exact_in(
            PoolXY(x=1000, y=1000, fee_bps=0),
            PoolXY(x=1000, y=1000, fee_bps=0),
            10,
        )


def test_heuristic_propagates_internal_quote_fault(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken(_pool: PoolXY, _amount_in: int) -> int:
        raise RuntimeError("internal split quote fault")

    monkeypatch.setattr(split_routing_mod, "exact_out_for_pool_exact_in", broken)

    with pytest.raises(RuntimeError, match="internal split quote fault"):
        best_split_two_pools_exact_in(
            PoolXY(x=20_000, y=20_000, fee_bps=30),
            PoolXY(x=24_000, y=18_000, fee_bps=30),
            20_000,
            window=64,
            search_profile="baseline",
        )


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


def test_dense_profile_recovers_known_gap_case():
    # Manual witness (M001): baseline misses by 1, dense profile should recover oracle output.
    p0 = PoolXY(x=87, y=80, fee_bps=75)
    p1 = PoolXY(x=46, y=66, fee_bps=11)
    amt = 6539
    best_out_bf, best_a_bf = brute_force_best_split_two_pools_exact_in(p0, p1, amt)

    base_out, _base_a = best_split_two_pools_exact_in(p0, p1, amt, window=64, search_profile="baseline")
    dense_out, dense_a = best_split_two_pools_exact_in(p0, p1, amt, window=64, search_profile="dense24")

    assert base_out < best_out_bf
    assert dense_out == best_out_bf
    assert dense_a == best_a_bf


def test_default_adaptive_v6_uses_budgeted_staircase_on_known_gap_case():
    # Default profile should use the Lean-backed exact optimizer when the
    # output-level budget is small enough for production routing.
    p0 = PoolXY(x=87, y=80, fee_bps=75)
    p1 = PoolXY(x=46, y=66, fee_bps=11)
    amt = 6539
    best_out_bf, best_a_bf = brute_force_best_split_two_pools_exact_in(p0, p1, amt)

    win, prof = resolve_two_pool_split_search_params(p0, p1, amt, search_profile="adaptive_v6", window=96)
    assert (win, prof) == (0, "staircase_v1")

    (default_out, default_a), default_calls = _count_profile_calls(p0, p1, amt, search_profile="adaptive_v6")
    (dense_out, dense_a), dense_calls = _count_profile_calls(p0, p1, amt, search_profile="dense32")
    assert default_out == best_out_bf
    assert default_a == best_a_bf
    assert (dense_out, dense_a) == (best_out_bf, best_a_bf)
    assert default_calls < dense_calls


def test_unknown_search_profile_rejected():
    p0 = PoolXY(x=100, y=100, fee_bps=10)
    p1 = PoolXY(x=100, y=100, fee_bps=10)
    try:
        best_split_two_pools_exact_in(p0, p1, 1000, search_profile="unknown_mode")
    except ValueError as exc:
        assert "unsupported search_profile" in str(exc)
    else:
        assert False, "expected ValueError for unknown search profile"


def test_adaptive_v1_resolves_to_expected_hardness_tier_on_known_hard_cases():
    # Adaptive policy is a heuristic; this test only checks the deterministic tier selection,
    # not global optimality.
    p0 = PoolXY(x=87, y=80, fee_bps=75)
    p1 = PoolXY(x=46, y=66, fee_bps=11)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 6539, search_profile="adaptive_v1", window=96)
    assert (win, prof) == (96, "dense24")

    p0 = PoolXY(x=42, y=42, fee_bps=58)
    p1 = PoolXY(x=172, y=317, fee_bps=14)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 6145, search_profile="adaptive_v1", window=96)
    assert (win, prof) == (96, "dense24")


def test_adaptive_v4_resolves_to_strict_escalation_tiers():
    # Hard regime: escalate to dense24/w96.
    p0 = PoolXY(x=87, y=80, fee_bps=75)
    p1 = PoolXY(x=46, y=66, fee_bps=11)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 6539, search_profile="adaptive_v4", window=96)
    assert (win, prof) == (96, "dense24")

    # Moderate regime: stay on baseline_canon16/w64.
    p0 = PoolXY(x=173, y=38, fee_bps=3)
    p1 = PoolXY(x=199, y=80, fee_bps=31)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 5925, search_profile="adaptive_v4", window=96)
    assert (win, prof) == (64, "baseline_canon16")


def test_adaptive_v6_uses_staircase_in_high_pressure_small_out_regime():
    # Stress witness family where dense24 can miss by 1; v6 now uses the exact
    # staircase path because the output-level budget is small.
    p0 = PoolXY(x=108, y=48, fee_bps=85)
    p1 = PoolXY(x=83, y=41, fee_bps=35)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 8533, search_profile="adaptive_v6", window=96)
    assert (win, prof) == (0, "staircase_v1")


def test_adaptive_v6_extreme_regime_uses_staircase_when_budgeted():
    p0 = PoolXY(x=102, y=31, fee_bps=193)
    p1 = PoolXY(x=132, y=92, fee_bps=177)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 13704, search_profile="adaptive_v6", window=96)
    assert (win, prof) == (0, "staircase_v1")


def test_adaptive_v6_keeps_heuristic_when_staircase_budget_is_large():
    # Deep, high-output pools would make jump enumeration too expensive; keep
    # the bounded heuristic in that regime.
    p0 = PoolXY(x=20_000, y=20_000, fee_bps=30)
    p1 = PoolXY(x=24_000, y=18_000, fee_bps=30)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 20_000, search_profile="adaptive_v6", window=96)
    assert (win, prof) == (64, "baseline_canon16")


@pytest.mark.parametrize(
    "pool0,pool1,amount_in,expected",
    [(case.pool0, case.pool1, case.amount_in, case.expected) for case in DGSTR_CURATED_CASES],
)
def test_dgstr_v1_matches_bruteforce_on_curated_easy_corpus(
    pool0: PoolXY,
    pool1: PoolXY,
    amount_in: int,
    expected: tuple[int, int],
) -> None:
    brute = brute_force_best_split_two_pools_exact_in(pool0, pool1, amount_in)
    got = best_split_two_pools_exact_in(pool0, pool1, amount_in, window=64, search_profile="dgstr_v1")
    assert brute == expected
    assert got == expected


def test_dgstr_v1_reduces_quote_calls_on_curated_easy_corpus() -> None:
    dgstr_calls = 0
    base_calls = 0
    for case in DGSTR_CURATED_CASES:
        pool0, pool1, amount_in, expected = case.pool0, case.pool1, case.amount_in, case.expected
        got_dgstr, calls_dgstr = _count_profile_calls(pool0, pool1, amount_in, search_profile="dgstr_v1")
        got_base, calls_base = _count_profile_calls(pool0, pool1, amount_in, search_profile="baseline_canon16")
        assert got_dgstr == expected
        assert got_base == expected
        dgstr_calls += int(calls_dgstr)
        base_calls += int(calls_base)
    assert dgstr_calls < base_calls
    assert dgstr_calls * 4 <= base_calls * 3


def test_adaptive_v7_routes_easy_manifold_to_dgstr_v1() -> None:
    p0 = PoolXY(x=125, y=153, fee_bps=119)
    p1 = PoolXY(x=125, y=140, fee_bps=150)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 6055, search_profile="adaptive_v7", window=96)
    assert (win, prof) == (64, "dgstr_v1")


def test_adaptive_v7_keeps_dense32_on_known_hard_regime() -> None:
    p0 = PoolXY(x=108, y=48, fee_bps=85)
    p1 = PoolXY(x=83, y=41, fee_bps=35)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 8533, search_profile="adaptive_v7", window=96)
    assert (win, prof) == (96, "dense32")
