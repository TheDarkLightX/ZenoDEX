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


def test_default_adaptive_v6_recovers_known_gap_case():
    # Default profile should resolve this case to a high-coverage search and match oracle.
    p0 = PoolXY(x=87, y=80, fee_bps=75)
    p1 = PoolXY(x=46, y=66, fee_bps=11)
    amt = 6539
    best_out_bf, best_a_bf = brute_force_best_split_two_pools_exact_in(p0, p1, amt)

    default_out, default_a = best_split_two_pools_exact_in(p0, p1, amt, window=64)
    assert default_out == best_out_bf
    assert default_a == best_a_bf


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


def test_adaptive_v6_escalates_to_dense32_in_high_pressure_small_out_regime():
    # Stress witness family where dense24 can miss by 1; v6 escalates to dense32.
    p0 = PoolXY(x=108, y=48, fee_bps=85)
    p1 = PoolXY(x=83, y=41, fee_bps=35)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 8533, search_profile="adaptive_v6", window=96)
    assert (win, prof) == (96, "dense32")


def test_adaptive_v6_extreme_regime_escalates_to_dense32_w128():
    p0 = PoolXY(x=102, y=31, fee_bps=193)
    p1 = PoolXY(x=132, y=92, fee_bps=177)
    win, prof = resolve_two_pool_split_search_params(p0, p1, 13704, search_profile="adaptive_v6", window=96)
    assert (win, prof) == (128, "dense32")


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


# ---------------------------------------------------------------------------
# Characterization grid for resolve_two_pool_split_search_params.
#
# This pins the (window, profile) resolution across EVERY profile branch —
# including adaptive_v2/v3/v5, which previously had no direct unit coverage on
# resolve_two_pool_split_search_params. The grid output is frozen as a SHA so a
# behavior-preserving refactor of the resolver must reproduce it byte-for-byte.
# Regenerate intentionally only with a deliberate, reviewed behavior change.
# ---------------------------------------------------------------------------

_CHAR_GRID_XS = (1, 42, 100, 200, 400, 1000)
_CHAR_GRID_YS = (3, 32, 48, 64, 80, 100, 1000)
_CHAR_GRID_FEES = (0, 11, 30, 60, 90, 110, 145, 177, 195)
_CHAR_GRID_AMTS = (0, 1, 50, 5925, 6055, 6145, 6539, 8533, 13704)
_CHAR_GRID_PROFILES = (
    "baseline",
    "dense24",
    "dense32",
    "baseline_canon16",
    "dgstr_v1",
    "adaptive_v1",
    "adaptive_v2",
    "adaptive_v3",
    "adaptive_v4",
    "adaptive_v5",
    "adaptive_v6",
    "adaptive_v7",
    "unknown_mode",
)
# Hand-picked pairs spanning imbalance / near-symmetric / thin-out manifolds.
_CHAR_GRID_STRUCT = (
    (87, 80, 75, 46, 66, 11),
    (42, 42, 58, 172, 317, 14),
    (173, 38, 3, 199, 80, 31),
    (108, 48, 85, 83, 41, 35),
    (102, 31, 193, 132, 92, 177),
    (125, 153, 119, 125, 140, 150),
    (40, 20, 0, 40, 63, 0),
    (1000, 5, 0, 1000, 5, 0),
    (1, 336, 438, 378, 5, 50),
    (2, 115, 424, 189, 3, 157),
    (200, 200, 0, 200, 200, 0),
    (50, 50, 500, 50, 50, 30),
)
# Frozen golden digest of the grid below, captured on the pre-refactor
# implementation (commit baseline). Any drift in resolver output changes it.
_CHAR_GRID_GOLDEN_SHA = (
    "e29d7dc41f08fd89b78cee80a11944e51bd3cecffa1fbd5b34cd6a4a5778aa50"
)


def _build_resolver_char_grid() -> list:
    import random as _random

    rng = _random.Random(20260607)
    pairs = [((a, b, c), (d, e, f)) for (a, b, c, d, e, f) in _CHAR_GRID_STRUCT]
    for _ in range(40):
        pairs.append(
            (
                (rng.choice(_CHAR_GRID_XS), rng.choice(_CHAR_GRID_YS), rng.choice(_CHAR_GRID_FEES)),
                (rng.choice(_CHAR_GRID_XS), rng.choice(_CHAR_GRID_YS), rng.choice(_CHAR_GRID_FEES)),
            )
        )

    rows = []
    for (p0, p1) in pairs:
        for amt in _CHAR_GRID_AMTS:
            for prof in _CHAR_GRID_PROFILES:
                try:
                    win, profile = resolve_two_pool_split_search_params(
                        PoolXY(*p0), PoolXY(*p1), amt, search_profile=prof, window=96
                    )
                    out = ["ok", win, profile]
                except Exception as exc:  # noqa: BLE001 - characterization of raises
                    out = ["err", type(exc).__name__, str(exc)]
                rows.append([list(p0), list(p1), amt, prof, out])
    return rows


def test_resolver_characterization_grid_is_stable() -> None:
    import hashlib
    import json

    rows = _build_resolver_char_grid()
    # 52 pairs (12 structured + 40 seeded-random) * 9 amounts * 13 profiles
    n_pairs = len(_CHAR_GRID_STRUCT) + 40
    assert len(rows) == n_pairs * len(_CHAR_GRID_AMTS) * len(_CHAR_GRID_PROFILES)
    digest = hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest()
    assert digest == _CHAR_GRID_GOLDEN_SHA, (
        "resolve_two_pool_split_search_params output drifted from frozen golden grid"
    )


# ---------------------------------------------------------------------------
# Boundary teeth (max / max+1 / zero / impossible-route).
#
# Each asserts an exact (window, profile) at a tier threshold so that flipping a
# >= to > (or moving a constant by one) flips the result and fails the test.
# ---------------------------------------------------------------------------


def test_tooth_zero_amount_returns_window_and_baseline() -> None:
    # amount_in <= 0 must short-circuit to (passed window, "baseline") BEFORE any
    # signal/tier logic, for every adaptive profile.
    p0 = PoolXY(x=100, y=100, fee_bps=10)
    p1 = PoolXY(x=100, y=100, fee_bps=10)
    for prof in (
        "adaptive_v1",
        "adaptive_v2",
        "adaptive_v3",
        "adaptive_v4",
        "adaptive_v5",
        "adaptive_v6",
        "adaptive_v7",
    ):
        assert resolve_two_pool_split_search_params(
            p0, p1, 0, search_profile=prof, window=77
        ) == (77, "baseline")
        assert resolve_two_pool_split_search_params(
            p0, p1, -1, search_profile=prof, window=77
        ) == (77, "baseline")


def test_tooth_non_adaptive_passthrough_returns_raw_profile_and_window() -> None:
    # Non-adaptive profile names pass through unchanged: the RAW search_profile
    # string (not a normalized/lowercased form) and the RAW window.
    p0 = PoolXY(x=100, y=100, fee_bps=10)
    p1 = PoolXY(x=100, y=100, fee_bps=10)
    assert resolve_two_pool_split_search_params(
        p0, p1, 5000, search_profile="Dense24", window=42
    ) == (42, "Dense24")
    assert resolve_two_pool_split_search_params(
        p0, p1, 5000, search_profile="baseline", window=13
    ) == (13, "baseline")


def test_tooth_fee_gap_high_threshold_v1_60_boundary() -> None:
    # adaptive_v1 `high` triggers at fee_gap >= 60. Build a regime where fee_gap
    # is the ONLY high signal: equal large reserves (no imbalance/near-sym in the
    # small-reserve sense), modest amount (amt_med false at D < 40*min_x).
    # min_x = 5000, so D = 50_000 < 40*5000 = 200_000 keeps amt_med False.
    below = PoolXY(x=5000, y=5000, fee_bps=0)
    below_hi = PoolXY(x=5000, y=5000, fee_bps=59)  # fee_gap = 59 -> not high, not med (>=30 true!)
    # fee_gap 59 >= 30 => med True, high False => v1 returns (64, "dense24")
    win, prof = resolve_two_pool_split_search_params(
        below, below_hi, 50_000, search_profile="adaptive_v1", window=96
    )
    assert (win, prof) == (64, "dense24")
    # fee_gap 60 -> high True => v1 returns (96, "dense24")
    at_hi = PoolXY(x=5000, y=5000, fee_bps=60)
    win, prof = resolve_two_pool_split_search_params(
        below, at_hi, 50_000, search_profile="adaptive_v1", window=96
    )
    assert (win, prof) == (96, "dense24")


def test_tooth_fee_gap_med_threshold_v1_30_boundary() -> None:
    # adaptive_v1 `med` triggers at fee_gap >= 30 (when not high). Straddle 29/30
    # with large equal reserves and a sub-amt_med amount so only fee_gap matters.
    base = PoolXY(x=5000, y=5000, fee_bps=0)
    # fee_gap 29 -> not med, not high => v1 returns (64, "baseline")
    win, prof = resolve_two_pool_split_search_params(
        base, PoolXY(x=5000, y=5000, fee_bps=29), 50_000, search_profile="adaptive_v1", window=96
    )
    assert (win, prof) == (64, "baseline")
    # fee_gap 30 -> med => v1 returns (64, "dense24")
    win, prof = resolve_two_pool_split_search_params(
        base, PoolXY(x=5000, y=5000, fee_bps=30), 50_000, search_profile="adaptive_v1", window=96
    )
    assert (win, prof) == (64, "dense24")


def test_tooth_amt_med_threshold_40x_min_x_boundary() -> None:
    # amt_med := (D >= 40*min_x). With min_x = 100, threshold D = 4000. Keep
    # fee_gap below med (0) and reserves large/equal so amt_med is the only
    # `high` driver in adaptive_v1.
    p = PoolXY(x=100, y=5000, fee_bps=0)
    q = PoolXY(x=100, y=5000, fee_bps=0)
    # D = 3999 < 4000 => amt_med False, no high/med => (64, "baseline")
    win, prof = resolve_two_pool_split_search_params(p, q, 3999, search_profile="adaptive_v1", window=96)
    assert (win, prof) == (64, "baseline")
    # D = 4000 == 4000 => amt_med True => high True => (96, "dense24")
    win, prof = resolve_two_pool_split_search_params(p, q, 4000, search_profile="adaptive_v1", window=96)
    assert (win, prof) == (96, "dense24")


def test_tooth_impossible_route_amount_in_zero_raises() -> None:
    # The resolver itself never rejects, but the split entrypoint does. An
    # "impossible route" (amount_in <= 0) must raise on the search entrypoint,
    # and a single empty/zero-output pool must raise in the leg quoter.
    p0 = PoolXY(x=1000, y=1000, fee_bps=0)
    p1 = PoolXY(x=1000, y=1000, fee_bps=0)
    with pytest.raises(ValueError, match="amount_in must be positive"):
        best_split_two_pools_exact_in(p0, p1, 0)
    with pytest.raises(ValueError, match="amount_in must be positive"):
        best_split_two_pools_exact_in(p0, p1, -5)


def test_tooth_impossible_route_empty_reserve_raises() -> None:
    # Degenerate pool with empty reserve cannot be swapped against.
    empty = PoolXY(x=0, y=1000, fee_bps=0)
    with pytest.raises(ValueError, match="cannot swap against empty reserve"):
        exact_out_for_pool_exact_in(empty, 100)
