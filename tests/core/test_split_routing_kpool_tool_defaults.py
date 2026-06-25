"""Regression tests for k-pool staircase evidence-tool defaults."""

from __future__ import annotations

from tools.benchmark_kpool_staircase import (
    all_benchmark_cases,
    default_benchmark_cases,
    performance_benchmark_cases,
)
from tools.profile_state_counts import profile_staircase
from src.core.split_routing import PoolXY


def test_kpool_benchmark_defaults_exclude_large_performance_cases() -> None:
    default_cases = default_benchmark_cases()
    performance_cases = performance_benchmark_cases()

    assert default_cases
    assert performance_cases
    assert len(all_benchmark_cases()) == len(default_cases) + len(performance_cases)
    assert all("performance" not in case.tags for case in default_cases)
    assert all("performance" in case.tags for case in performance_cases)
    assert max(case.amount_in for case in default_cases) <= 300


def test_kpool_profile_tracks_per_interior_residual_quote_counts() -> None:
    profile = profile_staircase(
        [
            ("a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
            ("b", PoolXY(x=8_000, y=12_000, fee_bps=30)),
            ("c", PoolXY(x=12_000, y=8_000, fee_bps=30)),
        ],
        amount_in_total=40,
        max_legs=3,
    )

    assert len(profile.residual_quote_counts) == 3
    assert profile.residual_quotes == sum(profile.residual_quote_counts)
    assert max(profile.residual_quote_counts) <= profile.max_residual_quotes
