from __future__ import annotations

from src.core.pokayoke_swap_suggest import _candidate_amount_schedule


def test_candidate_amount_schedule_prioritizes_high_impact_threshold_window() -> None:
    schedule = _candidate_amount_schedule(
        reserve_in=1000,
        fee_bps=0,
        amount_in=1000,
        baseline_reasons=("high_price_impact",),
    )

    assert schedule[:25] == list(range(64, 39, -1))
    assert 45 in schedule
    assert len(schedule) == len(set(schedule))


def test_candidate_amount_schedule_keeps_generic_ladder_order_and_unique_fallbacks() -> None:
    schedule = _candidate_amount_schedule(
        reserve_in=1000,
        fee_bps=0,
        amount_in=1000,
        baseline_reasons=(),
    )

    assert schedule[:6] == [500, 333, 250, 200, 150, 100]
    assert schedule[-4:] == [10, 1, 2, 5]
    assert len(schedule) == len(set(schedule))
