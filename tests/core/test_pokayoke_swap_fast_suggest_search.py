from __future__ import annotations

from src.core.pokayoke_swap_fast_suggest import (
    suggest_amount_in_for_impact_lt_bps,
    suggest_amount_in_for_required_slippage_le_bps,
)


def test_fast_impact_suggestion_preserves_integer_boundary_and_eval_count() -> None:
    suggestion = suggest_amount_in_for_impact_lt_bps(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        amount_in=1000,
        target_impact_bps=500,
        window=256,
    )

    assert suggestion.status == "ok"
    assert suggestion.suggested_amount_in == 45
    assert suggestion.eval_count == 265
    assert suggestion.baseline_value_bps == 5000
    assert suggestion.suggested_value_bps == 444


def test_fast_required_slippage_suggestion_preserves_probe_order() -> None:
    suggestion = suggest_amount_in_for_required_slippage_le_bps(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        amount_in=50,
        pending_volume_same_direction=20,
        confidence_bps=9500,
        target_required_slippage_bps=218,
        window=64,
    )

    assert suggestion.status == "ok"
    assert suggestion.suggested_amount_in == 49
    assert suggestion.eval_count == 6
    assert suggestion.baseline_value_bps == 426
    assert suggestion.suggested_value_bps == 218
