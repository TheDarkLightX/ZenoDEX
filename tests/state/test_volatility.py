from __future__ import annotations

import pytest

from src.state.volatility import BPS_DENOM, TierState, tier_effects


def test_tier_state_accepts_ordered_thresholds() -> None:
    state = TierState(tier=2, last_epoch=7, t1_bps=1000, t2_bps=3000, t3_bps=8000)

    assert state.tier == 2
    assert state.last_epoch == 7


def test_tier_effects_match_expected_table() -> None:
    assert tier_effects(0).fee_mult_bps == 10_000
    assert tier_effects(1).fee_mult_bps == 20_000
    assert tier_effects(2).max_trade_bps == 1_000
    assert tier_effects(3).halt is True


@pytest.mark.parametrize(
    "kwargs",
    [
        {"tier": 4},
        {"last_epoch": -1},
        {"t1_bps": 2000, "t2_bps": 1000, "t3_bps": 3000},
        {"t1_bps": 0, "t2_bps": BPS_DENOM + 1, "t3_bps": BPS_DENOM + 1},
    ],
)
def test_tier_state_rejects_invalid_ranges(kwargs: dict[str, int]) -> None:
    with pytest.raises((TypeError, ValueError)):
        TierState(**kwargs)


@pytest.mark.parametrize("tier", [-1, 4])
def test_tier_effects_rejects_out_of_range_tier(tier: int) -> None:
    with pytest.raises(ValueError):
        tier_effects(tier)
