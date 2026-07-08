from __future__ import annotations

import pytest

from src.state.volatility import TierEffects, TierState, tier_effects


def test_tier_state_rejects_negative_last_epoch() -> None:
    with pytest.raises(ValueError, match="last_epoch must be non-negative"):
        TierState(last_epoch=-1)


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("t1_bps", -1),
        ("t2_bps", 10_001),
        ("t3_bps", 10_001),
    ],
)
def test_tier_state_rejects_out_of_range_thresholds(field: str, value: int) -> None:
    kwargs = {field: value}

    with pytest.raises(ValueError, match=field):
        TierState(**kwargs)


def test_tier_effects_dataclass_rejects_non_int_and_non_bool_fields() -> None:
    with pytest.raises(TypeError, match="tier_out must be an int"):
        TierEffects(tier_out=True, fee_mult_bps=10_000, max_trade_bps=10_000, halt=False)

    with pytest.raises(TypeError, match="max_trade_bps must be an int"):
        TierEffects(tier_out=0, fee_mult_bps=10_000, max_trade_bps=True, halt=False)

    with pytest.raises(TypeError, match="halt must be a bool"):
        TierEffects(tier_out=0, fee_mult_bps=10_000, max_trade_bps=10_000, halt=1)  # type: ignore[arg-type]


def test_tier_effects_rejects_out_of_range_tier() -> None:
    with pytest.raises(ValueError, match="tier must be in \\[0, 3\\]"):
        tier_effects(4)
