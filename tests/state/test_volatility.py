from __future__ import annotations

import pytest

from src.state.volatility import TierEffects, TierState, tier_effects


def test_tier_state_accepts_valid_defaults() -> None:
    state = TierState()
    assert state.tier == 0
    assert state.last_epoch == 0


@pytest.mark.parametrize("field", ["tier", "last_epoch", "t1_bps", "t2_bps", "t3_bps"])
def test_tier_state_rejects_non_int_fields(field: str) -> None:
    kwargs = {field: True}

    with pytest.raises(TypeError, match=f"{field} must be an int"):
        TierState(**kwargs)


def test_tier_state_rejects_out_of_range_tier() -> None:
    with pytest.raises(ValueError, match="tier must be in \\[0, 3\\]"):
        TierState(tier=4)


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


def test_tier_state_rejects_unordered_thresholds() -> None:
    with pytest.raises(ValueError, match="thresholds must be ordered"):
        TierState(t1_bps=7000, t2_bps=6000, t3_bps=8000)


def test_tier_effects_dataclass_rejects_non_int_and_non_bool_fields() -> None:
    with pytest.raises(TypeError, match="tier_out must be an int"):
        TierEffects(tier_out=True, fee_mult_bps=10_000, max_trade_bps=10_000, halt=False)

    with pytest.raises(TypeError, match="max_trade_bps must be an int"):
        TierEffects(tier_out=0, fee_mult_bps=10_000, max_trade_bps=True, halt=False)

    with pytest.raises(TypeError, match="fee_mult_bps must be an int"):
        TierEffects(tier_out=0, fee_mult_bps=True, max_trade_bps=10_000, halt=False)

    with pytest.raises(TypeError, match="halt must be a bool"):
        TierEffects(tier_out=0, fee_mult_bps=10_000, max_trade_bps=10_000, halt=1)  # type: ignore[arg-type]


def test_tier_effects_returns_expected_halt_tier() -> None:
    effects = tier_effects(3)
    assert effects.tier_out == 3
    assert effects.fee_mult_bps == 0
    assert effects.max_trade_bps == 0
    assert effects.halt is True


def test_tier_effects_rejects_out_of_range_tier() -> None:
    with pytest.raises(ValueError, match="tier must be in \\[0, 3\\]"):
        tier_effects(4)


@pytest.mark.parametrize("tier", [True, "1"])
def test_tier_effects_rejects_non_int_tier(tier: object) -> None:
    # REVIEW [B -> A-]: this pins the bool-as-int helper leak found after the
    # dataclass boundary was already strict.
    with pytest.raises(TypeError, match="tier must be an int"):
        tier_effects(tier)  # type: ignore[arg-type]
