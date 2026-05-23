from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_BUDGET_GUARD_V1,
    build_autotrader_budget_guard_v1_step,
)


def test_build_autotrader_budget_guard_v1_step() -> None:
    step = build_autotrader_budget_guard_v1_step(
        spent_before=100,
        order_amount=50,
        per_order_limit=100,
        window_budget=500,
        spent_after=150,
        kill_switch_active=0,
    )
    assert AUTOTRADER_BUDGET_GUARD_V1.spec_id == "autotrader_budget_guard_v1"
    assert step == {
        "i1": 100,
        "i2": 50,
        "i3": 100,
        "i4": 500,
        "i5": 150,
        "i6": 0,
    }


def test_build_autotrader_budget_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="kill_switch_active must be 0 or 1"):
        build_autotrader_budget_guard_v1_step(
            spent_before=100,
            order_amount=50,
            per_order_limit=100,
            window_budget=500,
            spent_after=150,
            kill_switch_active=2,
        )
