from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_EXECUTION_GUARD_V1,
    build_autotrader_execution_guard_v1_step,
)


def test_build_autotrader_execution_guard_v1_step() -> None:
    step = build_autotrader_execution_guard_v1_step(
        current_epoch=10,
        valid_from_epoch=1,
        valid_until_epoch=100,
        last_action_known=1,
        last_action_epoch=5,
        cadence_epochs=4,
        min_order_spacing_epochs=2,
        projected_live_orders=2,
        max_live_orders=3,
    )
    assert AUTOTRADER_EXECUTION_GUARD_V1.spec_id == "autotrader_execution_guard_v1"
    assert step == {
        "i1": 10,
        "i2": 1,
        "i3": 100,
        "i4": 1,
        "i5": 5,
        "i6": 4,
        "i7": 2,
        "i8": 2,
        "i9": 3,
    }


def test_build_autotrader_execution_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="last_action_known must be 0 or 1"):
        build_autotrader_execution_guard_v1_step(
            current_epoch=10,
            valid_from_epoch=1,
            valid_until_epoch=100,
            last_action_known=2,
            last_action_epoch=5,
            cadence_epochs=4,
            min_order_spacing_epochs=2,
            projected_live_orders=2,
            max_live_orders=3,
        )
