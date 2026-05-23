from __future__ import annotations

from src.integration.tau_witness import (
    AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1,
    build_autotrader_oracle_freshness_guard_v1_step,
)


def test_build_autotrader_oracle_freshness_guard_v1_step() -> None:
    step = build_autotrader_oracle_freshness_guard_v1_step(
        current_epoch=10,
        quote_epoch=8,
        max_oracle_staleness_epochs=3,
    )
    assert AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1.spec_id == "autotrader_oracle_freshness_guard_v1"
    assert step == {
        "i1": 10,
        "i2": 8,
        "i3": 3,
    }
