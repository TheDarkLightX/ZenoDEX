from __future__ import annotations

import pytest

from src.kernels.python.strategy_oracle_freshness_guard_v1_adapter import check_oracle_freshness


def test_check_oracle_freshness_accepts_fresh_quote() -> None:
    result = check_oracle_freshness(
        current_epoch=10,
        quote_epoch=8,
        max_oracle_staleness_epochs=3,
    )
    assert result.ok is True
    assert result.age_epochs == 2
    assert result.error is None


def test_check_oracle_freshness_skips_stale_quote() -> None:
    result = check_oracle_freshness(
        current_epoch=10,
        quote_epoch=6,
        max_oracle_staleness_epochs=3,
    )
    assert result.ok is False
    assert result.error == "quote_receipt_stale:age=4,max=3"


def test_check_oracle_freshness_rejects_future_quote_epoch() -> None:
    result = check_oracle_freshness(
        current_epoch=10,
        quote_epoch=11,
        max_oracle_staleness_epochs=3,
    )
    assert result.ok is False
    assert result.error == "quote_epoch_in_future:11>10"


def test_check_oracle_freshness_rejects_invalid_types_and_ranges() -> None:
    with pytest.raises(TypeError, match="current_epoch must be an int"):
        check_oracle_freshness(
            current_epoch="10",
            quote_epoch=8,
            max_oracle_staleness_epochs=3,
        )
    with pytest.raises(ValueError, match="quote_epoch out of u32 range"):
        check_oracle_freshness(
            current_epoch=10,
            quote_epoch=-1,
            max_oracle_staleness_epochs=3,
        )
    with pytest.raises(ValueError, match="max_oracle_staleness_epochs out of u32 range"):
        check_oracle_freshness(
            current_epoch=10,
            quote_epoch=8,
            max_oracle_staleness_epochs=0,
        )
