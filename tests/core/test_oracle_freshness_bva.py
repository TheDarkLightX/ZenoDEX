"""BVA tests for oracle freshness (`src/core/oracle.py`)."""

from __future__ import annotations

import pytest

from src.core.oracle import OracleState, init_oracle_state, is_fresh, update_price_timestamp


class TestOracleFreshnessBVA:
    @pytest.mark.parametrize(
        "max_staleness,expect_ok,reason",
        [
            (0, False, "just below min=1"),
            (1, True, "at min"),
            (2, True, "just above min"),
        ],
    )
    def test_init_staleness_bounds(self, max_staleness: int, expect_ok: bool, reason: str) -> None:
        if expect_ok:
            s = init_oracle_state(max_staleness_seconds=max_staleness)
            assert s.max_staleness_seconds == max_staleness, reason
            assert s.price_timestamp == 0, reason
        else:
            with pytest.raises(ValueError):
                init_oracle_state(max_staleness_seconds=max_staleness)

    def test_is_fresh_rejects_negative_current_timestamp(self) -> None:
        s = init_oracle_state(max_staleness_seconds=300)
        with pytest.raises(ValueError):
            is_fresh(s, current_timestamp=-1)

    def test_is_fresh_future_price_timestamp_is_false(self) -> None:
        s = OracleState(price_timestamp=200, max_staleness_seconds=300)
        assert is_fresh(s, current_timestamp=199) is False

    def test_is_fresh_staleness_boundary(self) -> None:
        s = OracleState(price_timestamp=1000, max_staleness_seconds=300)
        assert is_fresh(s, current_timestamp=1299) is True   # just below
        assert is_fresh(s, current_timestamp=1300) is True   # at
        assert is_fresh(s, current_timestamp=1301) is False  # just above

    def test_update_price_timestamp_bva(self) -> None:
        s = init_oracle_state(max_staleness_seconds=300)
        with pytest.raises(ValueError):
            update_price_timestamp(s, current_timestamp=-1)

        s2 = update_price_timestamp(s, current_timestamp=0)
        assert s2.price_timestamp == 0

        s3 = update_price_timestamp(s2, current_timestamp=1)
        assert s3.price_timestamp == 1

