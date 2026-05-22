"""BVA + invariants for fee splitting (`src/core/fees.py`)."""

from __future__ import annotations

import pytest

from src.core.fees import (
    BPS_DENOM,
    FeeAccumulatorState,
    FeeSplitParams,
    split_fee_with_dust_carry,
)


class TestFeeSplitParamsBVA:
    def test_bps_sum_must_be_exact(self) -> None:
        FeeSplitParams(buyback_bps=0, treasury_bps=0, rewards_bps=BPS_DENOM)
        FeeSplitParams(buyback_bps=BPS_DENOM, treasury_bps=0, rewards_bps=0)

        with pytest.raises(ValueError):
            FeeSplitParams(buyback_bps=0, treasury_bps=0, rewards_bps=BPS_DENOM - 1)

        with pytest.raises(ValueError):
            FeeSplitParams(buyback_bps=1, treasury_bps=1, rewards_bps=BPS_DENOM)  # sum too large


class TestFeeSplitWithDustCarryBVA:
    @pytest.mark.parametrize(
        "fee_amount,expect_ok,reason",
        [
            (-1, False, "just below min=0"),
            (0, True, "at min"),
            (1, True, "just above min"),
            (2, True, "small integer"),
            (10**12, True, "large"),
        ],
    )
    def test_fee_amount_bounds(self, fee_amount: int, expect_ok: bool, reason: str) -> None:
        params = FeeSplitParams(buyback_bps=3333, treasury_bps=3333, rewards_bps=3334)
        if expect_ok:
            res, st = split_fee_with_dust_carry(fee_amount, params)
            assert st.dust == res.dust_carried
            assert res.buyback_amount + res.treasury_amount + res.rewards_amount + res.dust_carried == fee_amount
        else:
            with pytest.raises(ValueError):
                split_fee_with_dust_carry(fee_amount, params)

    def test_dust_is_bounded_by_number_of_parts(self) -> None:
        # With 3-way splitting and exact bps sum, dust is always < 3.
        params = FeeSplitParams(buyback_bps=3333, treasury_bps=3333, rewards_bps=3334)
        st = FeeAccumulatorState(dust=0)
        for fee in [0, 1, 2, 3, 7, 10, 12345]:
            res, st = split_fee_with_dust_carry(fee, params, state=st)
            assert 0 <= res.dust_carried < 3

    def test_dust_carry_conserves_over_multiple_splits(self) -> None:
        params = FeeSplitParams(buyback_bps=1111, treasury_bps=2222, rewards_bps=6667)
        st = FeeAccumulatorState(dust=0)

        total_fee = 0
        total_distributed = 0
        for fee in [1, 1, 1, 1, 1, 7, 9, 13, 2, 0, 5]:
            total_fee += fee
            res, st = split_fee_with_dust_carry(fee, params, state=st)
            total_distributed += res.buyback_amount + res.treasury_amount + res.rewards_amount

        # Whatever hasn't been distributed must be sitting in dust.
        assert total_distributed + st.dust == total_fee

