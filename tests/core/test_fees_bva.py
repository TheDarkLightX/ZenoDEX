"""BVA + invariants for fee splitting (`src/core/fees.py`)."""

from __future__ import annotations

import pytest

from src.core.fees import (
    BPS_DENOM,
    MAX_FEE_SPLIT_DUST,
    FeeAccumulatorState,
    FeeSplitParams,
    FeeSplitResult,
    split_fee_with_dust_carry,
)


class TestFeeSplitParamsBVA:
    def test_bps_sum_must_be_exact(self) -> None:
        FeeSplitParams(buyback_bps=0, treasury_bps=0, rewards_bps=BPS_DENOM)
        FeeSplitParams(buyback_bps=BPS_DENOM, treasury_bps=0, rewards_bps=0)

        with pytest.raises(ValueError):
            FeeSplitParams(buyback_bps=0, treasury_bps=0, rewards_bps=BPS_DENOM - 1)

        with pytest.raises(ValueError):
            FeeSplitParams(buyback_bps=1, treasury_bps=1, rewards_bps=BPS_DENOM)

    def test_boolean_and_subclass_parameters_reject(self) -> None:
        with pytest.raises(TypeError, match="buyback_bps must be an int"):
            FeeSplitParams(buyback_bps=True, treasury_bps=0, rewards_bps=BPS_DENOM)

        class DerivedParams(FeeSplitParams):
            pass

        with pytest.raises(TypeError, match="exact FeeSplitParams"):
            split_fee_with_dust_carry(
                1,
                DerivedParams(
                    buyback_bps=0,
                    treasury_bps=0,
                    rewards_bps=BPS_DENOM,
                ),
            )


class TestFeeAccumulatorStateBVA:
    @pytest.mark.parametrize("dust", (0, 1, MAX_FEE_SPLIT_DUST))
    def test_inductive_dust_bound_accepts(self, dust: int) -> None:
        assert FeeAccumulatorState(dust=dust).dust == dust

    @pytest.mark.parametrize("dust", (-1, MAX_FEE_SPLIT_DUST + 1, 10**30))
    def test_malformed_carry_prestate_rejects(self, dust: int) -> None:
        with pytest.raises(ValueError, match="inductive three-lane bound"):
            FeeAccumulatorState(dust=dust)

    def test_boolean_and_subclass_state_reject(self) -> None:
        with pytest.raises(TypeError, match="dust must be an int"):
            FeeAccumulatorState(dust=True)

        class DerivedState(FeeAccumulatorState):
            pass

        params = FeeSplitParams(
            buyback_bps=3333,
            treasury_bps=3333,
            rewards_bps=3334,
        )
        with pytest.raises(TypeError, match="exact FeeAccumulatorState"):
            split_fee_with_dust_carry(1, params, state=DerivedState())

    def test_effect_constructor_cannot_claim_fabricated_dust(self) -> None:
        with pytest.raises(ValueError, match="floor-rounding bound"):
            FeeSplitResult(
                buyback_amount=0,
                treasury_amount=0,
                rewards_amount=0,
                dust_carried=MAX_FEE_SPLIT_DUST + 1,
            )


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
            result, state = split_fee_with_dust_carry(fee_amount, params)
            assert state.dust == result.dust_carried
            assert (
                result.buyback_amount
                + result.treasury_amount
                + result.rewards_amount
                + result.dust_carried
                == fee_amount
            )
        else:
            with pytest.raises(ValueError):
                split_fee_with_dust_carry(fee_amount, params)

    def test_boolean_fee_rejects(self) -> None:
        params = FeeSplitParams(buyback_bps=3333, treasury_bps=3333, rewards_bps=3334)
        with pytest.raises(ValueError, match="non-negative int"):
            split_fee_with_dust_carry(True, params)

    def test_dust_is_bounded_by_number_of_parts(self) -> None:
        params = FeeSplitParams(buyback_bps=3333, treasury_bps=3333, rewards_bps=3334)
        state = FeeAccumulatorState(dust=0)
        for fee in [0, 1, 2, 3, 7, 10, 12345, 10**30]:
            result, state = split_fee_with_dust_carry(fee, params, state=state)
            assert 0 <= result.dust_carried <= MAX_FEE_SPLIT_DUST

    def test_dust_carry_conserves_over_multiple_splits(self) -> None:
        params = FeeSplitParams(buyback_bps=1111, treasury_bps=2222, rewards_bps=6667)
        state = FeeAccumulatorState(dust=0)

        total_fee = 0
        total_distributed = 0
        for fee in [1, 1, 1, 1, 1, 7, 9, 13, 2, 0, 5]:
            total_fee += fee
            result, state = split_fee_with_dust_carry(fee, params, state=state)
            total_distributed += (
                result.buyback_amount
                + result.treasury_amount
                + result.rewards_amount
            )

        assert total_distributed + state.dust == total_fee
