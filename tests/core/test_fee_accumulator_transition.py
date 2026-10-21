from __future__ import annotations

from src.core.fee_accumulator_transition import (
    FeeAccumulatorTransitionCodeV1,
    FeeAccumulatorTransitionOkV1,
    FeeAccumulatorTransitionRejectV1,
    split_fee_with_committed_dust_carry_v1,
)
from src.core.fees import FeeAccumulatorState, FeeSplitParams, split_fee_with_dust_carry
from src.state.state_snapshot_values import CommittedFeeAccumulatorStateV1
from src.state.state_snapshots import snapshot_fee_accumulator


def test_exact_fee_transition_matches_legacy_over_dust_carry_sequence() -> None:
    params = FeeSplitParams(buyback_bps=3_333, treasury_bps=3_333, rewards_bps=3_334)
    legacy = FeeAccumulatorState()
    exact = snapshot_fee_accumulator(legacy)

    for fee_amount in (0, 1, 2, 9_999, 10_000, 10_001, 999_999_999):
        legacy_allocation, legacy_next = split_fee_with_dust_carry(
            fee_amount,
            params,
            legacy,
        )
        exact_result = split_fee_with_committed_dust_carry_v1(
            fee_amount=fee_amount,
            params=params,
            state=exact,
        )

        assert type(exact_result) is FeeAccumulatorTransitionOkV1
        assert exact_result.allocation == legacy_allocation
        assert exact_result.state == snapshot_fee_accumulator(legacy_next)
        assert exact.dust == legacy.dust
        legacy = legacy_next
        exact = exact_result.state


def test_exact_fee_transition_conserves_input_plus_prior_dust() -> None:
    params = FeeSplitParams(buyback_bps=1, treasury_bps=5_999, rewards_bps=4_000)
    pre = CommittedFeeAccumulatorStateV1(dust=7)

    result = split_fee_with_committed_dust_carry_v1(
        fee_amount=123_456_789,
        params=params,
        state=pre,
    )

    assert type(result) is FeeAccumulatorTransitionOkV1
    allocation = result.allocation
    assert (
        allocation.buyback_amount
        + allocation.treasury_amount
        + allocation.rewards_amount
        + result.state.dust
        == 123_456_789 + pre.dust
    )
    assert allocation.dust_carried == result.state.dust
    assert pre.dust == 7


def test_exact_fee_transition_rejects_without_candidate() -> None:
    params = FeeSplitParams(buyback_bps=3_000, treasury_bps=3_000, rewards_bps=4_000)
    pre = CommittedFeeAccumulatorStateV1(dust=0)

    for fee_amount, expected_code in (
        (True, FeeAccumulatorTransitionCodeV1.WRONG_EXACT_TYPE),
        (-1, FeeAccumulatorTransitionCodeV1.OUT_OF_RANGE),
    ):
        result = split_fee_with_committed_dust_carry_v1(
            fee_amount=fee_amount,
            params=params,
            state=pre,
        )
        assert type(result) is FeeAccumulatorTransitionRejectV1
        assert result.code is expected_code
        assert not hasattr(result, "state")
        assert not hasattr(result, "allocation")


def test_exact_fee_transition_revalidates_owned_state_and_parameters() -> None:
    pre = CommittedFeeAccumulatorStateV1(dust=3)
    params = FeeSplitParams(buyback_bps=3_000, treasury_bps=3_000, rewards_bps=4_000)
    object.__setattr__(pre, "dust", True)

    corrupt_state = split_fee_with_committed_dust_carry_v1(
        fee_amount=1,
        params=params,
        state=pre,
    )
    assert corrupt_state == FeeAccumulatorTransitionRejectV1(
        FeeAccumulatorTransitionCodeV1.INVALID_PRESTATE,
        "state.dust",
    )

    fresh_pre = CommittedFeeAccumulatorStateV1(dust=3)
    object.__setattr__(params, "buyback_bps", True)
    corrupt_params = split_fee_with_committed_dust_carry_v1(
        fee_amount=1,
        params=params,
        state=fresh_pre,
    )
    assert corrupt_params == FeeAccumulatorTransitionRejectV1(
        FeeAccumulatorTransitionCodeV1.INVALID_PARAMETERS,
        "buyback_bps",
    )


def test_exact_fee_transition_rejects_lookalike_and_subclass_inputs() -> None:
    class ParamsLookalike:
        buyback_bps = 3_000
        treasury_bps = 3_000
        rewards_bps = 4_000

    params_subclass = type("ParamsSubclass", (FeeSplitParams,), {})
    state_subclass = type("StateSubclass", (CommittedFeeAccumulatorStateV1,), {})
    pre = CommittedFeeAccumulatorStateV1(dust=0)

    lookalike = split_fee_with_committed_dust_carry_v1(
        fee_amount=1,
        params=ParamsLookalike(),
        state=pre,
    )
    subclass_params = split_fee_with_committed_dust_carry_v1(
        fee_amount=1,
        params=params_subclass(3_000, 3_000, 4_000),
        state=pre,
    )
    subclass_state = split_fee_with_committed_dust_carry_v1(
        fee_amount=1,
        params=FeeSplitParams(3_000, 3_000, 4_000),
        state=state_subclass(0),
    )

    assert lookalike == FeeAccumulatorTransitionRejectV1(
        FeeAccumulatorTransitionCodeV1.WRONG_EXACT_TYPE,
        "params",
    )
    assert subclass_params == lookalike
    assert subclass_state == FeeAccumulatorTransitionRejectV1(
        FeeAccumulatorTransitionCodeV1.WRONG_EXACT_TYPE,
        "state",
    )
