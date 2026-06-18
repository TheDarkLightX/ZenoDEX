from __future__ import annotations

import pytest

from src.core.volatility_tier import TierAction, TierActionParams, TierStepResult, step
from src.state.volatility import TierState, tier_effects


def test_tier_step_result_accept_flag_must_be_bool() -> None:
    with pytest.raises(ValueError, match="accepted must be bool"):
        TierStepResult(
            accepted=1,  # type: ignore[arg-type]
            state=TierState(),
            effects=tier_effects(0),
        )


def test_tier_step_result_accept_requires_state_and_effects() -> None:
    with pytest.raises(ValueError, match="state and effects"):
        TierStepResult(accepted=True, state=TierState())

    with pytest.raises(ValueError, match="state and effects"):
        TierStepResult(accepted=True, effects=tier_effects(0))


def test_tier_step_result_accept_rejects_rejection_reason() -> None:
    with pytest.raises(ValueError, match="cannot include rejection"):
        TierStepResult(
            accepted=True,
            state=TierState(),
            effects=tier_effects(0),
            rejection="guard",
        )


def test_tier_step_result_reject_requires_reason_and_no_post_artifacts() -> None:
    with pytest.raises(ValueError, match="rejection reason"):
        TierStepResult(accepted=False)

    with pytest.raises(ValueError, match="state or effects"):
        TierStepResult(accepted=False, state=TierState(), rejection="guard")

    with pytest.raises(ValueError, match="state or effects"):
        TierStepResult(accepted=False, effects=tier_effects(0), rejection="guard")


def test_tier_step_result_live_step_shapes_remain_valid() -> None:
    accepted = step(
        TierState(),
        TierActionParams(action=TierAction.OBSERVE, epoch=1, volatility_bps=1000, data_ok=True),
    )
    rejected = step(
        TierState(),
        TierActionParams(action=TierAction.OBSERVE, epoch=-1, volatility_bps=1000, data_ok=True),
    )

    assert accepted.accepted is True
    assert accepted.state is not None
    assert accepted.effects is not None
    assert accepted.rejection is None
    assert rejected.accepted is False
    assert rejected.state is None
    assert rejected.effects is None
    assert rejected.rejection == "invalid_param:epoch"
