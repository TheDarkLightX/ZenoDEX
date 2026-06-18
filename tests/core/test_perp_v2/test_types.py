"""Constructor contracts for src/core/perp_v2/types.py."""

from __future__ import annotations

import pytest

from src.core.perp_v2.types import Effect, EpochPhase, Event, PerpState, StepResult


def test_step_result_accept_flag_must_be_bool() -> None:
    with pytest.raises(ValueError, match="accepted must be bool"):
        StepResult(accepted=1, state=PerpState(), effect=Effect(event=Event.EPOCH_ADVANCED))  # type: ignore[arg-type]


def test_step_result_accept_requires_state_and_effect() -> None:
    effect = Effect(event=Event.EPOCH_ADVANCED)

    with pytest.raises(ValueError, match="state and effect"):
        StepResult(accepted=True, effect=effect)

    with pytest.raises(ValueError, match="state and effect"):
        StepResult(accepted=True, state=PerpState(epoch_phase=EpochPhase.OPEN))


def test_step_result_accept_rejects_rejection_reason() -> None:
    with pytest.raises(ValueError, match="cannot include rejection"):
        StepResult(
            accepted=True,
            state=PerpState(),
            effect=Effect(event=Event.EPOCH_ADVANCED),
            rejection="guard",
        )


def test_step_result_reject_requires_reason_and_no_post_artifacts() -> None:
    with pytest.raises(ValueError, match="rejection reason"):
        StepResult(accepted=False)

    with pytest.raises(ValueError, match="state or effect"):
        StepResult(accepted=False, state=PerpState(), rejection="guard")

    with pytest.raises(ValueError, match="state or effect"):
        StepResult(
            accepted=False,
            effect=Effect(event=Event.EPOCH_ADVANCED),
            rejection="guard",
        )


def test_step_result_valid_shapes() -> None:
    post_state = PerpState(now_epoch=1)
    effect = Effect(event=Event.EPOCH_ADVANCED)

    assert StepResult(accepted=True, state=post_state, effect=effect).state == post_state
    assert StepResult(accepted=False, rejection="guard").rejection == "guard"
