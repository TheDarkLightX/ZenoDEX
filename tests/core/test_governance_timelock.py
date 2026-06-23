from __future__ import annotations

from collections.abc import Callable

import pytest

from src.core.governance_timelock import (
    REJECT_DELAY_BELOW_ABSOLUTE_FLOOR,
    REJECT_EXECUTION_TIME_BEFORE_PROPOSAL,
    REJECT_OK,
    REJECT_TIMELOCK_NOT_ELAPSED,
    GovernanceTimelockPolicy,
    TimelockProposalSnapshot,
    create_timelock_proposal_snapshot,
    evaluate_timelock_delay_update,
    evaluate_timelock_execution,
    timelock_delay_update_error,
    timelock_execution_error,
)


def test_timelock_snapshot_protects_existing_proposal_after_delay_is_lowered() -> None:
    initial_policy = GovernanceTimelockPolicy(min_delay_seconds=3_600, absolute_floor_seconds=300)
    snapshot = create_timelock_proposal_snapshot(
        proposal_id="upgrade-risk-controls",
        proposed_at_seconds=1_000,
        policy=initial_policy,
    )

    lowered_delay = evaluate_timelock_delay_update(
        new_min_delay_seconds=300,
        absolute_floor_seconds=300,
    )
    early_execution = evaluate_timelock_execution(
        snapshot=snapshot,
        current_time_seconds=1_300,
    )
    mature_execution = evaluate_timelock_execution(
        snapshot=snapshot,
        current_time_seconds=4_600,
    )

    assert lowered_delay.admission_ok is True
    assert early_execution.admission_ok is False
    assert early_execution.reject_code == REJECT_TIMELOCK_NOT_ELAPSED
    assert early_execution.snapshotted_min_delay_seconds == 3_600
    assert mature_execution.admission_ok is True
    assert mature_execution.reject_code == REJECT_OK
    assert timelock_execution_error(mature_execution) is None


def test_timelock_delay_update_rejects_below_absolute_floor() -> None:
    outcome = evaluate_timelock_delay_update(
        new_min_delay_seconds=0,
        absolute_floor_seconds=300,
    )

    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_DELAY_BELOW_ABSOLUTE_FLOOR
    assert timelock_delay_update_error(outcome) == "new timelock delay is below absolute floor"


def test_timelock_execution_rejects_time_before_proposal() -> None:
    snapshot = TimelockProposalSnapshot(
        proposal_id="param-change",
        proposed_at_seconds=1_000,
        snapshotted_min_delay_seconds=300,
        absolute_floor_seconds=300,
    )

    outcome = evaluate_timelock_execution(snapshot=snapshot, current_time_seconds=999)

    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_EXECUTION_TIME_BEFORE_PROPOSAL
    assert outcome.timestamp_order_ok is False


def test_timelock_execution_bounded_snapshot_surface() -> None:
    proposed_at = 100
    for floor in range(1, 5):
        for delay in range(floor, floor + 5):
            snapshot = TimelockProposalSnapshot(
                proposal_id=f"p-{floor}-{delay}",
                proposed_at_seconds=proposed_at,
                snapshotted_min_delay_seconds=delay,
                absolute_floor_seconds=floor,
            )

            before = evaluate_timelock_execution(
                snapshot=snapshot,
                current_time_seconds=proposed_at + delay - 1,
            )
            at_boundary = evaluate_timelock_execution(
                snapshot=snapshot,
                current_time_seconds=proposed_at + delay,
            )

            assert before.admission_ok is False
            assert before.reject_code == REJECT_TIMELOCK_NOT_ELAPSED
            assert at_boundary.admission_ok is True
            assert at_boundary.reject_code == REJECT_OK


def test_timelock_policy_rejects_min_delay_below_floor() -> None:
    with pytest.raises(ValueError, match="min_delay_seconds must be >= absolute_floor_seconds"):
        GovernanceTimelockPolicy(min_delay_seconds=299, absolute_floor_seconds=300)


@pytest.mark.parametrize(
    ("factory", "error_type", "match"),
    [
        (
            lambda: GovernanceTimelockPolicy(min_delay_seconds=True, absolute_floor_seconds=300),
            TypeError,
            "min_delay_seconds must be an int",
        ),
        (
            lambda: GovernanceTimelockPolicy(min_delay_seconds=300, absolute_floor_seconds=0),
            ValueError,
            "absolute_floor_seconds must be >= 1",
        ),
        (
            lambda: TimelockProposalSnapshot(
                proposal_id=" ",
                proposed_at_seconds=1,
                snapshotted_min_delay_seconds=300,
                absolute_floor_seconds=300,
            ),
            ValueError,
            "proposal_id must be non-empty",
        ),
        (
            lambda: evaluate_timelock_execution(
                snapshot=TimelockProposalSnapshot(
                    proposal_id="p",
                    proposed_at_seconds=1,
                    snapshotted_min_delay_seconds=300,
                    absolute_floor_seconds=300,
                ),
                current_time_seconds=True,
            ),
            TypeError,
            "current_time_seconds must be an int",
        ),
    ],
)
def test_timelock_contract_rejects_invalid_domains(
    factory: Callable[[], object],
    error_type: type[Exception],
    match: str,
) -> None:
    with pytest.raises(error_type, match=match):
        factory()
