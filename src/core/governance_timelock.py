from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from .domain_limits import require_int_range

REJECT_OK = "Ok"
REJECT_DELAY_BELOW_ABSOLUTE_FLOOR = "DelayBelowAbsoluteFloor"
REJECT_EXECUTION_TIME_BEFORE_PROPOSAL = "ExecutionTimeBeforeProposal"
REJECT_TIMELOCK_NOT_ELAPSED = "TimelockNotElapsed"


@dataclass(frozen=True)
class GovernanceTimelockPolicy:
    min_delay_seconds: int
    absolute_floor_seconds: int

    def __post_init__(self) -> None:
        min_delay = require_int_range("min_delay_seconds", self.min_delay_seconds, minimum=1)
        floor = require_int_range("absolute_floor_seconds", self.absolute_floor_seconds, minimum=1)
        if min_delay < floor:
            raise ValueError("min_delay_seconds must be >= absolute_floor_seconds")


@dataclass(frozen=True)
class TimelockProposalSnapshot:
    proposal_id: str
    proposed_at_seconds: int
    snapshotted_min_delay_seconds: int
    absolute_floor_seconds: int

    def __post_init__(self) -> None:
        proposal_id = _require_nonempty_text(self.proposal_id, name="proposal_id")
        object.__setattr__(self, "proposal_id", proposal_id)
        require_int_range("proposed_at_seconds", self.proposed_at_seconds, minimum=0)
        snapshotted_delay = require_int_range(
            "snapshotted_min_delay_seconds",
            self.snapshotted_min_delay_seconds,
            minimum=1,
        )
        floor = require_int_range("absolute_floor_seconds", self.absolute_floor_seconds, minimum=1)
        if snapshotted_delay < floor:
            raise ValueError("snapshotted_min_delay_seconds must be >= absolute_floor_seconds")


@dataclass(frozen=True)
class TimelockExecutionOutcome:
    proposal_id: str
    proposed_at_seconds: int
    current_time_seconds: int
    snapshotted_min_delay_seconds: int
    absolute_floor_seconds: int
    elapsed_seconds: int
    absolute_floor_ok: bool
    timestamp_order_ok: bool
    delay_elapsed: bool
    admission_ok: bool
    reject_code: str
    checks: Mapping[str, bool | int | str]


@dataclass(frozen=True)
class TimelockDelayUpdateOutcome:
    new_min_delay_seconds: int
    absolute_floor_seconds: int
    absolute_floor_ok: bool
    admission_ok: bool
    reject_code: str
    checks: Mapping[str, bool | int]


def create_timelock_proposal_snapshot(
    *,
    proposal_id: Any,
    proposed_at_seconds: Any,
    policy: GovernanceTimelockPolicy,
) -> TimelockProposalSnapshot:
    if not isinstance(policy, GovernanceTimelockPolicy):
        raise TypeError("policy must be a GovernanceTimelockPolicy")
    return TimelockProposalSnapshot(
        proposal_id=_require_nonempty_text(proposal_id, name="proposal_id"),
        proposed_at_seconds=require_int_range("proposed_at_seconds", proposed_at_seconds, minimum=0),
        snapshotted_min_delay_seconds=int(policy.min_delay_seconds),
        absolute_floor_seconds=int(policy.absolute_floor_seconds),
    )


def evaluate_timelock_execution(
    *,
    snapshot: TimelockProposalSnapshot,
    current_time_seconds: Any,
) -> TimelockExecutionOutcome:
    if not isinstance(snapshot, TimelockProposalSnapshot):
        raise TypeError("snapshot must be a TimelockProposalSnapshot")
    current_time = require_int_range("current_time_seconds", current_time_seconds, minimum=0)

    timestamp_order_ok = bool(current_time >= snapshot.proposed_at_seconds)
    elapsed = current_time - snapshot.proposed_at_seconds if timestamp_order_ok else 0
    absolute_floor_ok = bool(snapshot.snapshotted_min_delay_seconds >= snapshot.absolute_floor_seconds)
    delay_elapsed = bool(timestamp_order_ok and elapsed >= snapshot.snapshotted_min_delay_seconds)

    if not absolute_floor_ok:
        reject_code = REJECT_DELAY_BELOW_ABSOLUTE_FLOOR
    elif not timestamp_order_ok:
        reject_code = REJECT_EXECUTION_TIME_BEFORE_PROPOSAL
    elif not delay_elapsed:
        reject_code = REJECT_TIMELOCK_NOT_ELAPSED
    else:
        reject_code = REJECT_OK

    return TimelockExecutionOutcome(
        proposal_id=snapshot.proposal_id,
        proposed_at_seconds=int(snapshot.proposed_at_seconds),
        current_time_seconds=current_time,
        snapshotted_min_delay_seconds=int(snapshot.snapshotted_min_delay_seconds),
        absolute_floor_seconds=int(snapshot.absolute_floor_seconds),
        elapsed_seconds=elapsed,
        absolute_floor_ok=absolute_floor_ok,
        timestamp_order_ok=timestamp_order_ok,
        delay_elapsed=delay_elapsed,
        admission_ok=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        checks={
            "proposal_id": snapshot.proposal_id,
            "proposed_at_seconds": int(snapshot.proposed_at_seconds),
            "current_time_seconds": current_time,
            "snapshotted_min_delay_seconds": int(snapshot.snapshotted_min_delay_seconds),
            "absolute_floor_seconds": int(snapshot.absolute_floor_seconds),
            "elapsed_seconds": elapsed,
            "absolute_floor_ok": absolute_floor_ok,
            "timestamp_order_ok": timestamp_order_ok,
            "delay_elapsed": delay_elapsed,
        },
    )


def evaluate_timelock_delay_update(
    *,
    new_min_delay_seconds: Any,
    absolute_floor_seconds: Any,
) -> TimelockDelayUpdateOutcome:
    new_delay = require_int_range("new_min_delay_seconds", new_min_delay_seconds, minimum=0)
    floor = require_int_range("absolute_floor_seconds", absolute_floor_seconds, minimum=1)
    absolute_floor_ok = bool(new_delay >= floor)
    reject_code = REJECT_OK if absolute_floor_ok else REJECT_DELAY_BELOW_ABSOLUTE_FLOOR

    return TimelockDelayUpdateOutcome(
        new_min_delay_seconds=new_delay,
        absolute_floor_seconds=floor,
        absolute_floor_ok=absolute_floor_ok,
        admission_ok=absolute_floor_ok,
        reject_code=reject_code,
        checks={
            "new_min_delay_seconds": new_delay,
            "absolute_floor_seconds": floor,
            "absolute_floor_ok": absolute_floor_ok,
        },
    )


def timelock_execution_error(outcome: TimelockExecutionOutcome) -> str | None:
    if outcome.reject_code == REJECT_DELAY_BELOW_ABSOLUTE_FLOOR:
        return "timelock proposal delay is below absolute floor"
    if outcome.reject_code == REJECT_EXECUTION_TIME_BEFORE_PROPOSAL:
        return "timelock execution time precedes proposal time"
    if outcome.reject_code == REJECT_TIMELOCK_NOT_ELAPSED:
        return "timelock has not elapsed under proposal snapshot"
    return None


def timelock_delay_update_error(outcome: TimelockDelayUpdateOutcome) -> str | None:
    if outcome.reject_code == REJECT_DELAY_BELOW_ABSOLUTE_FLOOR:
        return "new timelock delay is below absolute floor"
    return None


def _require_nonempty_text(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


__all__ = [
    "REJECT_DELAY_BELOW_ABSOLUTE_FLOOR",
    "REJECT_EXECUTION_TIME_BEFORE_PROPOSAL",
    "REJECT_OK",
    "REJECT_TIMELOCK_NOT_ELAPSED",
    "GovernanceTimelockPolicy",
    "TimelockDelayUpdateOutcome",
    "TimelockExecutionOutcome",
    "TimelockProposalSnapshot",
    "create_timelock_proposal_snapshot",
    "evaluate_timelock_delay_update",
    "evaluate_timelock_execution",
    "timelock_delay_update_error",
    "timelock_execution_error",
]
