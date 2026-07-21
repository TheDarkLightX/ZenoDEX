from __future__ import annotations

from src.core.consensus_time import (
    ClockAuthorityProfileV1,
    ClockPolicyScheduleV1,
    ClockPolicyV1,
    VerifiedExecutionClockV1,
    clock_policy_schedule_hash_v1,
    verify_execution_clock_v1,
)


def execution_clock_v1(
    *,
    chain_id: str,
    height: int,
    blocks_per_epoch: int = 1,
    epoch_base: int = 0,
) -> VerifiedExecutionClockV1:
    """Build a governed height-only clock for deterministic integration tests."""

    policy = ClockPolicyV1(
        clock_policy_id="HEIGHT_ONLY_V1",
        clock_policy_version=1,
        chain_id=chain_id,
        deployment_profile=(ClockAuthorityProfileV1.ZENO_LEDGER_TAU_CHECKPOINTED_V1),
        consensus_domain_id=f"{chain_id}:zeno-ledger",
        activation_height=0,
        epoch_base=epoch_base,
        blocks_per_epoch=blocks_per_epoch,
    )
    schedule = ClockPolicyScheduleV1(policies=(policy,))
    return verify_execution_clock_v1(
        chain_id=chain_id,
        height=height,
        schedule=schedule,
        expected_schedule_hash=clock_policy_schedule_hash_v1(schedule),
    )
