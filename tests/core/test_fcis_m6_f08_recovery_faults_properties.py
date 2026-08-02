"""Deterministic property checks for the F08 corruption lock."""

from __future__ import annotations

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_f08_recovery_faults_check import (
    build_fault_payloads,
    build_post_payload,
    build_pre_payload,
)
from src.core.fcis_m6_f08_recovery_faults import (
    F08RecoveryObservationV1,
    F08RecoveryOutcomeV1,
    observe_f08_recovery,
)


@settings(max_examples=24, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(fault_name=st.sampled_from(tuple(build_fault_payloads())))  # type: ignore[untyped-decorator]
def test_generated_faults_all_remain_rejected_and_locked(fault_name: str) -> None:
    pre = build_pre_payload()
    post = build_post_payload()
    result = observe_f08_recovery(pre, post, build_fault_payloads()[fault_name])

    assert type(result) is F08RecoveryObservationV1
    assert result.outcome is F08RecoveryOutcomeV1.REJECTED_LOCKED
    assert result.observed_layout_root is None
    assert result.rejection_code is not None
    assert result.requires_fresh_authorization
    assert not result.can_accept_value_movement
