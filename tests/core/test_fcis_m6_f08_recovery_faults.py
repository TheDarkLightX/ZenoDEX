"""Focused F08 PRE/POST and corruption-recovery tests."""

from __future__ import annotations

from experiments.fcis_m6_f08_recovery_faults_check import (
    build_fault_payloads,
    build_post_payload,
    build_pre_payload,
    build_third_payload,
)
from src.core.fcis_m6_f04_fixed_point import F04FixedPointCodeV1
from src.core.fcis_m6_f08_recovery_faults import (
    F08RecoveryObservationV1,
    F08RecoveryOutcomeV1,
    F08RecoverySetupRejectV1,
    observe_f08_recovery,
)


def test_recovery_exposes_exact_pre_or_post_and_keeps_latch_closed() -> None:
    pre = build_pre_payload()
    post = build_post_payload()

    pre_result = observe_f08_recovery(pre, post, pre)
    post_result = observe_f08_recovery(pre, post, post)

    assert type(pre_result) is F08RecoveryObservationV1
    assert type(post_result) is F08RecoveryObservationV1
    assert pre_result.outcome is F08RecoveryOutcomeV1.PRE
    assert post_result.outcome is F08RecoveryOutcomeV1.POST
    assert pre_result.requires_fresh_authorization
    assert post_result.requires_fresh_authorization
    assert not pre_result.can_accept_value_movement
    assert not post_result.can_accept_value_movement
    assert pre_result.observed_layout_root != post_result.observed_layout_root


def test_every_table_and_byte_fault_returns_rejection_lock() -> None:
    pre = build_pre_payload()
    post = build_post_payload()

    faults = build_fault_payloads()
    assert len(faults) >= 30
    for payload in faults.values():
        result = observe_f08_recovery(pre, post, payload)
        assert type(result) is F08RecoveryObservationV1
        assert result.outcome is F08RecoveryOutcomeV1.REJECTED_LOCKED
        assert result.rejection_code is not None
        assert result.observed_layout_root is None
        assert result.requires_fresh_authorization
        assert not result.can_accept_value_movement


def test_valid_third_layout_and_wrong_types_never_authorize() -> None:
    pre = build_pre_payload()
    post = build_post_payload()
    third = build_third_payload()

    third_result = observe_f08_recovery(pre, post, third)
    assert type(third_result) is F08RecoveryObservationV1
    assert third_result.outcome is F08RecoveryOutcomeV1.REJECTED_LOCKED
    assert third_result.rejection_code is F04FixedPointCodeV1.FIXED_POINT_MISMATCH

    wrong_observed = observe_f08_recovery(pre, post, object())
    assert type(wrong_observed) is F08RecoveryObservationV1
    assert wrong_observed.rejection_code is F04FixedPointCodeV1.WRONG_EXACT_TYPE

    wrong_pre = observe_f08_recovery(object(), post, pre)
    assert type(wrong_pre) is F08RecoverySetupRejectV1
