"""Focused prior-state acknowledgment monotonicity tests."""

from __future__ import annotations

from experiments.fcis_m6_f04_ack_progress_check import (
    build_acked_payload,
    build_history_changed_payload,
    build_mutated_ack_payload,
    build_pending_payload,
)
from src.core.fcis_m6_f04_ack_progress import (
    F04AckProgressCodeV1,
    F04AckProgressRejectV1,
    F04AckProgressStatusV1,
    F04AckProgressSuccessV1,
    check_f04_ack_progress,
)


def test_pending_ack_state_is_explicit_and_ack_addition_is_monotone() -> None:
    pending = build_pending_payload()
    acked = build_acked_payload()

    unchanged = check_f04_ack_progress(pending, pending)
    completed = check_f04_ack_progress(pending, acked)

    assert type(unchanged) is F04AckProgressSuccessV1
    assert unchanged.status is F04AckProgressStatusV1.PENDING
    assert len(unchanged.pending_effect_ids) == 1
    assert type(completed) is F04AckProgressSuccessV1
    assert completed.status is F04AckProgressStatusV1.ACKED
    assert len(completed.added_ack_effect_ids) == 1


def test_prior_ack_deletion_and_mutation_reject() -> None:
    acked = build_acked_payload()
    pending = build_pending_payload()

    removed = check_f04_ack_progress(acked, pending)
    mutated = check_f04_ack_progress(acked, build_mutated_ack_payload())

    assert type(removed) is F04AckProgressRejectV1
    assert removed.code is F04AckProgressCodeV1.ACK_REMOVED
    assert type(mutated) is F04AckProgressRejectV1
    assert mutated.code is F04AckProgressCodeV1.ACK_MUTATED


def test_non_ack_history_change_and_wrong_type_reject() -> None:
    acked = build_acked_payload()
    changed = check_f04_ack_progress(acked, build_history_changed_payload())
    wrong = check_f04_ack_progress(object(), acked)

    assert type(changed) is F04AckProgressRejectV1
    assert changed.code is F04AckProgressCodeV1.HISTORY_CHANGED
    assert type(wrong) is F04AckProgressRejectV1
    assert wrong.code is F04AckProgressCodeV1.WRONG_EXACT_TYPE
