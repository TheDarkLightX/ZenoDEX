from __future__ import annotations

import pytest

from src.core.confidential_extension_live_admission import (
    evaluate_confidential_extension_live_admission_gate,
)


def test_confidential_extension_live_admission_gate_accepts_happy_path() -> None:
    outcome = evaluate_confidential_extension_live_admission_gate(
        do_execute=1,
        receipt_verified=1,
        policy_digest_match=1,
        request_used_before=0,
    )

    assert outcome.do_execute_ok is True
    assert outcome.receipt_verified_ok is True
    assert outcome.policy_digest_match_ok is True
    assert outcome.request_used_before is False
    assert outcome.request_unused_ok is True
    assert outcome.request_used_after is True
    assert outcome.admission_ok is True


def test_confidential_extension_live_admission_gate_rejects_replay() -> None:
    outcome = evaluate_confidential_extension_live_admission_gate(
        do_execute=1,
        receipt_verified=1,
        policy_digest_match=1,
        request_used_before=1,
    )

    assert outcome.request_used_before is True
    assert outcome.request_unused_ok is False
    assert outcome.request_used_after is True
    assert outcome.admission_ok is False


def test_confidential_extension_live_admission_gate_rejects_missing_execution() -> None:
    outcome = evaluate_confidential_extension_live_admission_gate(
        do_execute=0,
        receipt_verified=1,
        policy_digest_match=1,
        request_used_before=0,
    )

    assert outcome.do_execute_ok is False
    assert outcome.request_unused_ok is True
    assert outcome.request_used_after is False
    assert outcome.admission_ok is False


def test_confidential_extension_live_admission_gate_rejects_noncanonical_flag() -> None:
    with pytest.raises(ValueError, match="receipt_verified must be 0 or 1"):
        evaluate_confidential_extension_live_admission_gate(
            do_execute=1,
            receipt_verified=2,
            policy_digest_match=1,
            request_used_before=0,
        )
