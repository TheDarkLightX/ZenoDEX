from __future__ import annotations

import pytest

from src.state.intent_nonce_batch_policy_gate import (
    INTENT_NONCE_BATCH_POLICY_MIXED_PRESENCE,
    INTENT_NONCE_BATCH_POLICY_MISSING_INVALID_NONCE,
    INTENT_NONCE_BATCH_POLICY_OK_COPY,
    INTENT_NONCE_BATCH_POLICY_OK_PROCEED,
    evaluate_intent_nonce_batch_policy_gate,
    intent_nonce_batch_policy_error,
)


def test_intent_nonce_batch_policy_empty_batch_returns_copy() -> None:
    decision = evaluate_intent_nonce_batch_policy_gate(
        empty_batch=True,
        require_all_nonces=False,
        saw_nonce=False,
        saw_missing=False,
    )
    assert decision.batch_ok is True
    assert decision.return_copy is True
    assert decision.reject_code == INTENT_NONCE_BATCH_POLICY_OK_COPY
    assert intent_nonce_batch_policy_error(decision) is None


def test_intent_nonce_batch_policy_missing_required_precedes_mixed_presence() -> None:
    decision = evaluate_intent_nonce_batch_policy_gate(
        empty_batch=False,
        require_all_nonces=True,
        saw_nonce=True,
        saw_missing=True,
    )
    assert decision.batch_ok is False
    assert decision.return_copy is False
    assert decision.reject_code == INTENT_NONCE_BATCH_POLICY_MISSING_INVALID_NONCE
    assert intent_nonce_batch_policy_error(decision) == "Missing/invalid nonce"


def test_intent_nonce_batch_policy_rejects_mixed_presence_when_nonce_optional() -> None:
    decision = evaluate_intent_nonce_batch_policy_gate(
        empty_batch=False,
        require_all_nonces=False,
        saw_nonce=True,
        saw_missing=True,
    )
    assert decision.batch_ok is False
    assert decision.return_copy is False
    assert decision.reject_code == INTENT_NONCE_BATCH_POLICY_MIXED_PRESENCE
    assert intent_nonce_batch_policy_error(decision) == "nonce presence must be consistent across batch"


def test_intent_nonce_batch_policy_accepts_nonce_free_batch_as_copy() -> None:
    decision = evaluate_intent_nonce_batch_policy_gate(
        empty_batch=False,
        require_all_nonces=False,
        saw_nonce=False,
        saw_missing=True,
    )
    assert decision.batch_ok is True
    assert decision.return_copy is True
    assert decision.reject_code == INTENT_NONCE_BATCH_POLICY_OK_COPY


def test_intent_nonce_batch_policy_accepts_nonce_bearing_batch_as_proceed() -> None:
    decision = evaluate_intent_nonce_batch_policy_gate(
        empty_batch=False,
        require_all_nonces=True,
        saw_nonce=True,
        saw_missing=False,
    )
    assert decision.batch_ok is True
    assert decision.return_copy is False
    assert decision.reject_code == INTENT_NONCE_BATCH_POLICY_OK_PROCEED


@pytest.mark.parametrize("field", ["empty_batch", "require_all_nonces", "saw_nonce", "saw_missing"])
def test_intent_nonce_batch_policy_rejects_non_bool_inputs(field: str) -> None:
    kwargs = {
        "empty_batch": False,
        "require_all_nonces": False,
        "saw_nonce": False,
        "saw_missing": False,
    }
    kwargs[field] = 1
    with pytest.raises(TypeError, match=field):
        evaluate_intent_nonce_batch_policy_gate(**kwargs)
