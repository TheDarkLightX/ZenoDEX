from __future__ import annotations

import pytest

from src.state.confidential_requests import (
    ConfidentialRequestKey,
    ConfidentialRequestTable,
    ConfidentialRequestUseTransition,
    copy_confidential_request_table,
    evaluate_confidential_request_use_transition,
)


def _key() -> ConfidentialRequestKey:
    return ConfidentialRequestKey(
        extension_id=" ext-1 ",
        provider_id=" provider-1 ",
        request_id=" req-1 ",
    )


def test_confidential_request_key_normalizes_text_fields() -> None:
    key = _key()
    assert key.extension_id == "ext-1"
    assert key.provider_id == "provider-1"
    assert key.request_id == "req-1"


def test_confidential_request_key_rejects_blank_text() -> None:
    with pytest.raises(ValueError):
        ConfidentialRequestKey(extension_id=" ", provider_id="provider-1", request_id="req-1")


def test_confidential_request_use_transition_fresh_check_only() -> None:
    outcome = evaluate_confidential_request_use_transition(
        request_used_before=False,
        consume_request=False,
    )
    assert outcome.request_unused_ok is True
    assert outcome.transition_ok is True
    assert outcome.consume_applied is False
    assert outcome.request_used_after is False


def test_confidential_request_use_transition_fresh_consume() -> None:
    outcome = evaluate_confidential_request_use_transition(
        request_used_before=False,
        consume_request=True,
    )
    assert outcome.request_unused_ok is True
    assert outcome.transition_ok is True
    assert outcome.consume_applied is True
    assert outcome.request_used_after is True


def test_confidential_request_use_transition_replay_consume_fails_closed() -> None:
    outcome = evaluate_confidential_request_use_transition(
        request_used_before=True,
        consume_request=True,
    )
    assert outcome.request_unused_ok is False
    assert outcome.transition_ok is False
    assert outcome.consume_applied is False
    assert outcome.request_used_after is True


def test_confidential_request_use_transition_rejects_noncanonical_flag() -> None:
    with pytest.raises(ValueError):
        evaluate_confidential_request_use_transition(
            request_used_before=2,
            consume_request=True,
        )


def test_confidential_request_use_transition_witness_rejects_non_bool_fields() -> None:
    # REVIEW [B -> A-]: the public evaluator canonicalizes flags, but direct
    # witness construction is also part of the evidence surface. Truthy strings
    # or integers must not become accepted transition facts.
    with pytest.raises(TypeError):
        ConfidentialRequestUseTransition(
            request_used_before=1,  # type: ignore[arg-type]
            consume_request=True,
            request_unused_ok=True,
            transition_ok=True,
            consume_applied=True,
            request_used_after=True,
        )

    with pytest.raises(TypeError):
        ConfidentialRequestUseTransition(
            request_used_before=False,
            consume_request="yes",  # type: ignore[arg-type]
            request_unused_ok=True,
            transition_ok=True,
            consume_applied=False,
            request_used_after=False,
        )


def test_copy_confidential_request_table_preserves_used_entries_without_aliasing() -> None:
    key = _key()
    table = ConfidentialRequestTable()
    table.mark_used(key)

    copied = copy_confidential_request_table(table)
    assert copied.is_used(key) is True

    other = ConfidentialRequestKey(
        extension_id="ext-2",
        provider_id="provider-1",
        request_id="req-2",
    )
    copied.mark_used(other)
    assert copied.is_used(other) is True
    assert table.is_used(other) is False


def test_confidential_request_table_rejects_corrupted_used_markers() -> None:
    # REVIEW [B -> A-]: a copied table previously used bool(value), which turned
    # corrupted markers like "yes" into durable used-state. The store now grades
    # as A- because direct internal/deserializer corruption fails closed.
    key = _key()
    table = ConfidentialRequestTable()
    table._used[key] = "yes"  # type: ignore[assignment]

    with pytest.raises(TypeError):
        table.is_used(key)

    with pytest.raises(TypeError):
        table.get_all()

    with pytest.raises(TypeError):
        copy_confidential_request_table(table)
