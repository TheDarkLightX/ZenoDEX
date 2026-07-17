from __future__ import annotations

from dataclasses import FrozenInstanceError

import pytest

from src.state.confidential_requests import (
    ConfidentialRequestKey,
    ConfidentialRequestTable,
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


def test_confidential_request_table_constructor_owns_and_canonicalizes_entries() -> None:
    key = _key()
    other = ConfidentialRequestKey(
        extension_id="ext-2",
        provider_id="provider-1",
        request_id="req-2",
    )
    source = {other: True, key: True}

    table = ConfidentialRequestTable(source)
    source.clear()

    assert table.entries == ((key, True), (other, True))
    assert table.is_used(key) is True
    assert table.is_used(other) is True


def test_confidential_request_table_exposes_only_structurally_immutable_state() -> None:
    key = _key()
    table = ConfidentialRequestTable({key: True})

    assert isinstance(table.entries, tuple)
    assert isinstance(table.entries[0], tuple)
    with pytest.raises(FrozenInstanceError):
        table.entries = ()  # type: ignore[misc]
    with pytest.raises(TypeError):
        table.get_all()[key] = False  # type: ignore[index]

    assert table.is_used(key) is True


def test_confidential_request_table_consume_is_atomic_and_replay_is_no_op() -> None:
    key = _key()
    before = ConfidentialRequestTable()

    after = before.consume(key)

    assert after is not before
    assert before.get_all() == {}
    assert after.get_all() == {key: True}
    with pytest.raises(ValueError, match="request already used"):
        after.consume(key)
    assert after.get_all() == {key: True}


def test_copy_confidential_request_table_preserves_immutable_snapshot() -> None:
    key = _key()
    table = ConfidentialRequestTable({key: True})

    copied = copy_confidential_request_table(table)
    assert copied == table
    assert copied.is_used(key) is True
