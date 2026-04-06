from __future__ import annotations

import pytest

from src.state.intent_nonce_sender_resolution_gate import (
    INTENT_NONCE_SENDER_RESOLUTION_DUPLICATE,
    INTENT_NONCE_SENDER_RESOLUTION_OK,
    INTENT_NONCE_SENDER_RESOLUTION_SEQUENCE_INVALID,
    evaluate_intent_nonce_sender_resolution_gate,
    intent_nonce_sender_resolution_error,
)


def test_intent_nonce_sender_resolution_accepts_contiguous_sender_outcome() -> None:
    resolution = evaluate_intent_nonce_sender_resolution_gate(
        strict_increasing=True,
        contiguous_from_last=True,
        last_used_nonce=4,
        next_last_nonce=7,
    )
    assert resolution.sender_ok is True
    assert resolution.resolved_last_nonce == 7
    assert resolution.reject_code == INTENT_NONCE_SENDER_RESOLUTION_OK
    assert intent_nonce_sender_resolution_error(resolution) is None


def test_intent_nonce_sender_resolution_duplicate_precedes_gap() -> None:
    resolution = evaluate_intent_nonce_sender_resolution_gate(
        strict_increasing=False,
        contiguous_from_last=False,
        last_used_nonce=4,
        next_last_nonce=4,
    )
    assert resolution.sender_ok is False
    assert resolution.resolved_last_nonce == 4
    assert resolution.reject_code == INTENT_NONCE_SENDER_RESOLUTION_DUPLICATE
    assert intent_nonce_sender_resolution_error(resolution) == "duplicate nonce in batch"


def test_intent_nonce_sender_resolution_rejects_gap() -> None:
    resolution = evaluate_intent_nonce_sender_resolution_gate(
        strict_increasing=True,
        contiguous_from_last=False,
        last_used_nonce=4,
        next_last_nonce=4,
    )
    assert resolution.sender_ok is False
    assert resolution.resolved_last_nonce == 4
    assert resolution.reject_code == INTENT_NONCE_SENDER_RESOLUTION_SEQUENCE_INVALID
    assert intent_nonce_sender_resolution_error(resolution) == "nonce sequence invalid"


def test_intent_nonce_sender_resolution_rejects_backwards_next_last_nonce() -> None:
    with pytest.raises(ValueError, match="next_last_nonce must not move backwards"):
        evaluate_intent_nonce_sender_resolution_gate(
            strict_increasing=True,
            contiguous_from_last=True,
            last_used_nonce=7,
            next_last_nonce=6,
        )


@pytest.mark.parametrize(
    ("kwargs", "exc_type", "match"),
    [
        ({"strict_increasing": 1, "contiguous_from_last": True, "last_used_nonce": 0, "next_last_nonce": 0}, TypeError, "strict_increasing"),
        ({"strict_increasing": True, "contiguous_from_last": 1, "last_used_nonce": 0, "next_last_nonce": 0}, TypeError, "contiguous_from_last"),
        ({"strict_increasing": True, "contiguous_from_last": True, "last_used_nonce": True, "next_last_nonce": 0}, TypeError, "last_used_nonce"),
        ({"strict_increasing": True, "contiguous_from_last": True, "last_used_nonce": 0, "next_last_nonce": True}, TypeError, "next_last_nonce"),
    ],
)
def test_intent_nonce_sender_resolution_rejects_noncanonical_inputs(
    kwargs: dict[str, object],
    exc_type: type[Exception],
    match: str,
) -> None:
    with pytest.raises(exc_type, match=match):
        evaluate_intent_nonce_sender_resolution_gate(**kwargs)
