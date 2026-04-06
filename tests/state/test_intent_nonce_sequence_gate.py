from __future__ import annotations

import pytest

from src.state.intent_nonce_sequence_gate import (
    INTENT_NONCE_SEQUENCE_KERNEL_MAX,
    evaluate_intent_nonce_sequence,
    evaluate_sorted_intent_nonce_sequence_gate,
)


def _sorted_kwargs(*, last_used_nonce: int, nonce_values: tuple[int, ...]) -> dict[str, int]:
    padded = list(nonce_values) + [1] * (INTENT_NONCE_SEQUENCE_KERNEL_MAX - len(nonce_values))
    return {
        "last_used_nonce": last_used_nonce,
        "nonce_count": len(nonce_values),
        "nonce_0": padded[0],
        "nonce_1": padded[1],
        "nonce_2": padded[2],
        "nonce_3": padded[3],
        "nonce_4": padded[4],
        "nonce_5": padded[5],
        "nonce_6": padded[6],
        "nonce_7": padded[7],
    }


def test_sorted_gate_accepts_empty_prefix_and_leaves_last_nonce() -> None:
    outcome = evaluate_sorted_intent_nonce_sequence_gate(**_sorted_kwargs(last_used_nonce=9, nonce_values=()))
    assert outcome.strict_increasing is True
    assert outcome.contiguous_from_last is True
    assert outcome.sequence_ok is True
    assert outcome.next_last_nonce == 9


def test_sorted_gate_accepts_contiguous_prefix() -> None:
    outcome = evaluate_sorted_intent_nonce_sequence_gate(
        **_sorted_kwargs(last_used_nonce=4, nonce_values=(5, 6, 7))
    )
    assert outcome.strict_increasing is True
    assert outcome.contiguous_from_last is True
    assert outcome.sequence_ok is True
    assert outcome.next_last_nonce == 7


def test_sorted_gate_rejects_duplicate_prefix() -> None:
    outcome = evaluate_sorted_intent_nonce_sequence_gate(
        **_sorted_kwargs(last_used_nonce=4, nonce_values=(5, 5, 6))
    )
    assert outcome.strict_increasing is False
    assert outcome.contiguous_from_last is False
    assert outcome.sequence_ok is False
    assert outcome.next_last_nonce == 4


def test_sorted_gate_rejects_gap_prefix() -> None:
    outcome = evaluate_sorted_intent_nonce_sequence_gate(
        **_sorted_kwargs(last_used_nonce=4, nonce_values=(5, 7))
    )
    assert outcome.strict_increasing is True
    assert outcome.contiguous_from_last is False
    assert outcome.sequence_ok is False
    assert outcome.next_last_nonce == 4


def test_sorted_gate_rejects_nonce_count_above_kernel_bound() -> None:
    with pytest.raises(ValueError, match="nonce_count out of range"):
        evaluate_sorted_intent_nonce_sequence_gate(
            last_used_nonce=0,
            nonce_count=INTENT_NONCE_SEQUENCE_KERNEL_MAX + 1,
            nonce_0=1,
            nonce_1=2,
            nonce_2=3,
            nonce_3=4,
            nonce_4=5,
            nonce_5=6,
            nonce_6=7,
            nonce_7=8,
        )


def test_wrapper_sorts_unsorted_nonce_stream_before_checking_sequence() -> None:
    outcome = evaluate_intent_nonce_sequence(last_used_nonce=4, nonce_values=(7, 5, 6))
    assert outcome.strict_increasing is True
    assert outcome.contiguous_from_last is True
    assert outcome.sequence_ok is True
    assert outcome.next_last_nonce == 7


def test_wrapper_accepts_long_contiguous_nonce_stream() -> None:
    values = tuple(range(10, 10 + INTENT_NONCE_SEQUENCE_KERNEL_MAX + 1))
    outcome = evaluate_intent_nonce_sequence(last_used_nonce=9, nonce_values=values)
    assert outcome.nonce_count == INTENT_NONCE_SEQUENCE_KERNEL_MAX + 1
    assert outcome.strict_increasing is True
    assert outcome.contiguous_from_last is True
    assert outcome.sequence_ok is True
    assert outcome.next_last_nonce == 9 + len(values)


def test_wrapper_rejects_long_duplicate_nonce_stream() -> None:
    values = tuple(range(10, 10 + INTENT_NONCE_SEQUENCE_KERNEL_MAX)) + (17,)
    outcome = evaluate_intent_nonce_sequence(last_used_nonce=9, nonce_values=values)
    assert outcome.strict_increasing is False
    assert outcome.contiguous_from_last is False
    assert outcome.sequence_ok is False
    assert outcome.next_last_nonce == 9


def test_wrapper_rejects_long_gap_nonce_stream() -> None:
    values = (10, 11, 12, 13, 14, 15, 16, 17, 19)
    outcome = evaluate_intent_nonce_sequence(last_used_nonce=9, nonce_values=values)
    assert outcome.strict_increasing is True
    assert outcome.contiguous_from_last is False
    assert outcome.sequence_ok is False
    assert outcome.next_last_nonce == 9


@pytest.mark.parametrize(
    ("last_used_nonce", "nonce_values", "exc_type", "match"),
    [
        (True, (1,), TypeError, "last_used_nonce must be an int"),
        (0, (True,), TypeError, r"nonce_values\[0\] must be an int"),
        (0, (0,), ValueError, r"nonce_values\[0\] out of u32 range: 0"),
        (0, (-1,), ValueError, r"nonce_values\[0\] out of u32 range: -1"),
        (0, (0x1_0000_0000,), ValueError, r"nonce_values\[0\] out of u32 range: 4294967296"),
    ],
)
def test_wrapper_rejects_noncanonical_inputs(
    last_used_nonce: object,
    nonce_values: tuple[object, ...],
    exc_type: type[Exception],
    match: str,
) -> None:
    with pytest.raises(exc_type, match=match):
        evaluate_intent_nonce_sequence(
            last_used_nonce=last_used_nonce,
            nonce_values=nonce_values,
        )
