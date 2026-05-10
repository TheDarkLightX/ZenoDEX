from __future__ import annotations

import pytest

from src.core.endogenous_reference_gate import (
    REFERENCE_SOURCE_TWAP_ACCUMULATOR,
    REJECT_OK,
    REJECT_SOURCE_NOT_TWAP,
    REJECT_TWAP_ELAPSED_TOO_SHORT,
    REJECT_TWAP_WINDOW_TOO_SHORT,
    endogenous_reference_gate_error,
    evaluate_endogenous_reference_gate,
)


def test_endogenous_reference_gate_accepts_elapsed_twap_accumulator() -> None:
    outcome = evaluate_endogenous_reference_gate(
        source_kind=REFERENCE_SOURCE_TWAP_ACCUMULATOR,
        twap_window_blocks=12,
        reference_elapsed_blocks=2,
        min_twap_window_blocks=10,
        min_reference_elapsed_blocks=1,
    )

    assert outcome.admission_ok is True
    assert outcome.reject_code == REJECT_OK
    assert endogenous_reference_gate_error(outcome) is None


def test_endogenous_reference_gate_rejects_instantaneous_spot_reference() -> None:
    outcome = evaluate_endogenous_reference_gate(
        source_kind="spot",
        twap_window_blocks=12,
        reference_elapsed_blocks=2,
        min_twap_window_blocks=10,
        min_reference_elapsed_blocks=1,
    )

    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_SOURCE_NOT_TWAP
    assert outcome.source_kind_ok is False
    assert endogenous_reference_gate_error(outcome) == "endogenous payout reference requires twap_accumulator source"


def test_endogenous_reference_gate_rejects_too_short_window() -> None:
    outcome = evaluate_endogenous_reference_gate(
        source_kind=REFERENCE_SOURCE_TWAP_ACCUMULATOR,
        twap_window_blocks=9,
        reference_elapsed_blocks=2,
        min_twap_window_blocks=10,
    )

    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_TWAP_WINDOW_TOO_SHORT
    assert outcome.twap_window_ok is False


def test_endogenous_reference_gate_rejects_same_block_reference() -> None:
    outcome = evaluate_endogenous_reference_gate(
        source_kind=REFERENCE_SOURCE_TWAP_ACCUMULATOR,
        twap_window_blocks=10,
        reference_elapsed_blocks=0,
        min_twap_window_blocks=10,
        min_reference_elapsed_blocks=1,
    )

    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_TWAP_ELAPSED_TOO_SHORT
    assert outcome.reference_elapsed_ok is False


def test_endogenous_reference_gate_bounded_acceptance_surface() -> None:
    for source_kind in ("spot", REFERENCE_SOURCE_TWAP_ACCUMULATOR):
        for window in range(5):
            for elapsed in range(4):
                outcome = evaluate_endogenous_reference_gate(
                    source_kind=source_kind,
                    twap_window_blocks=window,
                    reference_elapsed_blocks=elapsed,
                    min_twap_window_blocks=3,
                    min_reference_elapsed_blocks=2,
                )

                expected = source_kind == REFERENCE_SOURCE_TWAP_ACCUMULATOR and window >= 3 and elapsed >= 2
                assert outcome.admission_ok is expected
                assert outcome.checks["source_kind_ok"] is (source_kind == REFERENCE_SOURCE_TWAP_ACCUMULATOR)
                assert outcome.checks["twap_window_ok"] is (window >= 3)
                assert outcome.checks["reference_elapsed_ok"] is (elapsed >= 2)


@pytest.mark.parametrize(
    ("field_name", "overrides", "error_type", "match"),
    [
        ("source_kind", {"source_kind": ""}, ValueError, "source_kind must be non-empty"),
        ("twap_window_blocks", {"twap_window_blocks": True}, TypeError, "twap_window_blocks must be an int"),
        ("reference_elapsed_blocks", {"reference_elapsed_blocks": -1}, ValueError, "reference_elapsed_blocks must be >= 0"),
        ("min_twap_window_blocks", {"min_twap_window_blocks": 0}, ValueError, "min_twap_window_blocks must be >= 1"),
    ],
)
def test_endogenous_reference_gate_rejects_invalid_domains(
    field_name: str,
    overrides: dict[str, object],
    error_type: type[Exception],
    match: str,
) -> None:
    del field_name
    args: dict[str, object] = {
        "source_kind": REFERENCE_SOURCE_TWAP_ACCUMULATOR,
        "twap_window_blocks": 10,
        "reference_elapsed_blocks": 1,
    }
    args.update(overrides)

    with pytest.raises(error_type, match=match):
        evaluate_endogenous_reference_gate(**args)
