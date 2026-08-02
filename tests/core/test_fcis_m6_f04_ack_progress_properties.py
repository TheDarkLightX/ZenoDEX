"""Deterministic generated checks for F04A acknowledgment deletion."""

from __future__ import annotations

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_f04_ack_progress_check import (
    build_acked_payload,
    build_mutated_ack_payload,
    build_pending_payload,
)
from src.core.fcis_m6_f04_ack_progress import (
    F04AckProgressCodeV1,
    F04AckProgressRejectV1,
    check_f04_ack_progress,
)


@settings(max_examples=24, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(kind=st.sampled_from(("removed", "mutated")))  # type: ignore[untyped-decorator]
def test_generated_prior_ack_breaks_never_accept(kind: str) -> None:
    prior = build_acked_payload()
    current = build_pending_payload() if kind == "removed" else build_mutated_ack_payload()
    result = check_f04_ack_progress(prior, current)

    assert type(result) is F04AckProgressRejectV1
    assert result.code in {
        F04AckProgressCodeV1.ACK_REMOVED,
        F04AckProgressCodeV1.ACK_MUTATED,
    }
