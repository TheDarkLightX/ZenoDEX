"""Deterministic property checks for J08 rollback sequence closure."""

from __future__ import annotations

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_j08_rollback_check import build_states
from src.core.fcis_m6_j08_rollback import (
    J08RollbackCodeV1,
    J08RollbackReasonV1,
    J08RollbackRejectV1,
    J08RollbackSuccessV1,
    rollback_j08_v1,
)


@settings(max_examples=24, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(sequence=st.integers(min_value=0, max_value=8))  # type: ignore[untyped-decorator]
def test_only_the_single_successor_epoch_is_accepted(sequence: int) -> None:
    switch, source, anchor = build_states()
    result = rollback_j08_v1(
        switch,
        source,
        anchor,
        reason=J08RollbackReasonV1.POST_SWITCH_VALIDATION_FAILURE,
        rollback_sequence=sequence,
    )
    if sequence == source.authority_epoch_index + 1:
        assert type(result) is J08RollbackSuccessV1
    else:
        assert type(result) is J08RollbackRejectV1
        assert result.code is J08RollbackCodeV1.SEQUENCE_REJECTED
