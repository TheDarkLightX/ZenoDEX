from __future__ import annotations

from dataclasses import replace
from typing import Any

import pytest

import src.core.fcis_step_evaluator as step_evaluator
from src.core.fcis_fee_occurrence_extractor import (
    SourceBoundFeeOccurrenceResultV1,
    SourceBoundFeeOccurrenceV1,
    extract_source_bound_fee_occurrence_v1,
)
from src.core.fcis_step_evaluation_values import (
    FCISFeeOccurrenceBindingV1,
    FCISStepEvaluationOkV1,
    FCISStepEvaluationRejectV1,
)
from src.core.fcis_step_evaluator import (
    evaluate_fcis_step_candidate_v1,
    evaluate_source_bound_fcis_step_candidate_v1,
)
from src.state.fcis_execution_context_values import FCISFeeSplitPolicySourceV1
from tests.core.test_fcis_decision_derivation import _exact_inputs


def _extract() -> SourceBoundFeeOccurrenceResultV1:
    inputs = _exact_inputs()
    return extract_source_bound_fee_occurrence_v1(
        state_source=inputs["state_source"],
        settlement=inputs["settlement"],
        intents=inputs["intents"],
        context=inputs["context"],
    )


def test_source_bound_evaluator_consumes_exact_segment_before_fee_transition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    occurrence = _extract()
    assert type(occurrence) is SourceBoundFeeOccurrenceV1
    observed: dict[str, object] = {}
    original = step_evaluator._fee_candidate_observed_v5

    def spy(**kwargs: Any) -> object:
        observed["source_fee_occurrence"] = kwargs["source_fee_occurrence"]
        return original(**kwargs)

    monkeypatch.setattr(step_evaluator, "_fee_candidate_observed_v5", spy)

    result = evaluate_source_bound_fcis_step_candidate_v1(
        source_occurrence=occurrence,
    )

    assert type(result) is FCISStepEvaluationOkV1
    binding = observed["source_fee_occurrence"]
    assert type(binding) is FCISFeeOccurrenceBindingV1
    assert binding.segment is occurrence.segment
    assert result.candidate.fee_allocation is not None
    assert result.candidate.source_fee_occurrence is binding
    assert result.evidence.source_fee_occurrence is binding


def test_regular_evaluator_has_no_source_binding() -> None:
    inputs = _exact_inputs()

    result = evaluate_fcis_step_candidate_v1(
        state_source=inputs["state_source"],
        settlement=inputs["settlement"],
        intents=inputs["intents"],
        context=inputs["context"],
    )

    assert type(result) is FCISStepEvaluationOkV1
    assert result.evidence.source_fee_occurrence is None
    assert result.candidate.fee_allocation is not None
    assert result.candidate.source_fee_occurrence is None


def test_crossed_source_segment_rejects_before_candidate() -> None:
    first_inputs = _exact_inputs()
    second_context = replace(
        first_inputs["context"],
        fee_split_policy=FCISFeeSplitPolicySourceV1(
            buyback_bps=10_000,
            treasury_bps=0,
            rewards_bps=0,
        ),
    )
    second_inputs = {**first_inputs, "context": second_context}
    first = extract_source_bound_fee_occurrence_v1(
        state_source=first_inputs["state_source"],
        settlement=first_inputs["settlement"],
        intents=first_inputs["intents"],
        context=first_inputs["context"],
    )
    second = extract_source_bound_fee_occurrence_v1(
        state_source=second_inputs["state_source"],
        settlement=second_inputs["settlement"],
        intents=second_inputs["intents"],
        context=second_inputs["context"],
    )
    assert type(first) is SourceBoundFeeOccurrenceV1
    assert type(second) is SourceBoundFeeOccurrenceV1
    object.__setattr__(first, "segment", second.segment)

    result = evaluate_source_bound_fcis_step_candidate_v1(
        source_occurrence=first,
    )

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.code == "source_occurrence_rejected"
    assert result.path[0] == "source_occurrence"


def test_source_occurrence_binding_constructor_is_not_caller_mintable() -> None:
    occurrence = _extract()
    assert type(occurrence) is SourceBoundFeeOccurrenceV1

    with pytest.raises(TypeError, match="controlled evaluation"):
        FCISFeeOccurrenceBindingV1(
            segment=occurrence.segment,
            boundary_root=occurrence.segment.boundary_root,
            policy_root=occurrence.segment.policy_root,
            witness_tuple_root=occurrence.segment.witness_tuple_root,
            semantic_stream_root=occurrence.segment.semantic_stream_root,
            lineage_stream_root=occurrence.segment.lineage_stream_root,
            _construction_token=object(),
        )
