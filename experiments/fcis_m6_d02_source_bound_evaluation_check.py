"""Recompute the deterministic D02 source-bound evaluation relation."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

from src.core.fcis_decision_derivation import (
    AcceptV1,
    evaluate_source_bound_fcis_decision_v1,
)
from src.core.fcis_fee_occurrence_extractor import (
    SourceBoundFeeOccurrenceRejectV1,
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
from src.state.fcis_execution_context_values import (
    FCISFeeSplitPolicySourceV1,
    FCISStepExecutionContextV1,
)
from tests.core.test_fcis_decision_derivation import _exact_inputs

_VECTOR_PATH = Path("docs/research/m6_tasks/TASK_D02_SOURCE_BOUND_EVALUATION_VECTOR.json")


def _text(mapping: dict[str, Any], key: str) -> str:
    value = mapping.get(key)
    if type(value) is not str:
        raise AssertionError(f"vector field is not text: {key}")
    return value


def _occurrence(inputs: dict[str, object]) -> SourceBoundFeeOccurrenceV1:
    result = extract_source_bound_fee_occurrence_v1(
        state_source=inputs["state_source"],
        settlement=inputs["settlement"],
        intents=inputs["intents"],
        context=inputs["context"],
    )
    if type(result) is SourceBoundFeeOccurrenceRejectV1:
        raise AssertionError(f"fixture extraction rejected: {result}")
    return result


def main() -> int:
    vector = cast(dict[str, Any], json.loads(_VECTOR_PATH.read_text(encoding="utf-8")))
    if vector["schema_version"] != "zenodex.fcis.m6.d02.source-bound-evaluation.v1":
        raise AssertionError("D02 schema version drift")
    expected_roots = cast(dict[str, Any], vector["binding_roots"])
    expected = cast(dict[str, Any], vector["expected"])
    inputs = _exact_inputs()
    occurrence = _occurrence(inputs)
    segment = occurrence.segment
    actual_roots = {
        "boundary_root": segment.boundary_root,
        "lineage_stream_root": segment.lineage_stream_root,
        "policy_root": segment.policy_root,
        "semantic_stream_root": segment.semantic_stream_root,
        "witness_tuple_root": segment.witness_tuple_root,
    }
    if actual_roots != expected_roots:
        raise AssertionError("D02 source-derived root vector drift")

    evaluation = evaluate_source_bound_fcis_step_candidate_v1(
        source_occurrence=occurrence,
    )
    if type(evaluation) is not FCISStepEvaluationOkV1:
        raise AssertionError(f"source-bound evaluation rejected: {evaluation}")
    if (evaluation.material == occurrence.material) is not expected["material_equal"]:
        raise AssertionError("extractor/evaluator material equality drift")
    candidate_binding = evaluation.candidate.source_fee_occurrence
    evidence_binding = evaluation.evidence.source_fee_occurrence
    if candidate_binding is None or evidence_binding is None:
        raise AssertionError("source-bound evaluation lost its occurrence binding")
    if (candidate_binding is evidence_binding) is not expected[
        "candidate_evidence_binding_identity"
    ]:
        raise AssertionError("candidate/evidence binding identity drift")
    if type(candidate_binding) is not FCISFeeOccurrenceBindingV1:
        raise AssertionError("source binding type drift")
    if (candidate_binding.segment is occurrence.segment) is not expected["segment_identity"]:
        raise AssertionError("evaluator did not consume the exact source segment")

    regular = evaluate_fcis_step_candidate_v1(
        state_source=inputs["state_source"],
        settlement=inputs["settlement"],
        intents=inputs["intents"],
        context=inputs["context"],
    )
    if type(regular) is not FCISStepEvaluationOkV1:
        raise AssertionError(f"regular evaluation rejected: {regular}")
    if regular.candidate.source_fee_occurrence is not expected["regular_evaluation_source_binding"]:
        raise AssertionError("regular evaluator unexpectedly acquired source binding")

    decision = evaluate_source_bound_fcis_decision_v1(
        source_occurrence=occurrence,
        budget=inputs["budget"],
    )
    if (type(decision) is AcceptV1) is not expected["source_bound_decision_accepts"]:
        raise AssertionError(f"source-bound decision result drift: {decision}")
    if type(decision) is not AcceptV1:
        raise AssertionError("source-bound decision did not accept the fixture")
    if decision.next_state != evaluation.candidate.state:
        raise AssertionError("source-bound decision recomputed a different candidate")

    context = cast(FCISStepExecutionContextV1, inputs["context"])
    crossed_context = replace(
        context,
        fee_split_policy=FCISFeeSplitPolicySourceV1(
            buyback_bps=10_000,
            treasury_bps=0,
            rewards_bps=0,
        ),
    )
    crossed_inputs = {**inputs, "context": crossed_context}
    crossed = _occurrence(crossed_inputs)
    object.__setattr__(occurrence, "segment", crossed.segment)
    crossed_result = evaluate_source_bound_fcis_step_candidate_v1(
        source_occurrence=occurrence,
    )
    if type(crossed_result) is not FCISStepEvaluationRejectV1:
        raise AssertionError("crossed source segment was accepted")
    if crossed_result.code != _text(expected, "foreign_segment_reject_code"):
        raise AssertionError("crossed source segment reject code drift")

    print("D02_SOURCE_BOUND_EVALUATION_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
