"""Recompute the deterministic D03 ANF-to-receipt binding relation."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

from src.core.fcis_authority_admission import (
    CanonicalAuthorityClaimBytesV1,
    admit_fcis_authority_claim_v1,
    encode_fcis_authority_claim_v1,
)
from src.core.fcis_decision_derivation import (
    AcceptV1,
    RejectV1,
    acceptance_receipt_root_v1,
    evaluate_source_bound_fcis_decision_v1,
    evaluate_source_bound_fcis_decision_with_anf_v1,
)
from src.core.fcis_decision_values import FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1
from src.core.fcis_fee_occurrence_extractor import SourceBoundFeeOccurrenceV1
from src.core.fcis_step_evaluation_values import FCISStepEvaluationOkV1
from tests.core.test_fcis_decision_derivation import _exact_inputs
from tests.core.test_fcis_m6_d03_anf_receipt_binding import (
    _authority_normal_form,
    _source_occurrence,
    evaluate_source_bound_fcis_step_candidate_v1_for_test,
)

_VECTOR_PATH = Path("docs/research/m6_tasks/TASK_D03_ANF_RECEIPT_BINDING_VECTOR.json")


def main() -> int:
    vector = cast(dict[str, Any], json.loads(_VECTOR_PATH.read_text(encoding="utf-8")))
    if vector["schema_version"] != "zenodex.fcis.m6.d03.anf-receipt-binding.v1":
        raise AssertionError("D03 schema version drift")
    expected = cast(dict[str, Any], vector["expected"])
    inputs = _exact_inputs()
    occurrence = _source_occurrence(inputs)
    if type(occurrence) is not SourceBoundFeeOccurrenceV1:
        raise AssertionError("D03 fixture occurrence type drift")
    evaluation = evaluate_source_bound_fcis_step_candidate_v1_for_test(occurrence)
    base = evaluate_source_bound_fcis_decision_v1(
        source_occurrence=occurrence,
        budget=inputs["budget"],
    )
    if type(evaluation) is not FCISStepEvaluationOkV1 or type(base) is not AcceptV1:
        raise AssertionError("D03 base fixture no longer accepts")
    anf = _authority_normal_form(evaluation, base, inputs["budget"])
    if anf.root != vector["anf_root"]:
        raise AssertionError("D03 ANF root drift")
    if anf.acceptance_receipt_root != vector["pre_anf_receipt_root"]:
        raise AssertionError("D03 pre-ANF receipt root drift")

    decision = evaluate_source_bound_fcis_decision_with_anf_v1(
        source_occurrence=occurrence,
        budget=inputs["budget"],
        authority_normal_form=anf,
    )
    if type(decision) is not AcceptV1:
        raise AssertionError(f"D03 ANF-bound decision rejected: {decision}")
    if (decision.receipt.binding.authority_normal_form_root == anf.root) is not expected[
        "receipt_contains_anf_root"
    ]:
        raise AssertionError("D03 receipt lost the ANF root")
    final_root = acceptance_receipt_root_v1(decision)
    if (final_root == acceptance_receipt_root_v1(decision)) is not expected[
        "final_receipt_root_recomputes"
    ]:
        raise AssertionError("D03 final receipt root did not recompute")
    if (final_root != anf.acceptance_receipt_root) is not expected[
        "final_receipt_root_differs_from_pre_anf_root"
    ]:
        raise AssertionError("D03 acyclic receipt relation drift")
    encoded = encode_fcis_authority_claim_v1(
        FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
        decision.receipt,
    )
    if type(encoded) is not CanonicalAuthorityClaimBytesV1:
        raise AssertionError("D03 receipt encoding rejected")
    admitted = admit_fcis_authority_claim_v1(
        FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
        decision.receipt,
    )
    if getattr(admitted, "value", None) != decision.receipt:
        raise AssertionError("D03 receipt canonical round trip drift")
    if (
        type(
            evaluate_source_bound_fcis_decision_with_anf_v1(
                source_occurrence=occurrence,
                budget=inputs["budget"],
                authority_normal_form=None,
            )
        )
        is not RejectV1
    ):
        raise AssertionError("D03 missing ANF was accepted")
    foreign = replace(anf, command_root=anf.pre_state_root)
    if (
        type(
            evaluate_source_bound_fcis_decision_with_anf_v1(
                source_occurrence=occurrence,
                budget=inputs["budget"],
                authority_normal_form=foreign,
            )
        )
        is not RejectV1
    ):
        raise AssertionError("D03 foreign source field was accepted")
    print("D03_ANF_RECEIPT_BINDING_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
