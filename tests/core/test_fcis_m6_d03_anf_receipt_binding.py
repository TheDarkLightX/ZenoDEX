from __future__ import annotations

from dataclasses import replace
from typing import cast

from src.core.fcis_authority_admission import (
    CanonicalAuthorityClaimBytesV1,
    admit_fcis_authority_claim_v1,
    encode_fcis_authority_claim_v1,
)
from src.core.fcis_authority_normal_form_v1 import (
    FCISAuthorityNormalFormV1,
    FCISProofContextRequirementV1,
)
from src.core.fcis_decision_derivation import (
    AcceptV1,
    RejectV1,
    _claim_root_v1,
    acceptance_receipt_root_v1,
    evaluate_source_bound_fcis_decision_v1,
    evaluate_source_bound_fcis_decision_with_anf_v1,
)
from src.core.fcis_decision_values import FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1
from src.core.fcis_fee_occurrence_extractor import (
    SourceBoundFeeOccurrenceV1,
    extract_source_bound_fee_occurrence_v1,
)
from src.core.fcis_step_evaluation_values import FCISStepEvaluationOkV1
from src.core.fcis_transition_budget import FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1
from src.core.fcis_transition_values import (
    FCIS_COMMIT_PLAN_SCHEMA_ID_V1,
    FCIS_DEX_PATCH_SCHEMA_ID_V1,
)
from src.state.canonical import domain_sep_bytes, sha256_hex
from tests.core.test_fcis_decision_derivation import _exact_inputs


def _digest(label: str) -> str:
    return cast(str, sha256_hex(domain_sep_bytes("fcis-m6-d03-test", version=1) + label.encode()))


def _source_occurrence(inputs: dict[str, object]) -> SourceBoundFeeOccurrenceV1:
    result = extract_source_bound_fee_occurrence_v1(
        state_source=inputs["state_source"],
        settlement=inputs["settlement"],
        intents=inputs["intents"],
        context=inputs["context"],
    )
    assert type(result) is SourceBoundFeeOccurrenceV1
    return result


def _authority_normal_form(
    evaluation: FCISStepEvaluationOkV1,
    base: AcceptV1,
    budget: object,
) -> FCISAuthorityNormalFormV1:
    plan = base.commit_plan
    _, patch_root = _claim_root_v1(FCIS_DEX_PATCH_SCHEMA_ID_V1, plan.patch)
    _, plan_root = _claim_root_v1(FCIS_COMMIT_PLAN_SCHEMA_ID_V1, plan)
    _, budget_hash = _claim_root_v1(FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1, budget)
    binding = evaluation.candidate.source_fee_occurrence
    assert binding is not None
    evidence = evaluation.evidence
    return FCISAuthorityNormalFormV1(
        command_root=evidence.command_root,
        execution_context_root=evidence.execution_context_hash,
        pre_state_root=evidence.pre_state_root,
        next_state_root=evidence.post_state_root,
        support_root=evidence.support_root,
        support_set_commitment=evidence.support_set_commitment,
        snapshot_commitment=evidence.snapshot_commitment,
        boundary_root=f"0x{binding.segment.boundary_root}",
        policy_root=f"0x{binding.segment.policy_root}",
        witness_tuple_root=f"0x{binding.segment.witness_tuple_root}",
        semantic_stream_root=f"0x{binding.segment.semantic_stream_root}",
        lineage_stream_root=f"0x{binding.segment.lineage_stream_root}",
        patch_root=patch_root,
        commit_plan_root=plan_root,
        c3_claim_set_root=_digest("c3"),
        budget_root=budget_hash,
        evaluation_certificate_root=_digest("evaluation"),
        receipt_certificate_root=_digest("receipt-certificate"),
        bundle_certificate_root=_digest("bundle-certificate"),
        outbox_certificate_root=_digest("outbox-certificate"),
        acceptance_decision_root=_digest("decision"),
        acceptance_receipt_root=acceptance_receipt_root_v1(base),
        base_bundle_root=_digest("base-bundle"),
        outbox_plan_root=_digest("outbox-plan"),
        tcg_topology_root=_digest("tcg-topology"),
        tcg_instance_root=_digest("tcg-instance"),
        dra_pre_history_root=_digest("dra-pre"),
        dra_post_history_root=_digest("dra-post"),
        migration_authority_epoch_root=_digest("migration-epoch"),
        proof_context_requirement=FCISProofContextRequirementV1.NOT_REQUIRED,
        proof_context_root=None,
    )


def test_anf_bound_receipt_carries_exact_version_and_root() -> None:
    inputs = _exact_inputs()
    occurrence = _source_occurrence(inputs)
    base_evaluation = evaluate_source_bound_fcis_step_candidate_v1_for_test(occurrence)
    base = evaluate_source_bound_fcis_decision_v1(
        source_occurrence=occurrence,
        budget=inputs["budget"],
    )
    assert type(base) is AcceptV1
    assert type(base_evaluation) is FCISStepEvaluationOkV1
    anf = _authority_normal_form(base_evaluation, base, inputs["budget"])

    decision = evaluate_source_bound_fcis_decision_with_anf_v1(
        source_occurrence=occurrence,
        budget=inputs["budget"],
        authority_normal_form=anf,
    )

    assert type(decision) is AcceptV1
    assert decision.receipt.binding.authority_normal_form_version == (
        "zenodex/fcis/authority-normal-form/v1"
    )
    assert decision.receipt.binding.authority_normal_form_root == anf.root
    assert acceptance_receipt_root_v1(decision) != anf.acceptance_receipt_root
    encoded = encode_fcis_authority_claim_v1(
        FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
        decision.receipt,
    )
    assert type(encoded) is CanonicalAuthorityClaimBytesV1
    admitted = admit_fcis_authority_claim_v1(
        FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
        decision.receipt,
    )
    assert getattr(admitted, "value", None) == decision.receipt


def test_anf_bound_receipt_rejects_missing_or_crossed_anf() -> None:
    inputs = _exact_inputs()
    occurrence = _source_occurrence(inputs)
    base_evaluation = evaluate_source_bound_fcis_step_candidate_v1_for_test(occurrence)
    base = evaluate_source_bound_fcis_decision_v1(
        source_occurrence=occurrence,
        budget=inputs["budget"],
    )
    assert type(base) is AcceptV1
    assert type(base_evaluation) is FCISStepEvaluationOkV1
    anf = _authority_normal_form(base_evaluation, base, inputs["budget"])

    missing = evaluate_source_bound_fcis_decision_with_anf_v1(
        source_occurrence=occurrence,
        budget=inputs["budget"],
        authority_normal_form=None,
    )
    assert type(missing) is RejectV1
    assert type(missing.receipt.code).__name__ == "OwnedEnumV1"
    assert missing.receipt.public_reason == "D03 requires one exact Authority Normal Form"

    foreign = replace(anf, command_root=_digest("foreign-command"))
    crossed = evaluate_source_bound_fcis_decision_with_anf_v1(
        source_occurrence=occurrence,
        budget=inputs["budget"],
        authority_normal_form=foreign,
    )
    assert type(crossed) is RejectV1


def evaluate_source_bound_fcis_step_candidate_v1_for_test(
    occurrence: SourceBoundFeeOccurrenceV1,
) -> FCISStepEvaluationOkV1:
    from src.core.fcis_step_evaluator import (
        evaluate_source_bound_fcis_step_candidate_v1,
    )

    result = evaluate_source_bound_fcis_step_candidate_v1(source_occurrence=occurrence)
    assert type(result) is FCISStepEvaluationOkV1
    return result
