from __future__ import annotations

from hashlib import sha256
from itertools import permutations

import pytest

from src.core.fcis_commit_bundle_derivation import (
    CommitBundleV1,
    build_commit_bundle_v1,
)
from src.core.fcis_decision_derivation import (
    AcceptV1,
    evaluate_fcis_decision_v1,
)
from src.core.fcis_fee_apportionment_values import FeeApportionmentKeyV2
from src.core.fcis_fee_occurrence_normal_form import (
    CanonicalFeeOccurrenceSegmentV1,
    FeeWitnessOccurrenceClaimV1,
    canonicalize_fee_occurrence_segment_v1,
)
from src.core.fcis_lineage_closure import (
    FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1,
    FCISLineageAxisV1,
    FCISLineageClaimKeyV1,
    FCISLineageClaimSetV1,
    FCISLineageClaimV1,
    FCISLineageClosureCertificateV1,
    FCISLineageClosureCodeV1,
    FCISLineageClosureRejectV1,
    build_fcis_lineage_closure_from_artifacts_v1,
    canonicalize_fcis_lineage_claims_v1,
    close_fcis_lineage_claim_sets_v1,
    derive_fcis_lineage_closure_v1,
)
from src.core.fcis_step_evaluation_values import FCISStepEvaluationOkV1
from src.core.fcis_step_evaluator import evaluate_fcis_step_candidate_v1
from tests.core.test_fcis_decision_derivation import _exact_inputs


def _digest(label: str) -> str:
    return sha256(label.encode()).hexdigest()


def _root(label: str) -> str:
    return f"0x{_digest(label)}"


def _witness(
    position: int,
    amount: int,
    label: str,
) -> FeeWitnessOccurrenceClaimV1:
    return FeeWitnessOccurrenceClaimV1(
        position=position,
        key=FeeApportionmentKeyV2("protocol-fees", "asset-a"),
        amount=amount,
        source_witness_root=_digest(label),
    )


def _segment(
    label: str,
    amounts: tuple[int, ...],
    *,
    boundary_label: str = "boundary",
    policy_label: str = "policy",
) -> CanonicalFeeOccurrenceSegmentV1:
    result = canonicalize_fee_occurrence_segment_v1(
        boundary_root=_digest(boundary_label),
        policy_root=_digest(policy_label),
        witnesses=tuple(
            _witness(position, amount, f"{label}:{position}")
            for position, amount in enumerate(amounts)
        ),
    )
    assert type(result) is CanonicalFeeOccurrenceSegmentV1
    return result


def _derive(
    segment: CanonicalFeeOccurrenceSegmentV1,
    *,
    axis_order: tuple[FCISLineageAxisV1, ...] = FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1,
) -> FCISLineageClosureCertificateV1 | FCISLineageClosureRejectV1:
    return derive_fcis_lineage_closure_v1(
        **_exact_inputs(),
        occurrence_segment=segment,
        axis_order=axis_order,
    )


def _artifacts() -> tuple[FCISStepEvaluationOkV1, AcceptV1, CommitBundleV1]:
    inputs = _exact_inputs()
    evaluation = evaluate_fcis_step_candidate_v1(
        state_source=inputs["state_source"],
        settlement=inputs["settlement"],
        intents=inputs["intents"],
        context=inputs["context"],
    )
    decision = evaluate_fcis_decision_v1(**inputs)
    assert type(evaluation) is FCISStepEvaluationOkV1
    assert type(decision) is AcceptV1
    bundle = build_commit_bundle_v1(decision)
    assert type(bundle) is CommitBundleV1
    return evaluation, decision, bundle


def test_all_six_axis_orders_close_to_one_concrete_certificate() -> None:
    segment = _segment("whole", (867,))
    roots: set[str] = set()
    closed_claims: set[FCISLineageClaimSetV1] = set()

    for order in permutations(FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1):
        result = _derive(segment, axis_order=tuple(order))
        assert type(result) is FCISLineageClosureCertificateV1
        roots.add(result.certificate_root)
        closed_claims.add(result.closed_claims)
        assert (
            result.closed_claims.value_for(FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT)
            is not None
        )
        assert (
            result.closed_claims.value_for(FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT)
            == result.receipt_extension.extension_root
        )
        assert (
            result.closed_claims.value_for(FCISLineageClaimKeyV1.BUNDLE_CERTIFICATE_ROOT)
            == result.bundle_extension.bundle_extension_root
        )
        assert (
            result.closed_claims.value_for(FCISLineageClaimKeyV1.OUTBOX_CERTIFICATE_ROOT)
            == result.bundle_extension.outbox_extension_root
        )

    assert len(roots) == 1
    assert len(closed_claims) == 1


def test_same_semantics_different_provenance_conflicts_across_faces() -> None:
    whole = _derive(_segment("whole", (867,)))
    split = _derive(_segment("split", (493, 374)))
    assert type(whole) is FCISLineageClosureCertificateV1
    assert type(split) is FCISLineageClosureCertificateV1
    assert (
        whole.occurrence_segment.semantic_stream_root
        == split.occurrence_segment.semantic_stream_root
    )
    assert (
        whole.occurrence_segment.lineage_stream_root != split.occurrence_segment.lineage_stream_root
    )

    crossed = close_fcis_lineage_claim_sets_v1(
        (
            split.semantic_claims,
            whole.authority_claims,
            whole.durability_claims,
        )
    )
    assert type(crossed) is FCISLineageClosureRejectV1
    assert crossed.code is FCISLineageClosureCodeV1.CLAIM_CONFLICT
    assert any("fee/lineage_stream_root" in part for part in crossed.path)


def test_forged_derived_claim_is_recomputed_and_rejected() -> None:
    certificate = _derive(_segment("whole", (867,)))
    assert type(certificate) is FCISLineageClosureCertificateV1
    forged = canonicalize_fcis_lineage_claims_v1(
        (
            FCISLineageClaimV1(
                FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT,
                _root("forged-evaluation"),
            ),
        )
    )
    result = close_fcis_lineage_claim_sets_v1((forged, certificate.semantic_claims))
    assert type(result) is FCISLineageClosureRejectV1
    assert result.code is FCISLineageClosureCodeV1.DERIVED_CLAIM_CONFLICT


def test_semantic_axis_alone_cannot_mint_receipt_or_bundle_authority() -> None:
    certificate = _derive(_segment("whole", (867,)))
    assert type(certificate) is FCISLineageClosureCertificateV1
    result = close_fcis_lineage_claim_sets_v1((certificate.semantic_claims,))
    assert type(result) is FCISLineageClaimSetV1
    assert result.value_for(FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT) is not None
    assert result.value_for(FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT) is None
    assert result.value_for(FCISLineageClaimKeyV1.BUNDLE_CERTIFICATE_ROOT) is None
    assert result.value_for(FCISLineageClaimKeyV1.OUTBOX_CERTIFICATE_ROOT) is None


def test_boundary_and_policy_substitution_change_the_terminal_certificate() -> None:
    base = _derive(_segment("same", (867,)))
    changed_boundary = _derive(_segment("same", (867,), boundary_label="foreign-boundary"))
    changed_policy = _derive(_segment("same", (867,), policy_label="foreign-policy"))
    assert type(base) is FCISLineageClosureCertificateV1
    assert type(changed_boundary) is FCISLineageClosureCertificateV1
    assert type(changed_policy) is FCISLineageClosureCertificateV1
    assert base.certificate_root != changed_boundary.certificate_root
    assert base.certificate_root != changed_policy.certificate_root


def test_bundle_must_retain_the_exact_decision_object() -> None:
    evaluation, first_decision, bundle = _artifacts()
    second_decision = evaluate_fcis_decision_v1(**_exact_inputs())
    assert type(second_decision) is AcceptV1
    assert second_decision == first_decision
    assert second_decision is not first_decision

    result = build_fcis_lineage_closure_from_artifacts_v1(
        evaluation=evaluation,
        occurrence_segment=_segment("whole", (867,)),
        decision=second_decision,
        bundle=bundle,
        budget=_exact_inputs()["budget"],
    )
    assert type(result) is FCISLineageClosureRejectV1
    assert result.code is FCISLineageClosureCodeV1.LINEAGE_MISMATCH


def test_corrupt_cached_bundle_root_fails_fresh_recomputation() -> None:
    evaluation, decision, bundle = _artifacts()
    object.__setattr__(bundle, "_bundle_root", _root("corrupt-bundle"))
    result = build_fcis_lineage_closure_from_artifacts_v1(
        evaluation=evaluation,
        occurrence_segment=_segment("whole", (867,)),
        decision=decision,
        bundle=bundle,
        budget=_exact_inputs()["budget"],
    )
    assert type(result) is FCISLineageClosureRejectV1
    assert result.code is FCISLineageClosureCodeV1.LINEAGE_MISMATCH


def test_axis_order_requires_one_exact_permutation() -> None:
    segment = _segment("whole", (867,))
    for bad_order in (
        (),
        (FCISLineageAxisV1.SEMANTIC,),
        (
            FCISLineageAxisV1.SEMANTIC,
            FCISLineageAxisV1.SEMANTIC,
            FCISLineageAxisV1.DURABILITY,
        ),
        ("semantic", "authority", "durability"),
    ):
        result = _derive(segment, axis_order=bad_order)  # type: ignore[arg-type]
        assert type(result) is FCISLineageClosureRejectV1
        assert result.code is FCISLineageClosureCodeV1.INVALID_AXIS_ORDER


def test_claim_join_is_idempotent_but_never_last_writer_wins() -> None:
    claim = FCISLineageClaimV1(FCISLineageClaimKeyV1.COMMAND_ROOT, _root("command"))
    duplicate = canonicalize_fcis_lineage_claims_v1((claim, claim))
    assert duplicate.claims == (claim,)

    with pytest.raises(ValueError, match="conflicting lineage claim"):
        canonicalize_fcis_lineage_claims_v1(
            (
                claim,
                FCISLineageClaimV1(
                    FCISLineageClaimKeyV1.COMMAND_ROOT,
                    _root("foreign-command"),
                ),
            )
        )
