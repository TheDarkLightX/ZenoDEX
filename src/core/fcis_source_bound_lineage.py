"""Source-bound R04 composition over pre-evaluation fee evidence.

The concrete R04 closure accepts an exact ``CanonicalFeeOccurrenceSegmentV1``.
This module removes that caller-controlled input from the public research
surface. It first admits command, context, and pre-state sources and derives the
transition-local segment. Only after that does it evaluate the candidate,
derive the decision and bundle, and close the certificate.

The module remains unmounted. Exact Python admission does not prove shell
authentication, datastore-current state authority, deployment pinning,
migration activation, durable publication, or no-bypass.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import TypeAlias, cast, final

from .fcis_commit_bundle_derivation import build_commit_bundle_v1
from .fcis_decision_derivation import (
    AcceptV1,
    RejectV1,
    evaluate_source_bound_fcis_decision_v1,
)
from .fcis_fee_occurrence_extractor import (
    SourceBoundFeeOccurrenceRejectV1,
    SourceBoundFeeOccurrenceV1,
    extract_source_bound_fee_occurrence_v1,
    verify_source_bound_fee_occurrence_v1,
)
from .fcis_lineage_closure import (
    FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1,
    FCISLineageClaimKeyV1,
    FCISLineageClosureCertificateV1,
    FCISLineageClosureRejectV1,
    _build_fcis_lineage_closure_from_artifacts_v1,
)
from .fcis_step_evaluation_values import (
    FCISStepEvaluationRejectV1,
)
from .fcis_step_evaluator import (
    evaluate_source_bound_fcis_step_candidate_v1,
)
from .fcis_transition_budget import TransitionBudgetV1

_SOURCE_BOUND_LINEAGE_TOKEN_V1 = object()
_REQUIRED_LINEAGE_KEYS_V1 = frozenset(FCISLineageClaimKeyV1)


class FCISSourceBoundLineageCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    EXTRACTION_REJECTED = "extraction_rejected"
    EVALUATION_REJECTED = "evaluation_rejected"
    DECISION_REJECTED = "decision_rejected"
    BUNDLE_REJECTED = "bundle_rejected"
    CLOSURE_REJECTED = "closure_rejected"
    INCOMPLETE_CLAIM_SET = "incomplete_claim_set"
    LINEAGE_IDENTITY_MISMATCH = "lineage_identity_mismatch"
    INTERNAL_RELATION_FAILURE = "internal_relation_failure"


@final
@dataclass(frozen=True, slots=True)
class FCISSourceBoundLineageRejectV1:
    """Stable source-bound composition rejection with no commit authority."""

    code: FCISSourceBoundLineageCodeV1
    path: tuple[str, ...]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _SOURCE_BOUND_LINEAGE_TOKEN_V1:
            raise TypeError("source-bound lineage rejection requires controlled derivation")
        if type(self.code) is not FCISSourceBoundLineageCodeV1:
            raise TypeError("source-bound lineage rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("source-bound lineage rejection path must be exact")


@final
@dataclass(frozen=True, slots=True)
class FCISSourceBoundLineageCertificateV1:
    """One pre-evaluation extraction and one concrete closure over its candidate."""

    extraction: SourceBoundFeeOccurrenceV1
    closure: FCISLineageClosureCertificateV1
    budget: TransitionBudgetV1
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _SOURCE_BOUND_LINEAGE_TOKEN_V1:
            raise TypeError("source-bound lineage certificate requires controlled derivation")
        if type(self.extraction) is not SourceBoundFeeOccurrenceV1:
            raise TypeError("source-bound lineage extraction must be exact")
        if type(self.closure) is not FCISLineageClosureCertificateV1:
            raise TypeError("source-bound lineage closure must be exact")
        if type(self.budget) is not TransitionBudgetV1:
            raise TypeError("source-bound lineage budget must be exact")
        if self.closure.evaluation.material != self.extraction.material:
            raise ValueError("source-bound lineage admitted-material mismatch")
        if self.closure.occurrence_segment is not self.extraction.segment:
            raise ValueError("source-bound lineage segment identity mismatch")
        if self.closure.certificate_root != self.closure.closed_claims.root:
            raise ValueError("source-bound lineage certificate root mismatch")
        actual_keys = frozenset(claim.key for claim in self.closure.closed_claims.claims)
        if actual_keys != _REQUIRED_LINEAGE_KEYS_V1:
            raise ValueError("source-bound lineage closed claim set is incomplete")

    @property
    def certificate_root(self) -> str:
        return cast(str, self.closure.certificate_root)


FCISSourceBoundLineageResultV1: TypeAlias = (
    FCISSourceBoundLineageCertificateV1 | FCISSourceBoundLineageRejectV1
)


def _reject_v1(
    code: FCISSourceBoundLineageCodeV1,
    *path: str,
) -> FCISSourceBoundLineageRejectV1:
    return FCISSourceBoundLineageRejectV1(
        code=code,
        path=path,
        _construction_token=_SOURCE_BOUND_LINEAGE_TOKEN_V1,
    )


def _complete_claim_set_v1(closure: FCISLineageClosureCertificateV1) -> bool:
    keys = frozenset(claim.key for claim in closure.closed_claims.claims)
    return keys == _REQUIRED_LINEAGE_KEYS_V1


def derive_source_bound_fcis_lineage_v1(
    *,
    state_source: object,
    settlement: object,
    intents: object,
    context: object,
    budget: object,
    axis_order: object = FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1,
) -> FCISSourceBoundLineageResultV1:
    """Extract first, then evaluate and close one R04 certificate."""

    if type(budget) is not TransitionBudgetV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.WRONG_EXACT_TYPE,
            "budget",
        )

    extraction = extract_source_bound_fee_occurrence_v1(
        state_source=state_source,
        settlement=settlement,
        intents=intents,
        context=context,
    )
    if type(extraction) is SourceBoundFeeOccurrenceRejectV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.EXTRACTION_REJECTED,
            extraction.code.value,
            *extraction.path,
        )

    evaluation = evaluate_source_bound_fcis_step_candidate_v1(
        source_occurrence=extraction,
    )
    if type(evaluation) is FCISStepEvaluationRejectV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.EVALUATION_REJECTED,
            evaluation.phase.value,
            evaluation.code,
        )
    if evaluation.material != extraction.material:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.LINEAGE_IDENTITY_MISMATCH,
            "material",
        )

    decision = evaluate_source_bound_fcis_decision_v1(
        source_occurrence=extraction,
        budget=budget,
    )
    if type(decision) is RejectV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.DECISION_REJECTED,
            decision.receipt.public_reason,
        )
    if type(decision) is not AcceptV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.DECISION_REJECTED,
            "unsupported_variant",
        )

    bundle = build_commit_bundle_v1(decision)
    if type(bundle) is RejectV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.BUNDLE_REJECTED,
            bundle.receipt.public_reason,
        )

    closure = _build_fcis_lineage_closure_from_artifacts_v1(
        evaluation=evaluation,
        occurrence_segment=extraction.segment,
        decision=decision,
        bundle=bundle,
        budget=budget,
        axis_order=axis_order,
    )
    if type(closure) is FCISLineageClosureRejectV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.CLOSURE_REJECTED,
            closure.code.value,
            *closure.path,
        )
    if closure.evaluation.material != extraction.material:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.LINEAGE_IDENTITY_MISMATCH,
            "material",
        )
    if closure.occurrence_segment is not extraction.segment:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.LINEAGE_IDENTITY_MISMATCH,
            "occurrence_segment",
        )
    if not _complete_claim_set_v1(closure):
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.INCOMPLETE_CLAIM_SET,
            "closed_claims",
        )
    try:
        return FCISSourceBoundLineageCertificateV1(
            extraction=extraction,
            closure=closure,
            budget=budget,
            _construction_token=_SOURCE_BOUND_LINEAGE_TOKEN_V1,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.INTERNAL_RELATION_FAILURE,
            "certificate",
        )


def verify_source_bound_fcis_lineage_v1(
    certificate: object,
) -> FCISSourceBoundLineageRejectV1 | None:
    """Re-extract sources, re-evaluate, and rebuild the complete closure."""

    if type(certificate) is not FCISSourceBoundLineageCertificateV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.WRONG_EXACT_TYPE,
            "certificate",
        )
    try:
        certificate.__post_init__(_SOURCE_BOUND_LINEAGE_TOKEN_V1)
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.LINEAGE_IDENTITY_MISMATCH,
            "certificate",
        )

    extraction_reject = verify_source_bound_fee_occurrence_v1(certificate.extraction)
    if extraction_reject is not None:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.EXTRACTION_REJECTED,
            extraction_reject.code.value,
            *extraction_reject.path,
        )

    material = certificate.extraction.material
    fresh_evaluation = evaluate_source_bound_fcis_step_candidate_v1(
        source_occurrence=certificate.extraction,
    )
    if type(fresh_evaluation) is FCISStepEvaluationRejectV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.EVALUATION_REJECTED,
            fresh_evaluation.phase.value,
            fresh_evaluation.code,
        )
    if fresh_evaluation.material != material:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.LINEAGE_IDENTITY_MISMATCH,
            "fresh_material",
        )

    fresh_closure = _build_fcis_lineage_closure_from_artifacts_v1(
        evaluation=fresh_evaluation,
        occurrence_segment=certificate.extraction.segment,
        decision=certificate.closure.decision,
        bundle=certificate.closure.bundle,
        budget=certificate.budget,
        axis_order=FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1,
    )
    if type(fresh_closure) is FCISLineageClosureRejectV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.CLOSURE_REJECTED,
            fresh_closure.code.value,
            *fresh_closure.path,
        )
    if fresh_closure != certificate.closure:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.LINEAGE_IDENTITY_MISMATCH,
            "closure",
        )
    return None


__all__ = (
    "FCISSourceBoundLineageCertificateV1",
    "FCISSourceBoundLineageCodeV1",
    "FCISSourceBoundLineageRejectV1",
    "FCISSourceBoundLineageResultV1",
    "derive_source_bound_fcis_lineage_v1",
    "verify_source_bound_fcis_lineage_v1",
)
