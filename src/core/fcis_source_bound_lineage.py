"""Source-bound R04 composition over replay-derived fee occurrence evidence.

The existing R04 closure accepts an exact ``CanonicalFeeOccurrenceSegmentV1``.
This module removes that caller-controlled input from the public research
surface. It evaluates the retained FCIS command, derives the segment from the
exact replayed settlement, derives the decision and bundle from the same input
lineage, closes the certificate, and retains the extraction evidence beside the
closure result.

The module remains unmounted. In particular, exact Python values do not by
themselves prove shell authentication, store-current authority, deployment
pinning, migration activation, durable publication, or no-bypass.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import TypeAlias, final

from .fcis_commit_bundle_derivation import CommitBundleV1, build_commit_bundle_v1
from .fcis_decision_derivation import AcceptV1, RejectV1, evaluate_fcis_decision_v1
from .fcis_fee_occurrence_extractor import (
    SourceBoundFeeOccurrenceRejectV1,
    SourceBoundFeeOccurrenceV1,
    extract_source_bound_fee_occurrence_v1,
)
from .fcis_lineage_closure import (
    FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1,
    FCISLineageClaimKeyV1,
    FCISLineageClosureCertificateV1,
    FCISLineageClosureRejectV1,
    build_fcis_lineage_closure_from_artifacts_v1,
)
from .fcis_step_evaluation_values import (
    FCISStepEvaluationOkV1,
    FCISStepEvaluationRejectV1,
)
from .fcis_step_evaluator import evaluate_fcis_step_candidate_v1
from .fcis_transition_budget import TransitionBudgetV1

_SOURCE_BOUND_LINEAGE_TOKEN_V1 = object()
_REQUIRED_LINEAGE_KEYS_V1 = frozenset(FCISLineageClaimKeyV1)


class FCISSourceBoundLineageCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    EVALUATION_REJECTED = "evaluation_rejected"
    EXTRACTION_REJECTED = "extraction_rejected"
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
    """One extraction and one concrete R04 closure from the identical evaluation."""

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
        if self.closure.evaluation is not self.extraction.evaluation:
            raise ValueError("source-bound lineage evaluation identity mismatch")
        if self.closure.occurrence_segment is not self.extraction.segment:
            raise ValueError("source-bound lineage segment identity mismatch")
        if self.closure.certificate_root != self.closure.closed_claims.root:
            raise ValueError("source-bound lineage certificate root mismatch")
        actual_keys = frozenset(claim.key for claim in self.closure.closed_claims.claims)
        if actual_keys != _REQUIRED_LINEAGE_KEYS_V1:
            raise ValueError("source-bound lineage closed claim set is incomplete")

    @property
    def certificate_root(self) -> str:
        return self.closure.certificate_root


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
    """Derive one R04 certificate with no caller-supplied fee lineage roots."""

    if type(budget) is not TransitionBudgetV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.WRONG_EXACT_TYPE,
            "budget",
        )

    evaluation = evaluate_fcis_step_candidate_v1(
        state_source=state_source,
        settlement=settlement,
        intents=intents,
        context=context,
    )
    if type(evaluation) is FCISStepEvaluationRejectV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.EVALUATION_REJECTED,
            evaluation.phase.value,
            evaluation.code,
        )
    if type(evaluation) is not FCISStepEvaluationOkV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.INTERNAL_RELATION_FAILURE,
            "evaluation",
        )

    extraction = extract_source_bound_fee_occurrence_v1(evaluation)
    if type(extraction) is SourceBoundFeeOccurrenceRejectV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.EXTRACTION_REJECTED,
            extraction.code.value,
            *extraction.path,
        )
    if type(extraction) is not SourceBoundFeeOccurrenceV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.INTERNAL_RELATION_FAILURE,
            "extraction",
        )

    decision = evaluate_fcis_decision_v1(
        state_source=state_source,
        settlement=settlement,
        intents=intents,
        context=context,
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
    if type(bundle) is not CommitBundleV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.INTERNAL_RELATION_FAILURE,
            "bundle",
        )

    closure = build_fcis_lineage_closure_from_artifacts_v1(
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
    if type(closure) is not FCISLineageClosureCertificateV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.INTERNAL_RELATION_FAILURE,
            "closure",
        )
    if closure.evaluation is not extraction.evaluation:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.LINEAGE_IDENTITY_MISMATCH,
            "evaluation",
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
    """Re-extract and rebuild the complete certificate from retained sources."""

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

    fresh_extraction = extract_source_bound_fee_occurrence_v1(certificate.extraction.evaluation)
    if type(fresh_extraction) is SourceBoundFeeOccurrenceRejectV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.EXTRACTION_REJECTED,
            fresh_extraction.code.value,
            *fresh_extraction.path,
        )
    if type(fresh_extraction) is not SourceBoundFeeOccurrenceV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.INTERNAL_RELATION_FAILURE,
            "fresh_extraction",
        )
    if fresh_extraction != certificate.extraction:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.LINEAGE_IDENTITY_MISMATCH,
            "extraction",
        )

    fresh_closure = build_fcis_lineage_closure_from_artifacts_v1(
        evaluation=certificate.extraction.evaluation,
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
    if type(fresh_closure) is not FCISLineageClosureCertificateV1:
        return _reject_v1(
            FCISSourceBoundLineageCodeV1.INTERNAL_RELATION_FAILURE,
            "fresh_closure",
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
