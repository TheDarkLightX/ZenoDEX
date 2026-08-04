"""Adversarial tests for the policy-bound J07 writer-admission context."""

from __future__ import annotations

from dataclasses import replace
from hashlib import sha256

import pytest

from experiments.fcis_m6_j07_authority_switch_check import build_f06_token, build_gate
from src.core.fcis_m6_j07_authority_switch import (
    J07RejectCodeV1,
    J07SwitchSuccessV1,
    J07WriterRejectV1,
    issue_writer_token_v2,
    switch_authority_v1,
)
from src.core.fcis_m6_j07_writer_admission_v2 import (
    FCIS_M6_J07_WRITER_ADMISSION_CONTEXT_SCHEMA_V2,
    J07WriterAdmissionContextV2,
    J07WriterAdmissionError,
    J07WriterAdmissionRejectCodeV2,
    J07WriterAdmissionRejectV2,
    verify_j07_writer_admission_context_v2,
    writer_admission_context_body_v2,
    writer_admission_context_root_v2,
)
from src.core.fcis_m6_j07_writer_token_v3 import (
    FCIS_M6_J07_WRITER_TOKEN_SCHEMA_V3,
    J07WriterAcceptedV3,
    J07WriterTokenV3,
    authorize_writer_v3,
    issue_writer_token_v3,
    writer_token_body_v3,
    writer_token_root_v3,
)
from src.core.fcis_m6_writer_profile_eligibility_v1 import (
    WriterProfileEligibilityReceiptV1,
    build_writer_profile_eligibility_claim_v1,
    verify_writer_profile_eligibility_v1,
)


def _digest(label: str) -> str:
    return sha256(label.encode("ascii")).hexdigest()


def _switch() -> J07SwitchSuccessV1:
    reopened, genesis, migration_token, verifier = build_f06_token()
    result = switch_authority_v1(
        build_gate(migration_token),
        reopened,
        genesis=genesis,
        migration_token=migration_token,
        verifier_adapter=verifier,
        current_epoch=3,
    )
    assert type(result) is J07SwitchSuccessV1
    return result


class _AdmissionVerifier:
    def __init__(self, decision: object = True) -> None:
        self.decision = decision
        self.kwargs: dict[str, object] | None = None

    def verify_j07_writer_admission_context(
        self,
        **kwargs: object,
    ) -> object:
        self.kwargs = dict(kwargs)
        return self.decision


class _EligibilityVerifier:
    def verify_writer_profile_eligibility(
        self,
        _claim: object,
        **_kwargs: object,
    ) -> object:
        return True


def _admission(
    switched: J07SwitchSuccessV1,
    *,
    promotion_subject_root: str | None = None,
    source_schema_root: str | None = None,
    policy_root: str | None = None,
    verifier_profile_root: str | None = None,
) -> J07WriterAdmissionContextV2:
    result = verify_j07_writer_admission_context_v2(
        authority_context=switched.post_context,
        promotion_subject_root=promotion_subject_root or _digest("promotion-subject"),
        source_schema_root=source_schema_root or _digest("source-schema"),
        eligibility_policy_root=policy_root or _digest("eligibility-policy"),
        eligibility_verifier_profile_root=(
            verifier_profile_root or _digest("eligibility-verifier")
        ),
        verification_evidence_root=_digest("writer-admission-evidence"),
        verifier_adapter=_AdmissionVerifier(),
    )
    assert type(result) is J07WriterAdmissionContextV2
    return result


def _eligibility(
    switched: J07SwitchSuccessV1,
    *,
    promotion_subject_root: str | None = None,
    source_schema_root: str | None = None,
    policy_root: str | None = None,
    verifier_profile_root: str | None = None,
) -> WriterProfileEligibilityReceiptV1:
    context = switched.post_context
    claim = build_writer_profile_eligibility_claim_v1(
        promotion_subject_root=promotion_subject_root or _digest("promotion-subject"),
        source_schema_root=source_schema_root or _digest("source-schema"),
        source_receipt_root=_digest("source-receipt"),
        source_binding_root=_digest("source-binding"),
        writer_profile_root=context.target_profile_root,
        authority_context_root=context.context_root,
        current_state_root=context.current_state_root,
        deployment_config_root=context.deployment_config_root,
        authority_epoch=context.epoch_index,
        authority_state_root=context.authority_state_root,
        expected_head_root=context.current_head_root,
        expected_snapshot_root=context.current_snapshot_root,
        eligibility_policy_root=policy_root or _digest("eligibility-policy"),
    )
    result = verify_writer_profile_eligibility_v1(
        claim=claim,
        verifier_profile_root=verifier_profile_root or _digest("eligibility-verifier"),
        verification_evidence_root=_digest(f"eligibility-evidence/{claim.claim_root}"),
        verifier_adapter=_EligibilityVerifier(),
    )
    assert type(result) is WriterProfileEligibilityReceiptV1
    return result


def test_v2_issue_path_is_closed_after_policy_context_is_required() -> None:
    switched = _switch()
    rejected = issue_writer_token_v2(switched.post_context, _eligibility(switched))
    assert type(rejected) is J07WriterRejectV1
    assert rejected.code is J07RejectCodeV1.WRITER_ADMISSION_CONTEXT_REQUIRED


def test_policy_bound_context_issues_and_uses_v3_token() -> None:
    switched = _switch()
    admission = _admission(switched)
    eligibility = _eligibility(switched)
    token = issue_writer_token_v3(switched.post_context, admission, eligibility)
    assert type(token) is J07WriterTokenV3
    assert writer_admission_context_root_v2(admission) == admission.admission_context_root
    assert writer_admission_context_body_v2(admission)["schema"] == (
        FCIS_M6_J07_WRITER_ADMISSION_CONTEXT_SCHEMA_V2
    )
    assert writer_token_root_v3(token) == token.token_root
    assert writer_token_body_v3(token)["schema"] == FCIS_M6_J07_WRITER_TOKEN_SCHEMA_V3
    accepted = authorize_writer_v3(
        switched.post_context,
        admission,
        token,
        eligibility,
    )
    assert type(accepted) is J07WriterAcceptedV3
    assert accepted.admission_context_root == admission.admission_context_root
    assert accepted.eligibility_verifier_profile_root == admission.eligibility_verifier_profile_root


def test_admission_verifier_receives_the_complete_current_authority_context() -> None:
    switched = _switch()
    context = switched.post_context
    verifier = _AdmissionVerifier()
    result = verify_j07_writer_admission_context_v2(
        authority_context=context,
        promotion_subject_root=_digest("promotion-subject"),
        source_schema_root=_digest("source-schema"),
        eligibility_policy_root=_digest("eligibility-policy"),
        eligibility_verifier_profile_root=_digest("eligibility-verifier"),
        verification_evidence_root=_digest("writer-admission-evidence"),
        verifier_adapter=verifier,
    )
    assert type(result) is J07WriterAdmissionContextV2
    assert verifier.kwargs == {
        "expected_authority_context_root": context.context_root,
        "expected_current_state_root": context.current_state_root,
        "expected_deployment_config_root": context.deployment_config_root,
        "expected_authority_epoch": context.epoch_index,
        "expected_authority_state_root": context.authority_state_root,
        "expected_head_root": context.current_head_root,
        "expected_snapshot_root": context.current_snapshot_root,
        "expected_promotion_subject_root": _digest("promotion-subject"),
        "expected_source_schema_root": _digest("source-schema"),
        "expected_eligibility_policy_root": _digest("eligibility-policy"),
        "expected_eligibility_verifier_profile_root": _digest("eligibility-verifier"),
        "expected_verification_evidence_root": _digest("writer-admission-evidence"),
    }


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("promotion_subject_root", _digest("foreign-promotion")),
        ("source_schema_root", _digest("foreign-source-schema")),
        ("policy_root", _digest("foreign-policy")),
        ("verifier_profile_root", _digest("foreign-verifier")),
    ),
)
def test_crossed_eligibility_cannot_issue_v3_token(field: str, value: str) -> None:
    switched = _switch()
    admission = _admission(switched)
    eligibility = _eligibility(switched, **{field: value})
    rejected = issue_writer_token_v3(switched.post_context, admission, eligibility)
    assert type(rejected) is J07WriterAdmissionRejectV2
    assert rejected.code is J07WriterAdmissionRejectCodeV2.ELIGIBILITY_CONTEXT_MISMATCH


def test_admission_context_constructor_is_verifier_owned() -> None:
    switched = _switch()
    with pytest.raises(J07WriterAdmissionError, match="verifier-owned"):
        replace(_admission(switched))


def test_writer_token_constructor_is_verifier_owned() -> None:
    switched = _switch()
    admission = _admission(switched)
    token = issue_writer_token_v3(switched.post_context, admission, _eligibility(switched))
    assert type(token) is J07WriterTokenV3
    with pytest.raises(J07WriterAdmissionError, match="verifier-owned"):
        replace(token)


def test_mutated_admission_context_rejects_at_point_of_use() -> None:
    switched = _switch()
    admission = _admission(switched)
    eligibility = _eligibility(switched)
    token = issue_writer_token_v3(switched.post_context, admission, eligibility)
    assert type(token) is J07WriterTokenV3
    object.__setattr__(admission, "eligibility_policy_root", _digest("mutated-policy"))
    rejected = authorize_writer_v3(
        switched.post_context,
        admission,
        token,
        eligibility,
    )
    assert type(rejected) is J07WriterAdmissionRejectV2
    assert rejected.code is J07WriterAdmissionRejectCodeV2.ADMISSION_CONTEXT_REJECTED


@pytest.mark.parametrize(
    "field",
    (
        "authority_context_root",
        "admission_context_root",
        "eligibility_receipt_root",
        "promotion_subject_root",
        "source_schema_root",
        "eligibility_policy_root",
        "eligibility_verifier_profile_root",
        "writer_profile_root",
        "authority_epoch_index",
        "authority_state_root",
        "expected_head_root",
        "expected_snapshot_root",
        "migration_token_root",
        "token_root",
    ),
)
def test_every_mutated_token_coordinate_rejects_at_point_of_use(field: str) -> None:
    switched = _switch()
    admission = _admission(switched)
    eligibility = _eligibility(switched)
    token = issue_writer_token_v3(switched.post_context, admission, eligibility)
    assert type(token) is J07WriterTokenV3
    replacement: object = (
        token.authority_epoch_index + 1
        if field == "authority_epoch_index"
        else _digest(f"mutated-token/{field}")
    )
    object.__setattr__(token, field, replacement)
    rejected = authorize_writer_v3(
        switched.post_context,
        admission,
        token,
        eligibility,
    )
    assert type(rejected) is J07WriterAdmissionRejectV2
    assert rejected.code is J07WriterAdmissionRejectCodeV2.TOKEN_REJECTED


def test_token_cannot_move_to_a_second_admission_context() -> None:
    switched = _switch()
    first = _admission(switched)
    eligibility = _eligibility(switched)
    token = issue_writer_token_v3(switched.post_context, first, eligibility)
    assert type(token) is J07WriterTokenV3
    second_result = verify_j07_writer_admission_context_v2(
        authority_context=switched.post_context,
        promotion_subject_root=first.promotion_subject_root,
        source_schema_root=first.source_schema_root,
        eligibility_policy_root=first.eligibility_policy_root,
        eligibility_verifier_profile_root=first.eligibility_verifier_profile_root,
        verification_evidence_root=_digest("second-admission-evidence"),
        verifier_adapter=_AdmissionVerifier(),
    )
    assert type(second_result) is J07WriterAdmissionContextV2
    rejected = authorize_writer_v3(
        switched.post_context,
        second_result,
        token,
        eligibility,
    )
    assert type(rejected) is J07WriterAdmissionRejectV2
    assert rejected.code is J07WriterAdmissionRejectCodeV2.STALE_CONTEXT


def test_admission_verifier_requires_exact_true() -> None:
    switched = _switch()
    result = verify_j07_writer_admission_context_v2(
        authority_context=switched.post_context,
        promotion_subject_root=_digest("promotion-subject"),
        source_schema_root=_digest("source-schema"),
        eligibility_policy_root=_digest("eligibility-policy"),
        eligibility_verifier_profile_root=_digest("eligibility-verifier"),
        verification_evidence_root=_digest("writer-admission-evidence"),
        verifier_adapter=_AdmissionVerifier(1),
    )
    assert type(result) is J07WriterAdmissionRejectV2
    assert result.code is J07WriterAdmissionRejectCodeV2.EXTERNAL_VERIFIER_REJECTED
