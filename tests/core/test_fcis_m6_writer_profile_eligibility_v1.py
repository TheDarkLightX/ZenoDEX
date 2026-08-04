"""Focused tests for substrate-neutral writer-profile eligibility."""

from __future__ import annotations

from dataclasses import replace
from hashlib import sha256

import pytest

from src.core.fcis_m6_writer_profile_eligibility_v1 import (
    WriterProfileEligibilityClaimV1,
    WriterProfileEligibilityError,
    WriterProfileEligibilityReceiptV1,
    WriterProfileEligibilityRejectCodeV1,
    WriterProfileEligibilityRejectV1,
    build_writer_profile_eligibility_claim_v1,
    is_verified_writer_profile_eligibility_receipt_v1,
    verify_writer_profile_eligibility_v1,
)


def _root(label: str) -> str:
    return sha256(label.encode("ascii")).hexdigest()


def _claim(**overrides: object) -> WriterProfileEligibilityClaimV1:
    values: dict[str, object] = {
        "promotion_subject_root": _root("promotion-subject"),
        "source_schema_root": _root("source-schema"),
        "source_receipt_root": _root("source-receipt"),
        "source_binding_root": _root("source-binding"),
        "writer_profile_root": _root("writer-profile"),
        "authority_context_root": _root("authority-context"),
        "current_state_root": _root("current-state"),
        "deployment_config_root": _root("deployment-config"),
        "authority_epoch": 7,
        "authority_state_root": _root("authority-state"),
        "expected_head_root": _root("head"),
        "expected_snapshot_root": _root("snapshot"),
        "eligibility_policy_root": _root("eligibility-policy"),
    }
    values.update(overrides)
    return build_writer_profile_eligibility_claim_v1(**values)  # type: ignore[arg-type]


class _Verifier:
    def __init__(self, decision: object = True) -> None:
        self.decision = decision
        self.claim: object | None = None
        self.kwargs: dict[str, object] | None = None

    def verify_writer_profile_eligibility(
        self,
        claim: object,
        **kwargs: object,
    ) -> object:
        self.claim = claim
        self.kwargs = dict(kwargs)
        return self.decision


def _verify(
    claim: WriterProfileEligibilityClaimV1,
    *,
    verifier: _Verifier | None = None,
) -> WriterProfileEligibilityReceiptV1 | WriterProfileEligibilityRejectV1:
    return verify_writer_profile_eligibility_v1(
        claim=claim,
        verifier_profile_root=_root("verifier-profile"),
        verification_evidence_root=_root("verification-evidence"),
        verifier_adapter=verifier or _Verifier(),
    )


def test_public_claim_is_canonical_data_and_not_a_receipt() -> None:
    claim = _claim()
    assert type(claim) is WriterProfileEligibilityClaimV1
    assert not is_verified_writer_profile_eligibility_receipt_v1(claim)
    changed = _claim(source_binding_root=_root("changed-binding"))
    assert changed.claim_root != claim.claim_root


def test_selected_verifier_mints_one_bound_opaque_receipt() -> None:
    claim = _claim()
    verifier = _Verifier()
    result = _verify(claim, verifier=verifier)
    assert type(result) is WriterProfileEligibilityReceiptV1
    assert is_verified_writer_profile_eligibility_receipt_v1(result)
    assert verifier.claim is claim
    assert verifier.kwargs is not None
    assert verifier.kwargs["expected_claim_root"] == claim.claim_root
    assert verifier.kwargs["expected_promotion_subject_root"] == claim.promotion_subject_root
    assert verifier.kwargs["expected_source_binding_root"] == claim.source_binding_root
    assert verifier.kwargs["expected_authority_context_root"] == claim.authority_context_root
    with pytest.raises(TypeError, match="selected verifier"):
        replace(result)


def test_verifier_must_return_exact_true() -> None:
    result = _verify(_claim(), verifier=_Verifier(1))
    assert type(result) is WriterProfileEligibilityRejectV1
    assert result.code is WriterProfileEligibilityRejectCodeV1.EXTERNAL_VERIFIER_REJECTED


def test_mutated_registered_receipt_rejects_at_point_of_use() -> None:
    result = _verify(_claim())
    assert type(result) is WriterProfileEligibilityReceiptV1
    object.__setattr__(result, "verification_evidence_root", _root("crossed-evidence"))
    assert not is_verified_writer_profile_eligibility_receipt_v1(result)


def test_boolean_authority_epoch_is_rejected() -> None:
    with pytest.raises(WriterProfileEligibilityError, match="exact u64"):
        _claim(authority_epoch=True)


def test_changed_claim_field_cannot_reuse_old_claim_root() -> None:
    claim = _claim()
    with pytest.raises(WriterProfileEligibilityError, match="does not rederive"):
        replace(claim, current_state_root=_root("foreign-state"))
