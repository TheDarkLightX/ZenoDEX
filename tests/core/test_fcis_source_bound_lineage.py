from __future__ import annotations

from inspect import signature

from src.core.fcis_commit_reference import (
    ReferenceCommitStatusV1,
    ReferenceCrashPointV1,
    _initial_reference_commit_store_v1,
    reference_commit_v1,
)
from src.core.fcis_lineage_closure import (
    FCISLineageClaimKeyV1,
    FCISLineageClaimSetV1,
    FCISLineageClaimV1,
)
from src.core.fcis_source_bound_lineage import (
    FCISSourceBoundLineageCertificateV1,
    FCISSourceBoundLineageCodeV1,
    FCISSourceBoundLineageRejectV1,
    derive_source_bound_fcis_lineage_v1,
    verify_source_bound_fcis_lineage_v1,
)
from tests.core.test_fcis_commit_bundle_derivation import _event_bundle
from tests.core.test_fcis_decision_derivation import _exact_inputs


def _certificate() -> FCISSourceBoundLineageCertificateV1:
    result = derive_source_bound_fcis_lineage_v1(**_exact_inputs())
    assert type(result) is FCISSourceBoundLineageCertificateV1
    return result


def test_source_bound_public_surface_has_no_fee_root_or_segment_argument() -> None:
    parameters = tuple(signature(derive_source_bound_fcis_lineage_v1).parameters)
    assert parameters == (
        "state_source",
        "settlement",
        "intents",
        "context",
        "budget",
        "axis_order",
    )


def test_source_bound_closure_retains_one_material_and_segment_lineage() -> None:
    certificate = _certificate()

    assert certificate.closure.evaluation.material == certificate.extraction.material
    assert certificate.closure.occurrence_segment is certificate.extraction.segment
    assert certificate.certificate_root == certificate.closure.closed_claims.root
    assert frozenset(claim.key for claim in certificate.closure.closed_claims.claims) == frozenset(
        FCISLineageClaimKeyV1
    )
    assert not hasattr(certificate.extraction, "post_state_root")
    assert verify_source_bound_fcis_lineage_v1(certificate) is None


def test_missing_claim_fails_even_when_attacker_rehashes_the_reduced_set() -> None:
    certificate = _certificate()
    incomplete = FCISLineageClaimSetV1(
        tuple(
            claim
            for claim in certificate.closure.closed_claims.claims
            if claim.key is not FCISLineageClaimKeyV1.PRE_STATE_ROOT
        )
    )
    object.__setattr__(certificate.closure, "closed_claims", incomplete)
    object.__setattr__(certificate.closure, "certificate_root", incomplete.root)

    result = verify_source_bound_fcis_lineage_v1(certificate)

    assert type(result) is FCISSourceBoundLineageRejectV1
    assert result.code is FCISSourceBoundLineageCodeV1.LINEAGE_IDENTITY_MISMATCH


def test_conflicting_digest_fails_after_coordinated_root_rehash() -> None:
    certificate = _certificate()
    claims = []
    for claim in certificate.closure.closed_claims.claims:
        if claim.key is FCISLineageClaimKeyV1.FEE_LINEAGE_STREAM_ROOT:
            claims.append(FCISLineageClaimV1(claim.key, "0x" + "ab" * 32))
        else:
            claims.append(claim)
    changed = FCISLineageClaimSetV1(tuple(claims))
    object.__setattr__(certificate.closure, "closed_claims", changed)
    object.__setattr__(certificate.closure, "certificate_root", changed.root)

    result = verify_source_bound_fcis_lineage_v1(certificate)

    assert type(result) is FCISSourceBoundLineageRejectV1
    assert result.code is FCISSourceBoundLineageCodeV1.LINEAGE_IDENTITY_MISMATCH


def test_actual_commit_port_exposes_only_pre_or_complete_post_at_crash_points() -> None:
    certificate = _certificate()
    bundle = certificate.closure.bundle
    pre_state = certificate.extraction.material.pre_state
    store = _initial_reference_commit_store_v1(pre_state)

    before = reference_commit_v1(
        store,
        bundle,
        ReferenceCrashPointV1.BEFORE_LINEARIZATION,
    )
    published = reference_commit_v1(store, bundle)
    after = reference_commit_v1(
        store,
        bundle,
        ReferenceCrashPointV1.AFTER_LINEARIZATION,
    )

    assert before.status is ReferenceCommitStatusV1.CRASHED_BEFORE_LINEARIZATION
    assert before.store == store
    assert published.status is ReferenceCommitStatusV1.PUBLISHED
    assert published.store.current_state == bundle.next_state
    assert len(published.store.publications) == 1
    assert after.status is ReferenceCommitStatusV1.CRASHED_AFTER_LINEARIZATION
    assert after.store == published.store


def test_store_current_mismatch_is_stale_and_publishes_nothing() -> None:
    certificate = _certificate()
    bundle = certificate.closure.bundle
    stale_store = _initial_reference_commit_store_v1(bundle.next_state)

    result = reference_commit_v1(stale_store, bundle)

    assert result.status is ReferenceCommitStatusV1.STALE
    assert result.store == stale_store
    assert result.store.publications == ()


def test_crossed_outbox_is_rejected_by_the_actual_commit_port() -> None:
    certificate = _certificate()
    foreign = _event_bundle()
    bundle = certificate.closure.bundle
    object.__setattr__(bundle, "outbox_plan", foreign.outbox_plan)
    store = _initial_reference_commit_store_v1(certificate.extraction.material.pre_state)

    result = reference_commit_v1(store, bundle)

    assert result.status is ReferenceCommitStatusV1.INVALID
    assert result.store == store
    assert result.store.publications == ()
