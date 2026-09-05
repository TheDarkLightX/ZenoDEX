"""Purpose isolation uses real BLS and explicitly synthetic policy evidence."""

from dataclasses import fields, replace

import pytest
from py_ecc.bls import G2Basic

from src.core import economic_command_authentication_witness_v1 as witnesses
from src.core import economic_command_signature_verifier_capability_v1 as capabilities
from src.core.economic_command_authentication_v1 import (
    _authenticate_isolated_economic_command_intent_v1,
    _isolated_economic_command_authentication_message_bytes_v1,
    authenticate_economic_command_intent_v1,
    bind_authenticated_intent_to_occurrence_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1,
    EconomicCommandSignatureVerifierRegistryV1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierSelectionPurposeV1 as Purpose,
)
from src.core.global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    ProfileStatusV1,
    ReleaseStatusV1,
)
from src.integration.economic_command_bls_signature_verifier_v1 import (
    bind_deployed_bls_economic_command_signature_verifier_v1,
)
from tests.core.test_economic_command_authentication_v1 import _rebuild_profile
from tests.integration.test_economic_command_bls_signature_verifier_v1 import _signed_fixture


def _release(release, **changes):
    arguments = {
        field.name: getattr(release, field.name)
        for field in fields(release)
        if field.name != "release_id"
    }
    return type(release).build(**{**arguments, **changes})


def _with_registry(fixture, registry):
    policy = EconomicPolicyRegistryV1(
        tuple(
            replace(row, policy_root=registry.registry_root)
            if row.policy_kind == "command_signature_verifier_registry"
            else row
            for row in fixture.policy_registry.bindings
        )
    )
    profile = _rebuild_profile(fixture.profile, policy.registry_root)
    return replace(
        fixture,
        policy_registry=policy,
        profile=profile,
        signature_verifier_registry=registry,
        intent=replace(fixture.intent, profile_root=profile.profile_id),
        occurrence=replace(fixture.occurrence, profile_root=profile.profile_id),
    )


@pytest.fixture(scope="module")
def isolated():
    fixture, artifact, manifest, release = _signed_fixture()
    artifacts = tuple(
        row
        for row in manifest.evidence_artifacts
        if row.status in REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1
    )
    manifest = replace(manifest, evidence_artifacts=artifacts)
    release = _release(
        release,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_authentications=False,
        evidence_statuses=tuple(row.status for row in artifacts),
        evidence_manifest_root=manifest.manifest_root,
    )
    fixture = _with_registry(fixture, EconomicCommandSignatureVerifierRegistryV1((release,)))
    message = _isolated_economic_command_authentication_message_bytes_v1(
        fixture.candidate, fixture.authorization
    )
    fixture = replace(
        fixture, envelope=replace(fixture.envelope, signature_bytes=G2Basic.Sign(25, message))
    )
    return fixture, artifact, manifest, release


def _bind(subject, **changes):
    fixture, artifact, manifest, release = subject
    return bind_deployed_bls_economic_command_signature_verifier_v1(
        **{
            "artifact_path": artifact,
            "release": release,
            "evidence_manifest": manifest,
            "deployment_root": fixture.intent.deployment_root,
            "profile_root": fixture.profile.profile_id,
            "selection_purpose": Purpose.ISOLATED_QUALIFICATION,
            **changes,
        }
    )


def test_genuine_isolated_authentication_preserves_shadow_status_and_purpose(isolated):
    fixture, _, _, release = isolated
    bound = _bind(isolated)
    authenticated = _authenticate_isolated_economic_command_intent_v1(fixture.candidate, bound)
    command = bind_authenticated_intent_to_occurrence_v1(authenticated, fixture.occurrence)
    assert (
        bound.selection_purpose
        is authenticated.selection_purpose
        is command.selection_purpose
        is Purpose.ISOLATED_QUALIFICATION
    )
    assert release.status is ReleaseStatusV1.SHADOW
    assert release.accepts_new_authentications is False
    assert {row.value for row in release.evidence_statuses} == {
        "SPECIFIED",
        "IMPLEMENTED",
        "TESTED",
        "SOURCE_PINNED",
        "TOOLCHAIN_PINNED",
    }
    assert command.occurrence_id == fixture.occurrence.occurrence_id


def test_production_authentication_refuses_an_isolated_bound_verifier(isolated):
    fixture = isolated[0]
    with pytest.raises(ValueError, match="purpose"):
        authenticate_economic_command_intent_v1(fixture.candidate, _bind(isolated))
    with pytest.raises(ValueError, match="purpose"):
        _bind(isolated).require_binding(
            release_id=isolated[3].release_id,
            deployment_root=fixture.intent.deployment_root,
            profile_root=fixture.profile.profile_id,
        )


def test_isolated_entry_refuses_production_bound_verifier():
    subject = _signed_fixture()
    fixture, artifact, manifest, release = subject
    bound = bind_deployed_bls_economic_command_signature_verifier_v1(
        artifact_path=artifact,
        release=release,
        evidence_manifest=manifest,
        deployment_root=fixture.intent.deployment_root,
        profile_root=fixture.profile.profile_id,
    )
    with pytest.raises(ValueError, match="purpose"):
        _authenticate_isolated_economic_command_intent_v1(fixture.candidate, bound)


@pytest.mark.parametrize("purpose", ("ISOLATED_QUALIFICATION", None, True, 1))
def test_unknown_or_non_enum_purpose_fails_closed(isolated, purpose):
    with pytest.raises(TypeError, match="purpose"):
        _bind(isolated, selection_purpose=purpose)


def test_default_production_binding_does_not_select_shadow_release(isolated):
    with pytest.raises(ValueError, match="active"):
        _bind(isolated, selection_purpose=Purpose.PRODUCTION_NEW)


@pytest.mark.parametrize(
    "missing",
    sorted(REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1, key=lambda row: row.value),
)
def test_each_isolated_evidence_requirement_is_independently_enforced(isolated, missing):
    fixture, artifact, manifest, release = isolated
    manifest = replace(
        manifest,
        evidence_artifacts=tuple(
            row for row in manifest.evidence_artifacts if row.status is not missing
        ),
    )
    release = _release(
        release,
        evidence_statuses=tuple(row.status for row in manifest.evidence_artifacts),
        evidence_manifest_root=manifest.manifest_root,
    )
    with pytest.raises(ValueError, match="baseline evidence"):
        _bind((fixture, artifact, manifest, release))


@pytest.mark.parametrize(
    "status", (ReleaseStatusV1.RETIRED, ReleaseStatusV1.DRAIN_ONLY, ReleaseStatusV1.REVOKED)
)
def test_revoked_or_draining_release_cannot_enter_isolation(isolated, status):
    fixture, artifact, manifest, release = isolated
    changed = _release(release, status=status)
    with pytest.raises(ValueError, match="shadow"):
        _bind((fixture, artifact, manifest, changed))


@pytest.mark.parametrize("scope", ("deployment_root", "profile_root"))
def test_foreign_scope_bound_verifier_cannot_authenticate_isolated_candidate(isolated, scope):
    bound = _bind(isolated, **{scope: "0x" + "fe" * 32})
    with pytest.raises(ValueError, match="binding mismatch"):
        _authenticate_isolated_economic_command_intent_v1(isolated[0].candidate, bound)


def test_isolated_authentication_retains_profile_and_policy_authorization(isolated):
    fixture = isolated[0]
    bound = _bind(isolated)
    for candidate in (
        replace(fixture.candidate, profile=replace(fixture.profile, status=ProfileStatusV1.SHADOW)),
        replace(fixture.candidate, policy_registry=EconomicPolicyRegistryV1(())),
    ):
        with pytest.raises(ValueError):
            _authenticate_isolated_economic_command_intent_v1(candidate, bound)


def test_old_bound_capability_does_not_override_new_profile_revocation(isolated):
    fixture, _, _, release = isolated
    bound = _bind(isolated)
    revoked = _with_registry(
        fixture,
        EconomicCommandSignatureVerifierRegistryV1(
            (_release(release, status=ReleaseStatusV1.RETIRED),)
        ),
    )
    with pytest.raises(ValueError, match="shadow"):
        _authenticate_isolated_economic_command_intent_v1(revoked.candidate, bound)


def test_changing_only_purpose_changes_each_opaque_binding_identity(isolated):
    fixture = isolated[0]
    bound = _bind(isolated)
    intent = _authenticate_isolated_economic_command_intent_v1(fixture.candidate, bound)
    command = bind_authenticated_intent_to_occurrence_v1(intent, fixture.occurrence)
    # Diagnostic hash comparison only: never register the altered authority.
    for witness, authority, derive in (
        (
            bound,
            capabilities._bound_verifier_authority_v1(bound),
            capabilities._bound_verifier_binding_root_v1,
        ),
        (
            intent,
            witnesses._authenticated_intent_authority_v1(intent),
            witnesses._authenticated_intent_binding_root_v1,
        ),
        (
            command,
            witnesses._authenticated_command_authority_v1(command),
            witnesses._authenticated_command_binding_root_v1,
        ),
    ):
        legacy = replace(authority, selection_purpose=Purpose.PRODUCTION_NEW)
        assert derive(legacy) != witness.binding_root
