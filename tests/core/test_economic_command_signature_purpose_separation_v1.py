"""Real signatures bind purpose-selecting registry state; evidence roots are fixtures."""

from dataclasses import replace

import pytest
from py_ecc.bls import G2Basic

from src.core.economic_command_authentication_v1 import (
    _authenticate_isolated_economic_command_intent_v1,
    _isolated_economic_command_authentication_message_bytes_v1,
    authenticate_economic_command_intent_v1,
    economic_command_authentication_message_bytes_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierRegistryV1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierSelectionPurposeV1 as Purpose,
)
from src.core.global_settlement_types_v1 import ReleaseStatusV1
from tests.core.test_economic_command_signature_verifier_purpose_v1 import (
    _bind,
    _release,
    _with_registry,
)
from tests.integration.test_economic_command_bls_signature_verifier_v1 import _signed_fixture


def _shadow(release, **changes):
    return _release(
        release, status=ReleaseStatusV1.SHADOW, accepts_new_authentications=False, **changes
    )


def test_same_release_cannot_simultaneously_select_shadow_and_production():
    release = _signed_fixture()[3]
    shadow = _shadow(release)
    assert shadow.release_id == release.release_id
    assert shadow.status is not release.status
    for rows in ((shadow, release), (release, shadow)):
        with pytest.raises(ValueError, match="sorted and unique"):
            EconomicCommandSignatureVerifierRegistryV1(rows)


@pytest.mark.parametrize("target_isolated", (False, True))
def test_status_transition_does_not_reuse_a_signature_for_the_same_release(target_isolated):
    fixture, artifact, manifest, release = _signed_fixture()
    shadow = _shadow(release)
    isolated = _with_registry(fixture, EconomicCommandSignatureVerifierRegistryV1((shadow,)))
    production_message = economic_command_authentication_message_bytes_v1(
        fixture.candidate, fixture.authorization
    )
    isolated_message = _isolated_economic_command_authentication_message_bytes_v1(
        isolated.candidate, isolated.authorization
    )
    assert shadow.release_id == release.release_id
    assert isolated.signature_verifier_registry.registry_root != (
        fixture.signature_verifier_registry.registry_root
    )
    assert isolated_message != production_message
    target, selected, message, other, purpose, authenticate = (
        (
            isolated,
            shadow,
            isolated_message,
            production_message,
            Purpose.ISOLATED_QUALIFICATION,
            _authenticate_isolated_economic_command_intent_v1,
        )
        if target_isolated
        else (
            fixture,
            release,
            production_message,
            isolated_message,
            Purpose.PRODUCTION_NEW,
            authenticate_economic_command_intent_v1,
        )
    )
    bound = _bind((target, artifact, manifest, selected), selection_purpose=purpose)
    signed = replace(
        target.candidate,
        envelope=replace(target.envelope, signature_bytes=G2Basic.Sign(25, message)),
    )
    assert authenticate(signed, bound).selection_purpose is purpose
    wrong = replace(
        signed, envelope=replace(signed.envelope, signature_bytes=G2Basic.Sign(25, other))
    )
    with pytest.raises(ValueError, match="signature rejected"):
        authenticate(wrong, bound)


def test_two_purposes_in_one_profile_sign_different_release_bound_messages():
    fixture, _, manifest, release = _signed_fixture()
    # Distinct source evidence creates a different content-derived release ID.
    shadow_manifest = replace(manifest, source_root="0x" + "ad" * 32)
    shadow = _shadow(
        release,
        source_root=shadow_manifest.source_root,
        evidence_manifest_root=shadow_manifest.manifest_root,
    )
    registry = EconomicCommandSignatureVerifierRegistryV1(
        tuple(sorted((release, shadow), key=lambda row: row.key))
    )
    common = _with_registry(fixture, registry)
    production = economic_command_authentication_message_bytes_v1(
        common.candidate, common.authorization
    )
    isolated = _isolated_economic_command_authentication_message_bytes_v1(
        common.candidate, common.authorization
    )
    assert registry.release_for_new_authentication(release.signature_algorithm) == release
    assert (
        registry.release_for(release.signature_algorithm, Purpose.ISOLATED_QUALIFICATION) == shadow
    )
    assert production != isolated
    key = G2Basic.SkToPk(25)  # Public deterministic fixture scalar.
    for message, other in ((production, isolated), (isolated, production)):
        signature = G2Basic.Sign(25, message)
        assert G2Basic.Verify(key, message, signature)
        assert not G2Basic.Verify(key, other, signature)
