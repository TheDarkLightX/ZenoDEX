from __future__ import annotations

import hashlib
import subprocess
import sys
from dataclasses import replace
from pathlib import Path

import pytest
from py_ecc.bls import G2Basic, G2MessageAugmentation, G2ProofOfPossession

from src.core.economic_command_authentication_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    EconomicCommandAuthorizationRegistryV1,
    authenticate_economic_command_intent_v1,
    bind_authenticated_intent_to_occurrence_v1,
    economic_command_authentication_message_bytes_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierRegistryV1,
)
from src.core.global_settlement_types_v1 import MAX_JOURNAL_BYTES_V1, EconomicPolicyRegistryV1
from src.integration import economic_command_bls_signature_verifier_v1 as bls_verifier
from tests.core.test_economic_command_authentication_v1 import (
    _fixture,
    _rebuild_profile,
    _root,
    _signature_verifier_manifest,
    _signature_verifier_release,
)

_ALGORITHM = "BLS12_381_G2_BASIC_V1"
_SECRET = 25  # Public deterministic test scalar; never a deployed key.
_MESSAGE = b"zenodex:economic-command-intent-authentication-message-v1:v1\0test"


class _StrSubclass(str):
    pass


class _BytesSubclass(bytes):
    pass


class _UnexpectedCryptoV1:
    def Verify(self, public_key, message, signature):
        raise AssertionError("malformed input reached cryptographic verification")


@pytest.fixture(scope="module")
def genuine_inputs():
    return {
        "signature_algorithm": _ALGORITHM,
        "signer_public_key": "0x" + G2Basic.SkToPk(_SECRET).hex(),
        "message_bytes": _MESSAGE,
        "signature_bytes": G2Basic.Sign(_SECRET, _MESSAGE),
    }


def _signed_fixture():
    """Reuse structural policy fixtures; their evidence roots are not attestations."""

    fixture = _fixture()
    public_key = "0x" + G2Basic.SkToPk(_SECRET).hex()
    artifact_path = Path(bls_verifier.__file__)
    manifest = replace(
        _signature_verifier_manifest(artifact_bytes=artifact_path.read_bytes()),
        max_public_key_bytes=98,
        max_signature_bytes=96,
    )
    release = _signature_verifier_release(manifest)
    verifier_registry = EconomicCommandSignatureVerifierRegistryV1((release,))
    authorization = replace(fixture.authorization, signer_public_key=public_key)
    authorization_registry = EconomicCommandAuthorizationRegistryV1((authorization,))
    policy_registry = EconomicPolicyRegistryV1(
        tuple(
            replace(
                row,
                policy_root=(
                    authorization_registry.registry_root
                    if row.policy_kind == ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1
                    else verifier_registry.registry_root
                ),
            )
            for row in fixture.policy_registry.bindings
        )
    )
    profile = _rebuild_profile(fixture.profile, policy_registry.registry_root)
    fixture = replace(
        fixture,
        profile=profile,
        policy_registry=policy_registry,
        authorization_registry=authorization_registry,
        signature_verifier_registry=verifier_registry,
        authorization=authorization,
        intent=replace(fixture.intent, profile_root=profile.profile_id),
        occurrence=replace(fixture.occurrence, profile_root=profile.profile_id),
        envelope=replace(
            fixture.envelope, signer_public_key=public_key, signature_bytes=b"\0" * 96
        ),
    )
    message = economic_command_authentication_message_bytes_v1(
        fixture.candidate, fixture.authorization
    )
    fixture = replace(
        fixture,
        envelope=replace(fixture.envelope, signature_bytes=G2Basic.Sign(_SECRET, message)),
    )
    return fixture, artifact_path, manifest, release


@pytest.fixture(scope="module")
def signed_fixture():
    return _signed_fixture()


def _bind(subject, **changes):
    fixture, artifact_path, manifest, release = subject
    arguments = {
        "artifact_path": artifact_path,
        "release": release,
        "evidence_manifest": manifest,
        "deployment_root": fixture.intent.deployment_root,
        "profile_root": fixture.intent.profile_root,
        **changes,
    }
    return bls_verifier.bind_deployed_bls_economic_command_signature_verifier_v1(**arguments)


def test_genuine_signature_accepts_without_granting_an_authentication_witness(genuine_inputs):
    backend = bls_verifier.make_bls_economic_command_signature_verifier_backend_v1()
    assert backend.verify_command_signature(**genuine_inputs) is True
    assert not hasattr(backend, "binding_root")
    with pytest.raises(AttributeError):
        object.__setattr__(backend, "replacement", object())


@pytest.mark.parametrize(
    "field,value",
    [
        ("signature_algorithm", "BLS12_381_G2_POP_V1"),
        ("signature_algorithm", None),
        ("signature_algorithm", _StrSubclass(_ALGORITHM)),
        ("signer_public_key", "0x" + "00" * 47),
        ("signer_public_key", "0x" + "00" * 49),
        ("signer_public_key", "0x" + "gg" * 48),
        ("signer_public_key", "0x" + "\ud800" * 96),
        ("signer_public_key", b"\0" * 48),
        ("signer_public_key", _StrSubclass("0x" + "00" * 48)),
        ("message_bytes", b""),
        ("message_bytes", b"m" * (MAX_JOURNAL_BYTES_V1 + 1)),
        ("message_bytes", bytearray(b"message")),
        ("message_bytes", _BytesSubclass(_MESSAGE)),
        ("signature_bytes", b"\0" * 95),
        ("signature_bytes", b"\0" * 97),
        ("signature_bytes", bytearray(b"\0" * 96)),
        ("signature_bytes", _BytesSubclass(b"\0" * 96)),
    ],
)
def test_malformed_exact_types_and_lengths_reject_before_crypto(
    genuine_inputs, field, value, monkeypatch
):
    backend = bls_verifier.make_bls_economic_command_signature_verifier_backend_v1()
    monkeypatch.setattr(bls_verifier, "_BLS_BACKEND_V1", _UnexpectedCryptoV1())
    assert backend.verify_command_signature(**{**genuine_inputs, field: value}) is False


@pytest.mark.parametrize("change", (str.upper, lambda value: value[2:], lambda value: " " + value))
def test_noncanonical_public_key_spellings_reject(genuine_inputs, change):
    backend = bls_verifier.make_bls_economic_command_signature_verifier_backend_v1()
    assert (
        backend.verify_command_signature(
            **{**genuine_inputs, "signer_public_key": change(genuine_inputs["signer_public_key"])}
        )
        is False
    )


@pytest.mark.parametrize(
    "field,value",
    [
        ("signer_public_key", "0x" + "00" * 48),
        ("signer_public_key", "0x" + "c0" + "00" * 47),
        ("signature_bytes", b"\0" * 96),
        ("signature_bytes", b"\xc0" + b"\0" * 95),
    ],
)
def test_invalid_curve_encodings_and_infinity_reject(genuine_inputs, field, value):
    backend = bls_verifier.make_bls_economic_command_signature_verifier_backend_v1()
    assert backend.verify_command_signature(**{**genuine_inputs, field: value}) is False


@pytest.mark.parametrize("length", (1, MAX_JOURNAL_BYTES_V1))
def test_message_ceiling_neighbors_have_genuine_positive_controls(length):
    message = b"m" * length
    backend = bls_verifier.make_bls_economic_command_signature_verifier_backend_v1()
    assert (
        backend.verify_command_signature(
            signature_algorithm=_ALGORITHM,
            signer_public_key="0x" + G2Basic.SkToPk(_SECRET).hex(),
            message_bytes=message,
            signature_bytes=G2Basic.Sign(_SECRET, message),
        )
        is True
    )


def test_foreign_key_and_wrong_message_reject_genuine_signature(genuine_inputs):
    backend = bls_verifier.make_bls_economic_command_signature_verifier_backend_v1()
    for change in (
        {"signer_public_key": "0x" + G2Basic.SkToPk(_SECRET + 1).hex()},
        {"message_bytes": _MESSAGE + b"different-context"},
    ):
        assert backend.verify_command_signature(**{**genuine_inputs, **change}) is False


@pytest.mark.parametrize("suite", (G2MessageAugmentation, G2ProofOfPossession))
def test_foreign_bls_ciphersuite_rejects_same_key_and_message(genuine_inputs, suite):
    backend = bls_verifier.make_bls_economic_command_signature_verifier_backend_v1()
    signature = suite.Sign(_SECRET, _MESSAGE)
    assert suite.Verify(G2Basic.SkToPk(_SECRET), _MESSAGE, signature) is True
    assert (
        backend.verify_command_signature(**{**genuine_inputs, "signature_bytes": signature})
        is False
    )


def test_given_raw_economic_intent_when_signed_then_core_authenticates_and_binds(signed_fixture):
    fixture, _, _, _ = signed_fixture
    bound = _bind(signed_fixture)
    authenticated = authenticate_economic_command_intent_v1(fixture.candidate, bound)
    command = bind_authenticated_intent_to_occurrence_v1(authenticated, fixture.occurrence)
    assert authenticated.intent == fixture.intent
    assert command.occurrence == fixture.occurrence


@pytest.mark.parametrize("legacy_form", ("sha256", "legacy_dex_domain"))
def test_extra_prehash_or_legacy_dex_domain_cannot_authenticate_economic_intent(
    signed_fixture, legacy_form
):
    fixture, _, _, _ = signed_fixture
    message = economic_command_authentication_message_bytes_v1(
        fixture.candidate, fixture.authorization
    )
    legacy = hashlib.sha256(message).digest()
    if legacy_form == "legacy_dex_domain":
        legacy = hashlib.sha256(b"zenodex:dex_intent_sig:legacy-chain:v1\0" + message).digest()
    envelope = replace(fixture.envelope, signature_bytes=G2Basic.Sign(_SECRET, legacy))
    candidate = replace(fixture.candidate, envelope=envelope)
    assert G2Basic.Verify(G2Basic.SkToPk(_SECRET), legacy, envelope.signature_bytes) is True
    with pytest.raises(ValueError, match="signature rejected"):
        authenticate_economic_command_intent_v1(candidate, _bind(signed_fixture))


@pytest.mark.parametrize("change", ({"chain_id": "foreign-chain"}, {"nonce": 10}))
def test_valid_structural_context_change_rejects_old_signature_without_input_change(
    signed_fixture, change
):
    fixture, _, _, _ = signed_fixture
    candidate = replace(fixture.candidate, intent=replace(fixture.intent, **change))
    baseline = (candidate.intent.intent_id, candidate.envelope.signature_bytes)
    with pytest.raises(ValueError, match="signature rejected"):
        authenticate_economic_command_intent_v1(candidate, _bind(signed_fixture))
    assert (candidate.intent.intent_id, candidate.envelope.signature_bytes) == baseline


def test_even_genuine_signature_does_not_authorize_an_unregistered_subject(signed_fixture):
    fixture, _, _, _ = signed_fixture
    candidate = replace(fixture.candidate, intent=replace(fixture.intent, subject_id="mallory"))
    message = economic_command_authentication_message_bytes_v1(candidate, fixture.authorization)
    signature = G2Basic.Sign(_SECRET, message)
    candidate = replace(candidate, envelope=replace(candidate.envelope, signature_bytes=signature))
    assert G2Basic.Verify(G2Basic.SkToPk(_SECRET), message, signature) is True
    with pytest.raises(ValueError, match="authorization"):
        authenticate_economic_command_intent_v1(candidate, _bind(signed_fixture))


@pytest.mark.parametrize("scope", ("deployment_root", "profile_root"))
def test_core_rejects_foreign_bound_scope_with_genuine_signature(signed_fixture, scope):
    fixture, _, _, _ = signed_fixture
    bound = _bind(signed_fixture, **{scope: _root(9001)})
    with pytest.raises(ValueError, match="binding mismatch"):
        authenticate_economic_command_intent_v1(fixture.candidate, bound)


def test_core_owns_occurrence_binding_after_genuine_authentication(signed_fixture):
    fixture, _, _, _ = signed_fixture
    authenticated = authenticate_economic_command_intent_v1(
        fixture.candidate, _bind(signed_fixture)
    )
    with pytest.raises(ValueError, match="occurrence nonce mismatch"):
        bind_authenticated_intent_to_occurrence_v1(
            authenticated, replace(fixture.occurrence, nonce=fixture.occurrence.nonce + 1)
        )


def test_concrete_binder_preserves_measured_artifact_and_manifest_checks(signed_fixture, tmp_path):
    _, source_path, manifest, _ = signed_fixture
    changed = tmp_path / "changed-artifact.py"
    changed.write_bytes(source_path.read_bytes() + b"\n")
    with pytest.raises(ValueError, match="measured implementation root mismatch"):
        _bind(signed_fixture, artifact_path=changed)
    with pytest.raises(ValueError, match="manifest root mismatch"):
        _bind(signed_fixture, evidence_manifest=replace(manifest, source_root=_root(9002)))


def test_concrete_binder_has_no_backend_injection_argument(signed_fixture):
    with pytest.raises(TypeError, match="unexpected keyword argument 'backend'"):
        _bind(signed_fixture, backend=object())


@pytest.mark.parametrize(
    "change,reason",
    (
        ({"signature_algorithm": "OTHER_ALGORITHM_V1"}, "algorithm mismatch"),
        ({"max_public_key_bytes": 97}, "ceilings are incompatible"),
        ({"max_signature_bytes": 95}, "ceilings are incompatible"),
    ),
)
def test_concrete_backend_rejects_incompatible_governed_release(signed_fixture, change, reason):
    manifest = replace(signed_fixture[2], **change)
    with pytest.raises(ValueError, match=reason):
        _bind(
            signed_fixture,
            evidence_manifest=manifest,
            release=_signature_verifier_release(manifest),
        )


def test_unavailable_backend_cannot_construct_or_use_verifier(
    genuine_inputs, signed_fixture, monkeypatch
):
    backend = bls_verifier.make_bls_economic_command_signature_verifier_backend_v1()
    monkeypatch.setattr(bls_verifier, "_BLS_BACKEND_V1", None)
    with pytest.raises(bls_verifier.EconomicCommandBlsBackendUnavailableErrorV1):
        bls_verifier.make_bls_economic_command_signature_verifier_backend_v1()
    with pytest.raises(bls_verifier.EconomicCommandBlsBackendUnavailableErrorV1):
        backend.verify_command_signature(**genuine_inputs)
    with pytest.raises(bls_verifier.EconomicCommandBlsBackendUnavailableErrorV1):
        _bind(signed_fixture)


@pytest.mark.parametrize("failure", ("ImportError", "RuntimeError"))
def test_import_absence_is_distinct_from_broken_backend_initialization(failure):
    script = f'''
import builtins
original = builtins.__import__
def failed_import(name, *args, **kwargs):
    if name == "py_ecc.bls":
        raise {failure}("injected backend initialization fault")
    return original(name, *args, **kwargs)
builtins.__import__ = failed_import
try:
    from src.integration import economic_command_bls_signature_verifier_v1 as module
except RuntimeError:
    if "{failure}" != "RuntimeError":
        raise
else:
    if "{failure}" != "ImportError":
        raise SystemExit("broken backend was concealed")
    try:
        module.make_bls_economic_command_signature_verifier_backend_v1()
    except module.EconomicCommandBlsBackendUnavailableErrorV1:
        pass
    else:
        raise SystemExit("missing backend was accepted")
'''
    result = subprocess.run(
        [sys.executable, "-B", "-c", script],
        cwd=Path(__file__).resolve().parents[2],
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    assert result.returncode == 0, result.stderr
