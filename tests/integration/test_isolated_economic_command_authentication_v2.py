"""V2 signatures through owned inputs and the fixed sealed BLS factory.

Most cases use a sealed-file protocol fixture with independent py_ecc checking.
The explicitly configured native case executes Rust. Profile and evidence roots
remain synthetic and confer no release or publication qualification.
"""

from __future__ import annotations

import hashlib
import inspect
import json
import os
from dataclasses import replace
from pathlib import Path

import pytest
from eth_typing import BLSPubkey, BLSSignature
from py_ecc.bls import G2Basic

import src.integration.economic_command_authentication_v2 as authentication
from src.core.asset_transfer_types_v2 import ASSET_TRANSFER_COMMAND_KIND_V2, AssetTransferCommandV2
from src.core.economic_command_authentication_types_v2 import (
    EconomicCommandAuthenticationCandidateV2,
    EconomicCommandIntentV2,
)
from src.core.economic_command_authentication_v2 import (
    ECONOMIC_COMMAND_AUTHENTICATION_MESSAGE_SCHEMA_ROOT_V2,
    prepare_isolated_economic_command_authentication_v2,
)
from src.core.economic_command_authorization_registry_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    EconomicCommandAuthorizationRegistryV1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierRegistryV1,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_primitives_v2 import canonical_economic_command_body_bytes_v2
from src.core.global_settlement_types_v1 import EconomicPolicyRegistryV1, ProfileStatusV1
from src.integration import global_receipt_verifier_v1 as receipt_transport
from src.integration import sealed_bls_command_verifier_deployment_v1 as deployment
from src.integration import sealed_bls_command_verifier_v1 as sealed
from tests.core.test_economic_command_authentication_v1 import (
    _bound_verifier,
    _fixture,
    _rebuild_profile,
    _RecordingVerifierV1,
    _root,
)
from tests.integration.test_sealed_bls_command_verifier_deployment_v1 import (
    _isolated_test_manifest,
    _isolated_test_release,
)

_SECRET = 25  # Public deterministic test scalar, never a deployed secret.
_ARTIFACT = b"\x7fELFprotocol-fixture-not-executable"
_NATIVE_SHA256 = "597f1e56fcca8f00bc94805cf020ca0e6f2779ded3b1944d1d699231f55b0eee"


def _signed_case(artifact: bytes = _ARTIFACT):
    base = _fixture()
    public_key = "0x" + G2Basic.SkToPk(_SECRET).hex()
    manifest = replace(
        _isolated_test_manifest(artifact),
        message_schema_root=ECONOMIC_COMMAND_AUTHENTICATION_MESSAGE_SCHEMA_ROOT_V2,
    )
    release = _isolated_test_release(manifest)
    verifier_registry = EconomicCommandSignatureVerifierRegistryV1((release,))
    authorization = replace(base.authorization, signer_public_key=public_key)
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
            for row in base.policy_registry.bindings
        )
    )
    profile = _rebuild_profile(base.profile, policy_registry.registry_root)
    command = AssetTransferCommandV2(
        ASSET_TRANSFER_COMMAND_KIND_V2, "USD", "alice", "bob", 30, 2, _root(72)
    )
    intent = EconomicCommandIntentV2(
        base.intent.chain_id,
        base.intent.deployment_root,
        profile.profile_id,
        command.command_kind,
        command.command_body_hash,
        base.intent.route_release_id,
        base.intent.subject_id,
        base.intent.grant_root,
        base.intent.nonce,
        (),
        base.intent.valid_from_height,
        base.intent.valid_through_height,
    )
    envelope = replace(
        base.envelope,
        command_body_bytes=canonical_economic_command_body_bytes_v2(command.command_kind, command),
        signer_public_key=public_key,
        signature_bytes=b"\0" * 96,
    )
    candidate = EconomicCommandAuthenticationCandidateV2(
        profile, policy_registry, authorization_registry, verifier_registry, intent, envelope
    )
    _, _, message = prepare_isolated_economic_command_authentication_v2(candidate)
    candidate = replace(
        candidate,
        envelope=replace(envelope, signature_bytes=G2Basic.Sign(_SECRET, message)),
    )
    occurrence = EconomicCommandOccurrenceV2(
        intent.chain_id,
        intent.deployment_root,
        11,
        2,
        3,
        intent.command_kind,
        intent.command_body_hash,
        intent.route_release_id,
        intent.subject_id,
        intent.grant_root,
        intent.nonce,
        intent.profile_root,
        _root(2),
        (),
    )
    return candidate, occurrence, manifest, message


def _run(case, artifact_path: Path):
    candidate, occurrence, manifest, _ = case
    return authentication.verify_isolated_economic_command_occurrence_v2(
        candidate,
        occurrence,
        signature_artifact_path=artifact_path,
        signature_evidence_manifest=manifest,
        signature_timeout_ms=5_000,
    )


@pytest.fixture
def protocol_case(monkeypatch: pytest.MonkeyPatch, tmp_path: Path):
    case = _signed_case()
    path = tmp_path / "protocol-fixture"
    path.write_bytes(_ARTIFACT)
    requests: list[bytes] = []

    def exchange(descriptor: int, request: bytes, timeout_ms: int):
        assert os.pread(descriptor, len(_ARTIFACT), 0) == _ARTIFACT
        assert timeout_ms == 5_000
        assert request[:8] == b"ZDXBLSV1"
        message = request[156:]
        assert int.from_bytes(request[152:156], "little") == len(message)
        requests.append(request)
        valid = G2Basic.Verify(BLSPubkey(request[8:56]), message, BLSSignature(request[56:152]))
        prefix = b"ZDXBOKV1" if valid else b"ZDXBNOV1"
        return prefix + hashlib.sha256(request).digest(), b"", 0

    monkeypatch.setattr(sealed, "_invoke_v1", exchange)
    return case, path, requests


def test_genuine_v2_signature_uses_exact_prepared_message_and_no_authority_result(protocol_case):
    case, path, requests = protocol_case

    result = _run(case, path)

    assert result is None
    assert len(requests) == 1
    assert requests[0][156:] == case[3]


@pytest.mark.parametrize("kind", ("foreign_key", "message_prehash", "v1_domain", "malformed"))
def test_signature_for_another_key_or_message_never_authenticates(protocol_case, kind):
    case, path, requests = protocol_case
    candidate, occurrence, manifest, message = case
    signature: bytes
    if kind == "foreign_key":
        signature = G2Basic.Sign(_SECRET + 1, message)
    elif kind == "message_prehash":
        signature = G2Basic.Sign(_SECRET, hashlib.sha256(message).digest())
    elif kind == "v1_domain":
        signature = G2Basic.Sign(
            _SECRET,
            message.replace(
                b"economic-command-intent-authentication-message-v2:v2",
                b"economic-command-intent-authentication-message-v1:v1",
                1,
            ),
        )
    else:
        signature = b"\0" * 96
    rejected = replace(candidate, envelope=replace(candidate.envelope, signature_bytes=signature))

    with pytest.raises(ValueError, match="command authentication signature rejected"):
        _run((rejected, occurrence, manifest, message), path)

    assert len(requests) == 1


def test_forged_always_true_bound_handle_is_not_an_input(protocol_case):
    case, path, requests = protocol_case
    fake_backend = _RecordingVerifierV1(True)
    fake_bound = _bound_verifier(_fixture(), fake_backend)
    candidate, occurrence, manifest, _ = case
    parameters = inspect.signature(
        authentication.verify_isolated_economic_command_occurrence_v2
    ).parameters
    assert set(parameters) == {
        "candidate",
        "occurrence",
        "signature_artifact_path",
        "signature_evidence_manifest",
        "signature_timeout_ms",
    }
    with pytest.raises(TypeError, match="unexpected keyword argument 'signature_verifier'"):
        authentication.verify_isolated_economic_command_occurrence_v2(  # type: ignore[call-arg]
            candidate,
            occurrence,
            signature_artifact_path=path,
            signature_evidence_manifest=manifest,
            signature_timeout_ms=5_000,
            signature_verifier=fake_bound,
        )
    assert fake_backend.calls == requests == []


def test_mallory_signature_cannot_substitute_an_ungoverned_alice_authorization(
    protocol_case, monkeypatch
):
    case, path, requests = protocol_case
    candidate, occurrence, manifest, message = case
    mallory_key = G2Basic.SkToPk(_SECRET + 1)
    authorization = replace(
        candidate.authorization_registry.authorizations[0],
        signer_public_key="0x" + mallory_key.hex(),
    )
    foreign_registry = EconomicCommandAuthorizationRegistryV1((authorization,))
    prefix, body_bytes = message.split(b"\0", 1)
    body = json.loads(body_bytes)
    body["authorization_registry_root"] = foreign_registry.registry_root
    body["authorization_id"] = authorization.authorization_id
    body["signer_public_key"] = authorization.signer_public_key
    foreign_message = (
        prefix + b"\0" + json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    )
    signature = G2Basic.Sign(_SECRET + 1, foreign_message)
    assert G2Basic.Verify(mallory_key, foreign_message, signature) is True
    forged = replace(
        candidate,
        authorization_registry=foreign_registry,
        envelope=replace(
            candidate.envelope,
            signer_public_key=authorization.signer_public_key,
            signature_bytes=signature,
        ),
    )

    def forbidden_read(_):
        pytest.fail("ungoverned signer registry reached artifact acquisition")

    monkeypatch.setattr(deployment, "_read_regular_artifact_bytes_v1", forbidden_read)
    with pytest.raises(ValueError, match="authorization registry is not profile governed"):
        _run((forged, occurrence, manifest, foreign_message), path)
    assert requests == []


@pytest.mark.parametrize(
    "field,value",
    (
        ("chain_id", "foreign-chain"),
        ("deployment_root", _root(81)),
        ("profile_root", _root(82)),
        ("command_kind", "foreign-command"),
        ("command_body_hash", _root(83)),
        ("route_release_id", _root(84)),
        ("subject_id", "mallory"),
        ("grant_root", _root(85)),
        ("nonce", 10),
        ("consumed_object_ids", ("foreign-object",)),
    ),
)
def test_signed_occurrence_substitution_rejects_before_artifact_access(
    protocol_case, monkeypatch, field, value
):
    case, path, requests = protocol_case
    candidate, occurrence, manifest, message = case

    def forbidden_read(_):
        pytest.fail("mismatched signed occurrence reached artifact acquisition")

    monkeypatch.setattr(deployment, "_read_regular_artifact_bytes_v1", forbidden_read)
    with pytest.raises(ValueError, match="occurrence .* mismatch"):
        _run((candidate, replace(occurrence, **{field: value}), manifest, message), path)
    assert requests == []


@pytest.mark.parametrize("height,accepted", ((9, False), (10, True), (12, True), (13, False)))
def test_sequenced_height_has_the_exact_signed_interval(protocol_case, height, accepted):
    case, path, requests = protocol_case
    candidate, occurrence, manifest, message = case
    selected = (candidate, replace(occurrence, height=height), manifest, message)

    if accepted:
        assert _run(selected, path) is None
        assert len(requests) == 1
    else:
        with pytest.raises(ValueError, match="height.*validity"):
            _run(selected, path)
        assert requests == []


def test_unsigned_sequencer_coordinates_still_need_separate_admission(protocol_case):
    case, path, requests = protocol_case
    candidate, occurrence, manifest, message = case
    resequenced = replace(occurrence, tx_index=20, op_index=30, pre_state_root=_root(86))

    assert _run((candidate, resequenced, manifest, message), path) is None
    assert requests[0][156:] == message


@pytest.mark.parametrize("kind", ("artifact", "manifest"))
def test_measurement_and_manifest_failures_never_launch_verification(protocol_case, kind):
    case, path, requests = protocol_case
    candidate, occurrence, manifest, message = case
    if kind == "artifact":
        path.write_bytes(_ARTIFACT + b"-substituted")
    else:
        manifest = replace(manifest, source_root=_root(87))

    with pytest.raises(ValueError, match="(implementation|manifest)"):
        _run((candidate, occurrence, manifest, message), path)
    assert requests == []


def test_transport_timeout_propagates_without_authentication(protocol_case, monkeypatch):
    case, path, requests = protocol_case

    def timeout(*_):
        raise receipt_transport.GlobalReceiptVerifierErrorV1(
            receipt_transport.GlobalReceiptVerifierRejectV1.PROCESS_TIMEOUT
        )

    monkeypatch.setattr(sealed, "_invoke_v1", timeout)
    with pytest.raises(sealed.SealedBlsCommandVerifierErrorV1) as error:
        _run(case, path)
    assert error.value.reason is sealed.SealedBlsCommandVerifierRejectV1.PROCESS_TIMEOUT
    assert requests == []


def test_unavailable_artifact_cannot_authenticate(protocol_case):
    case, path, requests = protocol_case
    path.unlink()

    with pytest.raises(ValueError, match="regular non-symlink file"):
        _run(case, path)
    assert requests == []


def test_retry_reacquires_and_rechecks_revocation_instead_of_caching_success(
    protocol_case, monkeypatch
):
    case, path, requests = protocol_case
    candidate, occurrence, manifest, message = case
    reads: list[Path] = []
    original_read = deployment._read_regular_artifact_bytes_v1

    def read(artifact_path):
        reads.append(artifact_path)
        return original_read(artifact_path)

    monkeypatch.setattr(deployment, "_read_regular_artifact_bytes_v1", read)
    assert _run(case, path) is None
    assert _run(case, path) is None
    revoked = replace(candidate, profile=replace(candidate.profile, status=ProfileStatusV1.REVOKED))
    assert revoked.profile.profile_id == candidate.profile.profile_id
    with pytest.raises(ValueError, match="ACTIVE profile"):
        _run((revoked, occurrence, manifest, message), path)
    assert reads == [path, path]
    assert len(requests) == 2


def test_artifact_acquisition_cannot_change_the_owned_signed_inputs(protocol_case, monkeypatch):
    case, path, requests = protocol_case
    candidate, occurrence, _, message = case
    original_read = deployment._read_regular_artifact_bytes_v1

    def mutate_originals(artifact_path):
        object.__setattr__(candidate.intent, "nonce", 100)
        object.__setattr__(candidate.envelope, "signature_bytes", b"\0" * 96)
        object.__setattr__(occurrence, "subject_id", "mallory")
        return original_read(artifact_path)

    monkeypatch.setattr(deployment, "_read_regular_artifact_bytes_v1", mutate_originals)
    assert _run(case, path) is None
    assert requests[0][156:] == message
    assert candidate.intent.nonce == 100
    assert occurrence.subject_id == "mallory"


def test_native_sealed_verifier_accepts_v2_and_rejects_a_foreign_signature():
    configured = os.environ.get("ZENODEX_BLS_VERIFIER_TEST_BINARY")
    if configured is None:
        pytest.skip("explicit checksum-qualified native BLS verifier is required")
    path = Path(configured)
    artifact = path.read_bytes()
    assert hashlib.sha256(artifact).hexdigest() == _NATIVE_SHA256
    case = _signed_case(artifact)

    assert _run(case, path) is None
    candidate, occurrence, manifest, message = case
    foreign = replace(
        candidate,
        envelope=replace(candidate.envelope, signature_bytes=G2Basic.Sign(_SECRET + 1, message)),
    )
    with pytest.raises(ValueError, match="command authentication signature rejected"):
        _run((foreign, occurrence, manifest, message), path)
