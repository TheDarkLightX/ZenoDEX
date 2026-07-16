from __future__ import annotations

import copy
import hashlib
import json
import pickle
from dataclasses import FrozenInstanceError, fields, replace
from typing import Any, cast

import pytest

from src.integration._zrpf_spot_v7_release_selection_envelope_v1 import (
    SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
    SpotV7ReleaseSelectionEnvelopeRejectV1,
    parse_exact_spot_v7_release_selection_envelope_v1,
    spot_v7_release_selection_envelope_payload_hash_v1,
)
from src.integration.zeno_ledger_signature import (
    SUPPORTED_PAYLOAD_KINDS_V0,
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zrpf_spot_v7_authenticated_release_selection_v1 import (
    SpotV7ReleaseSelectionAuthenticationErrorV1,
    SpotV7ReleaseSelectionExternalTrustPinsV1,
    _AuthenticatedReleaseSelectionDurableArtifactsV2,
    _AuthenticatedSpotV7ReleaseSelectionV1,
    authenticate_spot_v7_release_selection_v1,
    build_spot_v7_release_selection_envelope_v1,
)
from src.state.canonical import canonical_json_bytes
from tests.test_zrpf_spot_v7_governed_release_selection_store_v1 import (
    _candidate_lineage,
    _checked_candidate,
    _position_bytes,
    _selector_bytes,
)
from tools import zrpf_spot_v7_governed_release_selection_store_v1 as store_module
from tools import zrpf_spot_v7_governed_release_selector_input_v1 as selector_module
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate_module

PRIVATE_KEY_0 = "0x" + (1).to_bytes(32, "big").hex()
PRIVATE_KEY_1 = "0x" + (2).to_bytes(32, "big").hex()
EVALUATION_EPOCH = 0x0102_0304_0506
REGISTRY_REVISION = 7
REGISTRY_ACTIVATION_EPOCH = EVALUATION_EPOCH - 10


def _registry(
    *,
    registry_id: str = "zrpf-spot-v7-release-selection-signers",
    threshold: int = 2,
) -> dict[str, Any]:
    return build_signer_registry_v0(
        registry_id=registry_id,
        payload_kind=SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
        threshold=threshold,
        signers=[
            {
                "key_id": "release-selection-key-0",
                "public_key": bls_public_key_hex_from_private_key_v0(PRIVATE_KEY_0),
                "signer_id": "release-selection-signer-0",
                "status": "active",
                "weight": 1,
            },
            {
                "key_id": "release-selection-key-1",
                "public_key": bls_public_key_hex_from_private_key_v0(PRIVATE_KEY_1),
                "signer_id": "release-selection-signer-1",
                "status": "active",
                "weight": 1,
            },
        ],
    )


def _genesis_cursor() -> store_module.SpotV7ReleaseSelectionCursorV1:
    return store_module.SpotV7ReleaseSelectionCursorV1(
        database_revision=0,
        state_root=store_module.GENESIS_SELECTION_STATE_ROOT_V1,
        last_evaluation_epoch=None,
        current_candidate_id=None,
        current_candidate_sha256=None,
        current_release_revision=None,
        current_select_input_id=None,
        current_scope_id=None,
        current_revoked=False,
        current_revocation_record_id=None,
    )


def _selection_material() -> tuple[
    candidate_module.SpotV7ReleaseCandidateManifestV1,
    bytes,
    bytes,
    bytes,
]:
    candidate = _checked_candidate(
        revision=1,
        parent_candidate_id=None,
        variant=0,
        activation_epoch=EVALUATION_EPOCH,
        expiration_epoch=EVALUATION_EPOCH + 1_000,
    )
    revocation_registry_root = _position_bytes(180)
    selector_bytes, selector_id = _selector_bytes(
        operation=selector_module.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=_genesis_cursor(),
        evaluation_epoch=EVALUATION_EPOCH,
        nonce_index=200,
        revocation_registry_root=revocation_registry_root,
    )
    return candidate, selector_bytes, selector_id, revocation_registry_root


def _pins(
    candidate: candidate_module.SpotV7ReleaseCandidateManifestV1,
    *,
    registry: dict[str, Any],
    revocation_registry_root: bytes,
    registry_revocation_epoch: int | None = None,
    minimum_target_release_revision: int = 1,
) -> SpotV7ReleaseSelectionExternalTrustPinsV1:
    document = cast(dict[str, Any], json.loads(candidate.canonical_bytes))
    scope = cast(dict[str, Any], document["scope"])
    lineage = _candidate_lineage(candidate)
    return SpotV7ReleaseSelectionExternalTrustPinsV1(
        application_id=scope["application_id"],
        chain_id=scope["chain_id"],
        domain_id=scope["domain_id"],
        release_profile=scope["release_profile"],
        trusted_evaluation_epoch=EVALUATION_EPOCH,
        expected_database_revision=0,
        expected_current_candidate_id=None,
        expected_current_select_input_id=None,
        minimum_target_release_revision=minimum_target_release_revision,
        rollback_policy_root=bytes.fromhex(lineage["rollback_policy_root"]),
        revocation_policy_root=bytes.fromhex(lineage["revocation_policy_root"]),
        revocation_registry_root=revocation_registry_root,
        signer_registry_id=str(registry["registry_id"]),
        expected_signer_registry_hash=str(registry["registry_hash"]),
        signer_registry_revision=REGISTRY_REVISION,
        signer_registry_activation_epoch=REGISTRY_ACTIVATION_EPOCH,
        signer_registry_revocation_epoch=registry_revocation_epoch,
        expected_quorum_threshold=int(registry["threshold"]),
    )


def _envelope_and_signatures() -> tuple[
    bytes,
    tuple[dict[str, Any], ...],
    candidate_module.SpotV7ReleaseCandidateManifestV1,
    bytes,
    bytes,
    SpotV7ReleaseSelectionExternalTrustPinsV1,
    dict[str, Any],
]:
    candidate, selector_bytes, selector_id, revocation_registry_root = _selection_material()
    registry = _registry()
    pins = _pins(
        candidate,
        registry=registry,
        revocation_registry_root=revocation_registry_root,
    )
    envelope = build_spot_v7_release_selection_envelope_v1(
        selector_input_bytes=selector_bytes,
        expected_selector_input_id=selector_id,
        candidate_bytes=candidate.canonical_bytes,
        external_trust_pins=pins,
        trusted_signer_registry=registry,
    )
    payload_hash = spot_v7_release_selection_envelope_payload_hash_v1(envelope)
    signatures = (
        build_bls_signed_artifact_envelope_v0(
            payload_kind=SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id="release-selection-signer-0",
            key_id="release-selection-key-0",
            private_key_hex=PRIVATE_KEY_0,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id="release-selection-signer-1",
            key_id="release-selection-key-1",
            private_key_hex=PRIVATE_KEY_1,
        ),
    )
    return (
        envelope,
        signatures,
        candidate,
        selector_bytes,
        selector_id,
        pins,
        registry,
    )


def _authenticate(
    envelope: bytes,
    signatures: object,
    candidate: candidate_module.SpotV7ReleaseCandidateManifestV1,
    selector_bytes: bytes,
    selector_id: bytes,
    pins: SpotV7ReleaseSelectionExternalTrustPinsV1,
    registry: object,
) -> _AuthenticatedSpotV7ReleaseSelectionV1:
    return authenticate_spot_v7_release_selection_v1(
        envelope,
        selector_input_bytes=selector_bytes,
        expected_selector_input_id=selector_id,
        candidate_bytes=candidate.canonical_bytes,
        external_trust_pins=pins,
        trusted_signer_registry=registry,
        signature_envelopes=signatures,
    )


def _authenticated_result() -> _AuthenticatedSpotV7ReleaseSelectionV1:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, registry = (
        _envelope_and_signatures()
    )
    return _authenticate(
        envelope,
        signatures,
        candidate,
        selector_bytes,
        selector_id,
        pins,
        registry,
    )


def test_exact_quorum_authentication_mints_private_authority_neutral_capability() -> None:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, registry = (
        _envelope_and_signatures()
    )
    result = _authenticate(
        envelope,
        signatures,
        candidate,
        selector_bytes,
        selector_id,
        pins,
        registry,
    )
    parsed = parse_exact_spot_v7_release_selection_envelope_v1(envelope)

    assert type(result) is _AuthenticatedSpotV7ReleaseSelectionV1
    assert result._has_private_seal() is True
    assert result.selector_input_id == parsed.selector_input_id
    assert result.selected_candidate_id == parsed.candidate_id
    assert result.selected_candidate_sha256 == parsed.candidate_sha256
    assert result.release_revision == 1
    assert result.evaluation_epoch == EVALUATION_EPOCH
    assert result.signer_registry_hash == registry["registry_hash"]
    assert result.signer_registry_revision == REGISTRY_REVISION
    assert result.quorum_threshold == 2
    assert result.signature_quorum_authenticated is True
    assert result.exact_selector_and_candidate_bound is True
    assert result.external_registry_pin_matched is True
    assert result.release_governed_registry_pin_authenticated is False
    assert result.durable_selection_committed is False
    assert result.hostile_same_interpreter_resistance_established is False
    assert result.candidate_selected is False
    assert result.release_authority is False
    assert result.runtime_authority is False
    assert result.settlement_authority is False
    assert result.production_authority is False
    assert len(result.evidence_sha256) == 64


def test_signature_order_canonicalizes_retained_evidence() -> None:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, registry = (
        _envelope_and_signatures()
    )
    forward = _authenticate(
        envelope,
        signatures,
        candidate,
        selector_bytes,
        selector_id,
        pins,
        registry,
    )
    reverse = _authenticate(
        envelope,
        tuple(reversed(signatures)),
        candidate,
        selector_bytes,
        selector_id,
        pins,
        registry,
    )

    assert forward.evidence_sha256 == reverse.evidence_sha256
    assert forward.quorum_report_hash == reverse.quorum_report_hash


@pytest.mark.parametrize("signatures", [(), []])
def test_missing_quorum_rejects(signatures: object) -> None:
    envelope, _, candidate, selector_bytes, selector_id, pins, registry = _envelope_and_signatures()

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SIGNATURE_SET_SIZE",
    ):
        _authenticate(
            envelope,
            signatures,
            candidate,
            selector_bytes,
            selector_id,
            pins,
            registry,
        )


def test_registry_and_signature_inputs_reject_overdeep_in_memory_shapes() -> None:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, registry = (
        _envelope_and_signatures()
    )
    overdeep_registry = dict(registry)
    overdeep_registry["uncommitted"] = {"a": {"b": {"c": "value"}}}
    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SIGNER_REGISTRY_SIZE",
    ):
        build_spot_v7_release_selection_envelope_v1(
            selector_input_bytes=selector_bytes,
            expected_selector_input_id=selector_id,
            candidate_bytes=candidate.canonical_bytes,
            external_trust_pins=pins,
            trusted_signer_registry=overdeep_registry,
        )

    overdeep_signature = dict(signatures[0])
    overdeep_signature["uncommitted"] = {"nested": "value"}
    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SIGNATURE_ENVELOPE_SIZE",
    ):
        _authenticate(
            envelope,
            (overdeep_signature, signatures[1]),
            candidate,
            selector_bytes,
            selector_id,
            pins,
            registry,
        )


def test_insufficient_quorum_rejects() -> None:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, registry = (
        _envelope_and_signatures()
    )

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SIGNATURE_QUORUM_INVALID.*threshold not met",
    ):
        _authenticate(
            envelope,
            signatures[:1],
            candidate,
            selector_bytes,
            selector_id,
            pins,
            registry,
        )


def test_registry_substitution_rejects_against_independent_expected_hash() -> None:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, _ = (
        _envelope_and_signatures()
    )
    substituted = _registry(threshold=1)

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SIGNER_REGISTRY_HASH_MISMATCH",
    ):
        _authenticate(
            envelope,
            signatures,
            candidate,
            selector_bytes,
            selector_id,
            pins,
            substituted,
        )


def test_selector_and_candidate_tampering_reject_before_quorum() -> None:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, registry = (
        _envelope_and_signatures()
    )
    tampered_selector = selector_bytes[:-1] + bytes([selector_bytes[-1] ^ 1])
    tampered_candidate = candidate.canonical_bytes.replace(b"zenodex", b"zenodey", 1)

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SELECTOR_INPUT_INVALID",
    ):
        _authenticate(
            envelope,
            signatures,
            candidate,
            tampered_selector,
            selector_id,
            pins,
            registry,
        )
    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="RELEASE_CANDIDATE_INVALID",
    ):
        authenticate_spot_v7_release_selection_v1(
            envelope,
            selector_input_bytes=selector_bytes,
            expected_selector_input_id=selector_id,
            candidate_bytes=tampered_candidate,
            external_trust_pins=pins,
            trusted_signer_registry=registry,
            signature_envelopes=signatures,
        )


def test_signed_envelope_candidate_tampering_rejects_exact_recomposition() -> None:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, registry = (
        _envelope_and_signatures()
    )
    document = cast(dict[str, Any], json.loads(envelope))
    selection = cast(dict[str, Any], document["selection"])
    selection["candidate_sha256"] = "0x" + _position_bytes(249).hex()
    tampered = canonical_json_bytes(document)

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SELECTION_ENVELOPE_BINDING_MISMATCH",
    ):
        _authenticate(
            tampered,
            signatures,
            candidate,
            selector_bytes,
            selector_id,
            pins,
            registry,
        )


def test_rollback_floor_and_registry_revocation_reject() -> None:
    _, _, candidate, selector_bytes, selector_id, pins, registry = _envelope_and_signatures()
    rollback_pins = replace(pins, minimum_target_release_revision=2)
    revoked_pins = replace(
        pins,
        signer_registry_revocation_epoch=EVALUATION_EPOCH,
    )

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="RELEASE_REVISION_ROLLBACK",
    ):
        build_spot_v7_release_selection_envelope_v1(
            selector_input_bytes=selector_bytes,
            expected_selector_input_id=selector_id,
            candidate_bytes=candidate.canonical_bytes,
            external_trust_pins=rollback_pins,
            trusted_signer_registry=registry,
        )
    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SIGNER_REGISTRY_REVOKED",
    ):
        build_spot_v7_release_selection_envelope_v1(
            selector_input_bytes=selector_bytes,
            expected_selector_input_id=selector_id,
            candidate_bytes=candidate.canonical_bytes,
            external_trust_pins=revoked_pins,
            trusted_signer_registry=registry,
        )


def test_candidate_revocation_state_is_exact_and_cannot_be_signed_as_active() -> None:
    envelope, _, _, _, _, _, _ = _envelope_and_signatures()
    document = cast(dict[str, Any], json.loads(envelope))
    selection = cast(dict[str, Any], document["selection"])
    selection["candidate_revocation_state"] = "revoked"

    with pytest.raises(
        SpotV7ReleaseSelectionEnvelopeRejectV1,
        match="CANDIDATE_REVOCATION_STATE_INVALID",
    ):
        parse_exact_spot_v7_release_selection_envelope_v1(canonical_json_bytes(document))


def test_registry_revision_and_quorum_policy_are_signed_exactly() -> None:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, registry = (
        _envelope_and_signatures()
    )
    revision_pins = replace(pins, signer_registry_revision=REGISTRY_REVISION + 1)
    threshold_pins = replace(pins, expected_quorum_threshold=1)

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SELECTION_ENVELOPE_BINDING_MISMATCH",
    ):
        _authenticate(
            envelope,
            signatures,
            candidate,
            selector_bytes,
            selector_id,
            revision_pins,
            registry,
        )
    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SIGNER_REGISTRY_THRESHOLD_MISMATCH",
    ):
        _authenticate(
            envelope,
            signatures,
            candidate,
            selector_bytes,
            selector_id,
            threshold_pins,
            registry,
        )


def test_unknown_and_duplicate_envelope_fields_reject() -> None:
    envelope, _, _, _, _, _, _ = _envelope_and_signatures()
    document = cast(dict[str, Any], json.loads(envelope))
    document["verified"] = True
    unknown = canonical_json_bytes(document)
    duplicate = envelope.replace(
        b'{"schema":',
        b'{"schema":"forged","schema":',
        1,
    )

    with pytest.raises(
        SpotV7ReleaseSelectionEnvelopeRejectV1,
        match="FIELD_SET_MISMATCH",
    ):
        parse_exact_spot_v7_release_selection_envelope_v1(unknown)
    with pytest.raises(
        SpotV7ReleaseSelectionEnvelopeRejectV1,
        match="DUPLICATE_JSON_KEY",
    ):
        parse_exact_spot_v7_release_selection_envelope_v1(duplicate)


def test_plain_boolean_mapping_and_nominal_object_cannot_bypass_authentication() -> None:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, registry = (
        _envelope_and_signatures()
    )

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="SELECTION_ENVELOPE_INVALID.*ENVELOPE_TYPE",
    ):
        authenticate_spot_v7_release_selection_v1(
            cast(Any, True),
            selector_input_bytes=selector_bytes,
            expected_selector_input_id=selector_id,
            candidate_bytes=candidate.canonical_bytes,
            external_trust_pins=pins,
            trusted_signer_registry=registry,
            signature_envelopes=signatures,
        )
    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="EXTERNAL_TRUST_PINS_REQUIRED",
    ):
        authenticate_spot_v7_release_selection_v1(
            envelope,
            selector_input_bytes=selector_bytes,
            expected_selector_input_id=selector_id,
            candidate_bytes=candidate.canonical_bytes,
            external_trust_pins=cast(Any, {"verified": True}),
            trusted_signer_registry=registry,
            signature_envelopes=signatures,
        )
    with pytest.raises(TypeError, match="verified construction"):
        _AuthenticatedSpotV7ReleaseSelectionV1()


def test_authenticated_capability_is_noncopyable_nonserializable_and_immutable() -> None:
    envelope, signatures, candidate, selector_bytes, selector_id, pins, registry = (
        _envelope_and_signatures()
    )
    result = _authenticate(
        envelope,
        signatures,
        candidate,
        selector_bytes,
        selector_id,
        pins,
        registry,
    )

    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(result)
    with pytest.raises(TypeError, match="cannot be deep-copied"):
        copy.deepcopy(result)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(result)
    with pytest.raises(TypeError, match="cannot be mutated"):
        result._candidate_id = _position_bytes(250)


def test_durable_accessor_returns_fresh_private_bytes_only_artifacts() -> None:
    result = _authenticated_result()

    first = result._artifacts_for_durable_store_v2()
    second = result._artifacts_for_durable_store_v2()

    assert type(first) is _AuthenticatedReleaseSelectionDurableArtifactsV2
    assert first is not second
    assert first == second
    assert {field.name for field in fields(first)} == {
        "authentication_evidence_bytes",
        "candidate_bytes",
        "envelope_bytes",
        "external_trust_pins_bytes",
        "quorum_report_bytes",
        "selector_input_bytes",
        "signature_envelopes_bytes",
        "signer_registry_bytes",
    }
    assert all(type(getattr(first, field.name)) is bytes for field in fields(first))
    assert first.authentication_evidence_bytes == result._evidence_bytes
    assert hashlib.sha256(first.candidate_bytes).digest() == result.selected_candidate_sha256
    assert json.loads(first.signer_registry_bytes)["registry_hash"] == (result.signer_registry_hash)
    assert json.loads(first.quorum_report_bytes)["quorum_report_hash"] == (
        result.quorum_report_hash
    )
    assert isinstance(json.loads(first.signature_envelopes_bytes), list)
    assert first.durable_selection_committed is False
    assert first.release_authority is False
    assert first.runtime_authority is False
    assert first.settlement_authority is False
    assert first.production_authority is False


def test_durable_artifacts_are_nonconstructible_noncopyable_and_frozen() -> None:
    artifacts = _authenticated_result()._artifacts_for_durable_store_v2()

    with pytest.raises(TypeError, match="revalidated construction"):
        _AuthenticatedReleaseSelectionDurableArtifactsV2()
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(artifacts)
    with pytest.raises(TypeError, match="cannot be deep-copied"):
        copy.deepcopy(artifacts)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(artifacts)
    with pytest.raises(FrozenInstanceError):
        artifacts.candidate_bytes = b"forged"  # type: ignore[misc]


def test_durable_accessor_rejects_retained_evidence_hash_mutation() -> None:
    result = _authenticated_result()
    object.__setattr__(result, "_evidence_bytes", result._evidence_bytes + b" ")

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="AUTHENTICATION_EVIDENCE_DRIFT",
    ):
        result._artifacts_for_durable_store_v2()


def test_durable_accessor_recomposes_envelope_from_exact_retained_parts() -> None:
    result = _authenticated_result()
    evidence = cast(dict[str, Any], json.loads(result._evidence_bytes))
    envelope = cast(
        dict[str, Any],
        json.loads(bytes.fromhex(evidence["release_selection_envelope_hex"])),
    )
    registry = cast(dict[str, Any], envelope["signer_registry"])
    registry["registry_revision"] += 1
    evidence["release_selection_envelope_hex"] = canonical_json_bytes(envelope).hex()
    tampered = canonical_json_bytes(evidence)
    object.__setattr__(result, "_evidence_bytes", tampered)
    object.__setattr__(result, "_evidence_sha256", hashlib.sha256(tampered).hexdigest())

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="RETAINED_ENVELOPE_RECOMPOSITION_MISMATCH",
    ):
        result._artifacts_for_durable_store_v2()


def test_durable_accessor_reverifies_retained_quorum_report() -> None:
    result = _authenticated_result()
    evidence = cast(dict[str, Any], json.loads(result._evidence_bytes))
    report = cast(dict[str, Any], evidence["signature_quorum_report"])
    report["accepted_weight"] += 1
    tampered = canonical_json_bytes(evidence)
    object.__setattr__(result, "_evidence_bytes", tampered)
    object.__setattr__(result, "_evidence_sha256", hashlib.sha256(tampered).hexdigest())

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="RETAINED_QUORUM_REPORT_MISMATCH",
    ):
        result._artifacts_for_durable_store_v2()


def test_durable_accessor_rejects_retained_capability_field_mutation() -> None:
    result = _authenticated_result()
    object.__setattr__(result, "_release_revision", result.release_revision + 1)

    with pytest.raises(
        SpotV7ReleaseSelectionAuthenticationErrorV1,
        match="AUTHENTICATED_CAPABILITY_FIELD_DRIFT",
    ):
        result._artifacts_for_durable_store_v2()


def test_release_selection_payload_kind_is_dedicated_and_allowlisted() -> None:
    assert SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1 in SUPPORTED_PAYLOAD_KINDS_V0
    assert SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1 != ("zrpf_spot_v7_operational_policy")


def test_external_trust_pins_remain_authority_neutral() -> None:
    _, _, candidate, _, _, pins, _ = _envelope_and_signatures()
    assert candidate.release_authority is False
    assert pins.release_governed_registry_pin_authenticated is False
    assert pins.release_authority is False
    assert pins.settlement_authority is False
    assert pins.production_authority is False
