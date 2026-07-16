from __future__ import annotations

import copy
import hashlib
import json
import pickle
from dataclasses import FrozenInstanceError, fields, replace
from typing import Any, cast

import pytest

from src.integration._zrpf_spot_v7_release_revocation_envelope_v1 import (
    SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
    SpotV7ReleaseRevocationEnvelopeRejectV1,
    parse_exact_spot_v7_release_revocation_envelope_v1,
    spot_v7_release_revocation_envelope_payload_hash_v1,
)
from src.integration.zeno_ledger_signature import (
    SUPPORTED_PAYLOAD_KINDS_V0,
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zrpf_spot_v7_authenticated_release_revocation_v1 import (
    SpotV7ReleaseRevocationAuthenticationErrorV1,
    SpotV7ReleaseRevocationExternalTrustPinsV1,
    _AuthenticatedReleaseRevocationDurableArtifactsV1,
    _AuthenticatedSpotV7ReleaseRevocationV1,
    authenticate_spot_v7_release_revocation_v1,
    build_spot_v7_release_revocation_envelope_v1,
)
from src.state.canonical import canonical_json_bytes
from tests.test_zrpf_spot_v7_governed_release_selection_store_v1 import (
    _candidate_lineage,
    _checked_candidate,
    _position_bytes,
    _revocation_bytes,
    _selector_bytes,
)
from tools import zrpf_spot_v7_governed_release_selection_store_v1 as store_module
from tools import zrpf_spot_v7_governed_release_selector_input_v1 as selector_module
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate_module

PRIVATE_KEY_0 = "0x" + (1).to_bytes(32, "big").hex()
PRIVATE_KEY_1 = "0x" + (2).to_bytes(32, "big").hex()
EVALUATION_EPOCH = 0x0102_0304_0510
LAST_EVALUATION_EPOCH = EVALUATION_EPOCH - 1
REGISTRY_REVISION = 11
REGISTRY_ACTIVATION_EPOCH = EVALUATION_EPOCH - 100
RECORD_REVISION = 3
REASON_CODE = 0x1020_3040


def _registry() -> dict[str, Any]:
    return build_signer_registry_v0(
        registry_id="zrpf-spot-v7-release-revocation-signers",
        payload_kind=SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
        threshold=2,
        signers=[
            {
                "key_id": "release-revocation-key-0",
                "public_key": bls_public_key_hex_from_private_key_v0(PRIVATE_KEY_0),
                "signer_id": "release-revocation-signer-0",
                "status": "active",
                "weight": 1,
            },
            {
                "key_id": "release-revocation-key-1",
                "public_key": bls_public_key_hex_from_private_key_v0(PRIVATE_KEY_1),
                "signer_id": "release-revocation-signer-1",
                "status": "active",
                "weight": 1,
            },
        ],
    )


def _current_material(
    *,
    evaluation_epoch: int = EVALUATION_EPOCH,
    effective_epoch: int = EVALUATION_EPOCH,
) -> tuple[
    candidate_module.SpotV7ReleaseCandidateManifestV1,
    store_module.SpotV7ReleaseSelectionCursorV1,
    bytes,
    bytes,
    bytes,
    bytes,
]:
    candidate = _checked_candidate(
        revision=1,
        parent_candidate_id=None,
        variant=0,
        activation_epoch=EVALUATION_EPOCH - 1_000,
        expiration_epoch=EVALUATION_EPOCH + 1_000,
    )
    current_selector_id = _position_bytes(170)
    cursor = store_module.SpotV7ReleaseSelectionCursorV1(
        database_revision=1,
        state_root=_position_bytes(171),
        last_evaluation_epoch=LAST_EVALUATION_EPOCH,
        current_candidate_id=candidate.candidate_id,
        current_candidate_sha256=hashlib.sha256(candidate.canonical_bytes).digest(),
        current_release_revision=candidate.release_revision,
        current_select_input_id=current_selector_id,
        current_scope_id=_position_bytes(172),
        current_revoked=False,
        current_revocation_record_id=None,
    )
    registry_root = _position_bytes(180)
    record_bytes, record_id = _revocation_bytes(
        candidate=candidate,
        revocation_registry_root=registry_root,
        effective_epoch=effective_epoch,
        record_revision=RECORD_REVISION,
        nonce_index=240,
    )
    selector_bytes, selector_id = _selector_bytes(
        operation=selector_module.SelectorOperationV1.REVOKE,
        candidate=candidate,
        cursor=cursor,
        evaluation_epoch=evaluation_epoch,
        nonce_index=241,
        revocation_registry_root=registry_root,
        revocation_record_id=record_id,
    )
    return candidate, cursor, selector_bytes, selector_id, record_bytes, record_id


def _pins(
    candidate: candidate_module.SpotV7ReleaseCandidateManifestV1,
    cursor: store_module.SpotV7ReleaseSelectionCursorV1,
    record_bytes: bytes,
    record_id: bytes,
    *,
    registry: dict[str, Any],
    trusted_evaluation_epoch: int = EVALUATION_EPOCH,
    current_revocation_record_id: bytes | None = None,
    registry_revocation_epoch: int | None = None,
) -> SpotV7ReleaseRevocationExternalTrustPinsV1:
    document = cast(dict[str, Any], json.loads(candidate.canonical_bytes))
    scope = cast(dict[str, Any], document["scope"])
    lineage = _candidate_lineage(candidate)
    record = selector_module.parse_exact_spot_v7_revocation_record_v1(
        record_bytes,
        expected_record_id=record_id,
    )
    assert cursor.current_candidate_id is not None
    assert cursor.current_candidate_sha256 is not None
    assert cursor.current_release_revision is not None
    assert cursor.current_select_input_id is not None
    assert cursor.last_evaluation_epoch is not None
    return SpotV7ReleaseRevocationExternalTrustPinsV1(
        application_id=cast(str, scope["application_id"]),
        chain_id=cast(str, scope["chain_id"]),
        domain_id=cast(str, scope["domain_id"]),
        release_profile=cast(str, scope["release_profile"]),
        trusted_evaluation_epoch=trusted_evaluation_epoch,
        expected_database_revision=cursor.database_revision,
        expected_last_evaluation_epoch=cursor.last_evaluation_epoch,
        expected_current_candidate_id=cursor.current_candidate_id,
        expected_current_candidate_sha256=cursor.current_candidate_sha256,
        expected_current_release_revision=cursor.current_release_revision,
        expected_current_select_input_id=cursor.current_select_input_id,
        current_revocation_record_id=current_revocation_record_id,
        rollback_policy_root=bytes.fromhex(cast(str, lineage["rollback_policy_root"])),
        revocation_policy_root=bytes.fromhex(cast(str, lineage["revocation_policy_root"])),
        revocation_registry_root=record.revocation_registry_root,
        expected_revocation_record_id=record.record_id,
        expected_revocation_effective_epoch=record.effective_epoch,
        expected_revocation_record_revision=record.record_revision,
        expected_revocation_reason_code=record.reason_code,
        expected_revocation_issuer_set_root=record.issuer_set_root,
        signer_registry_id=cast(str, registry["registry_id"]),
        expected_signer_registry_hash=cast(str, registry["registry_hash"]),
        signer_registry_revision=REGISTRY_REVISION,
        signer_registry_activation_epoch=REGISTRY_ACTIVATION_EPOCH,
        signer_registry_revocation_epoch=registry_revocation_epoch,
        expected_quorum_threshold=cast(int, registry["threshold"]),
    )


def _envelope_and_signatures() -> tuple[
    bytes,
    tuple[dict[str, Any], ...],
    candidate_module.SpotV7ReleaseCandidateManifestV1,
    bytes,
    bytes,
    bytes,
    bytes,
    SpotV7ReleaseRevocationExternalTrustPinsV1,
    dict[str, Any],
]:
    candidate, cursor, selector_bytes, selector_id, record_bytes, record_id = _current_material()
    registry = _registry()
    pins = _pins(candidate, cursor, record_bytes, record_id, registry=registry)
    envelope = build_spot_v7_release_revocation_envelope_v1(
        revocation_selector_input_bytes=selector_bytes,
        expected_revocation_selector_input_id=selector_id,
        current_candidate_bytes=candidate.canonical_bytes,
        revocation_record_bytes=record_bytes,
        expected_revocation_record_id=record_id,
        external_trust_pins=pins,
        trusted_signer_registry=registry,
    )
    payload_hash = spot_v7_release_revocation_envelope_payload_hash_v1(envelope)
    signatures = tuple(
        build_bls_signed_artifact_envelope_v0(
            payload_kind=SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id=f"release-revocation-signer-{index}",
            key_id=f"release-revocation-key-{index}",
            private_key_hex=private_key,
        )
        for index, private_key in enumerate((PRIVATE_KEY_0, PRIVATE_KEY_1))
    )
    return (
        envelope,
        signatures,
        candidate,
        selector_bytes,
        selector_id,
        record_bytes,
        record_id,
        pins,
        registry,
    )


def _authenticate(
    envelope: bytes,
    signatures: object,
    candidate: candidate_module.SpotV7ReleaseCandidateManifestV1,
    selector_bytes: bytes,
    selector_id: bytes,
    record_bytes: bytes,
    record_id: bytes,
    pins: SpotV7ReleaseRevocationExternalTrustPinsV1,
    registry: object,
) -> _AuthenticatedSpotV7ReleaseRevocationV1:
    return authenticate_spot_v7_release_revocation_v1(
        envelope,
        revocation_selector_input_bytes=selector_bytes,
        expected_revocation_selector_input_id=selector_id,
        current_candidate_bytes=candidate.canonical_bytes,
        revocation_record_bytes=record_bytes,
        expected_revocation_record_id=record_id,
        external_trust_pins=pins,
        trusted_signer_registry=registry,
        signature_envelopes=signatures,
    )


def _authenticated_result() -> _AuthenticatedSpotV7ReleaseRevocationV1:
    return _authenticate(*_envelope_and_signatures())


def test_exact_quorum_authentication_mints_authority_neutral_private_capability() -> None:
    material = _envelope_and_signatures()
    result = _authenticate(*material)
    parsed = parse_exact_spot_v7_release_revocation_envelope_v1(material[0])

    assert type(result) is _AuthenticatedSpotV7ReleaseRevocationV1
    assert result.revocation_selector_input_id == parsed.revocation_selector_input_id
    assert result.current_candidate_id == parsed.current_candidate_id
    assert result.current_candidate_sha256 == parsed.current_candidate_sha256
    assert result.current_select_input_id == parsed.current_select_input_id
    assert result.revocation_record_id == parsed.revocation_record_id
    assert result.revocation_effective_epoch == EVALUATION_EPOCH
    assert result.revocation_record_revision == RECORD_REVISION
    assert result.signature_quorum_authenticated is True
    assert result.exact_current_selection_bound is True
    assert result.exact_revocation_record_bound is True
    assert result.release_governed_registry_pin_authenticated is False
    assert result.durable_revocation_committed is False
    assert result.replay_prevention_established is False
    assert result.hostile_same_interpreter_resistance_established is False
    assert result.revocation_authority is False
    assert result.release_authority is False
    assert result.runtime_authority is False
    assert result.settlement_authority is False
    assert result.production_authority is False


def test_signature_order_is_canonical_and_duplicate_signer_rejects() -> None:
    material = _envelope_and_signatures()
    forward = _authenticate(*material)
    reverse_material = (material[0], tuple(reversed(material[1])), *material[2:])
    reverse = _authenticate(*reverse_material)
    assert forward.evidence_sha256 == reverse.evidence_sha256
    assert forward.quorum_report_hash == reverse.quorum_report_hash

    duplicate_material = (material[0], (material[1][0], material[1][0]), *material[2:])
    with pytest.raises(
        SpotV7ReleaseRevocationAuthenticationErrorV1,
        match="SIGNATURE_QUORUM_INVALID.*duplicate envelope",
    ):
        _authenticate(*duplicate_material)


def test_registry_and_signature_inputs_reject_overdeep_in_memory_shapes() -> None:
    material = _envelope_and_signatures()
    overdeep_registry = dict(material[8])
    overdeep_registry["uncommitted"] = {"a": {"b": {"c": "value"}}}
    with pytest.raises(
        SpotV7ReleaseRevocationAuthenticationErrorV1,
        match="SIGNER_REGISTRY_SIZE",
    ):
        build_spot_v7_release_revocation_envelope_v1(
            revocation_selector_input_bytes=material[3],
            expected_revocation_selector_input_id=material[4],
            current_candidate_bytes=material[2].canonical_bytes,
            revocation_record_bytes=material[5],
            expected_revocation_record_id=material[6],
            external_trust_pins=material[7],
            trusted_signer_registry=overdeep_registry,
        )

    overdeep_signature = dict(material[1][0])
    overdeep_signature["uncommitted"] = {"nested": "value"}
    changed = (
        material[0],
        (overdeep_signature, material[1][1]),
        *material[2:],
    )
    with pytest.raises(
        SpotV7ReleaseRevocationAuthenticationErrorV1,
        match="SIGNATURE_ENVELOPE_SIZE",
    ):
        _authenticate(*changed)


def test_cross_kind_signature_rejects() -> None:
    material = _envelope_and_signatures()
    payload_hash = spot_v7_release_revocation_envelope_payload_hash_v1(material[0])
    wrong = tuple(
        build_bls_signed_artifact_envelope_v0(
            payload_kind="zrpf_spot_v7_release_selection",
            payload_hash=payload_hash,
            signer_id=f"release-revocation-signer-{index}",
            key_id=f"release-revocation-key-{index}",
            private_key_hex=private_key,
        )
        for index, private_key in enumerate((PRIVATE_KEY_0, PRIVATE_KEY_1))
    )
    wrong_material = (material[0], wrong, *material[2:])
    with pytest.raises(
        SpotV7ReleaseRevocationAuthenticationErrorV1,
        match="SIGNATURE_QUORUM_INVALID",
    ):
        _authenticate(*wrong_material)


def test_wrong_scope_and_current_selection_hash_reject() -> None:
    material = _envelope_and_signatures()
    wrong_scope = replace(material[7], domain_id="other-domain")
    wrong_hash = replace(material[7], expected_current_candidate_sha256=_position_bytes(249))
    for pins, code in (
        (wrong_scope, "DOMAIN_ID_MISMATCH"),
        (wrong_hash, "CURRENT_CANDIDATE_SHA256_MISMATCH"),
    ):
        changed = (*material[:7], pins, material[8])
        with pytest.raises(SpotV7ReleaseRevocationAuthenticationErrorV1, match=code):
            _authenticate(*changed)


def test_stale_future_and_replayed_revocation_inputs_reject() -> None:
    material = _envelope_and_signatures()
    stale = replace(
        material[7],
        trusted_evaluation_epoch=LAST_EVALUATION_EPOCH - 1,
    )
    replayed = replace(material[7], current_revocation_record_id=material[6])
    for pins, code in (
        (stale, "EVALUATION_EPOCH_ROLLBACK"),
        (replayed, "CURRENT_SELECTION_ALREADY_REVOKED"),
    ):
        changed = (*material[:7], pins, material[8])
        with pytest.raises(SpotV7ReleaseRevocationAuthenticationErrorV1, match=code):
            _authenticate(*changed)

    candidate, cursor, selector_bytes, selector_id, record_bytes, record_id = _current_material(
        effective_epoch=EVALUATION_EPOCH + 1
    )
    registry = _registry()
    pins = _pins(candidate, cursor, record_bytes, record_id, registry=registry)
    with pytest.raises(
        SpotV7ReleaseRevocationAuthenticationErrorV1,
        match="REVOCATION_EFFECTIVE_EPOCH_FUTURE",
    ):
        build_spot_v7_release_revocation_envelope_v1(
            revocation_selector_input_bytes=selector_bytes,
            expected_revocation_selector_input_id=selector_id,
            current_candidate_bytes=candidate.canonical_bytes,
            revocation_record_bytes=record_bytes,
            expected_revocation_record_id=record_id,
            external_trust_pins=pins,
            trusted_signer_registry=registry,
        )


def test_wrong_record_and_selector_bindings_reject() -> None:
    material = _envelope_and_signatures()
    bad_record = material[5][:-1] + bytes([material[5][-1] ^ 1])
    with pytest.raises(
        SpotV7ReleaseRevocationAuthenticationErrorV1,
        match="REVOCATION_RECORD_INVALID",
    ):
        authenticate_spot_v7_release_revocation_v1(
            material[0],
            revocation_selector_input_bytes=material[3],
            expected_revocation_selector_input_id=material[4],
            current_candidate_bytes=material[2].canonical_bytes,
            revocation_record_bytes=bad_record,
            expected_revocation_record_id=material[6],
            external_trust_pins=material[7],
            trusted_signer_registry=material[8],
            signature_envelopes=material[1],
        )
    with pytest.raises(
        SpotV7ReleaseRevocationAuthenticationErrorV1,
        match="REVOCATION_SELECTOR_INVALID",
    ):
        authenticate_spot_v7_release_revocation_v1(
            material[0],
            revocation_selector_input_bytes=material[3],
            expected_revocation_selector_input_id=_position_bytes(248),
            current_candidate_bytes=material[2].canonical_bytes,
            revocation_record_bytes=material[5],
            expected_revocation_record_id=material[6],
            external_trust_pins=material[7],
            trusted_signer_registry=material[8],
            signature_envelopes=material[1],
        )


def test_unknown_duplicate_ambiguous_and_malformed_envelopes_reject() -> None:
    material = _envelope_and_signatures()
    document = cast(dict[str, Any], json.loads(material[0]))
    document["verified"] = True
    unknown = canonical_json_bytes(document)
    duplicate = b'{"current_selection":null,' + material[0][1:]
    ambiguous = cast(dict[str, Any], json.loads(material[0]))
    current = cast(dict[str, Any], ambiguous["current_selection"])
    current["current_select_input_id"] = None
    cases = (
        (unknown, "FIELD_SET_MISMATCH"),
        (duplicate, "DUPLICATE_JSON_KEY"),
        (canonical_json_bytes(ambiguous), "ROOT_REQUIRED"),
        (material[0][:-1], "INVALID_JSON"),
    )
    for raw, code in cases:
        with pytest.raises(SpotV7ReleaseRevocationEnvelopeRejectV1, match=code):
            parse_exact_spot_v7_release_revocation_envelope_v1(raw)


def test_registry_lifecycle_and_exact_tuple_are_enforced() -> None:
    material = _envelope_and_signatures()
    revoked = replace(material[7], signer_registry_revocation_epoch=EVALUATION_EPOCH)
    revision = replace(material[7], signer_registry_revision=REGISTRY_REVISION + 1)
    for pins, code in (
        (revoked, "SIGNER_REGISTRY_REVOKED"),
        (revision, "REVOCATION_ENVELOPE_BINDING_MISMATCH"),
    ):
        changed = (*material[:7], pins, material[8])
        with pytest.raises(SpotV7ReleaseRevocationAuthenticationErrorV1, match=code):
            _authenticate(*changed)


def test_capability_and_durable_projection_are_private_frozen_and_authority_false() -> None:
    result = _authenticated_result()
    first = result._artifacts_for_durable_store_v1()
    second = result._artifacts_for_durable_store_v1()

    assert type(first) is _AuthenticatedReleaseRevocationDurableArtifactsV1
    assert first is not second
    assert first == second
    assert {field.name for field in fields(first)} == {
        "authentication_evidence_bytes",
        "current_candidate_bytes",
        "envelope_bytes",
        "external_trust_pins_bytes",
        "quorum_report_bytes",
        "revocation_record_bytes",
        "revocation_selector_input_bytes",
        "signature_envelopes_bytes",
        "signer_registry_bytes",
    }
    assert all(type(getattr(first, field.name)) is bytes for field in fields(first))
    assert first.durable_revocation_committed is False
    assert first.revocation_authority is False
    assert first.release_authority is False
    assert first.runtime_authority is False
    assert first.settlement_authority is False
    assert first.production_authority is False

    with pytest.raises(TypeError, match="verified construction"):
        _AuthenticatedSpotV7ReleaseRevocationV1()
    with pytest.raises(TypeError, match="revalidated construction"):
        _AuthenticatedReleaseRevocationDurableArtifactsV1()
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(result)
    with pytest.raises(TypeError, match="cannot be deep-copied"):
        copy.deepcopy(first)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(result)
    with pytest.raises(FrozenInstanceError):
        first.current_candidate_bytes = b"forged"  # type: ignore[misc]


def test_durable_projection_revalidates_retained_evidence_and_capability_fields() -> None:
    result = _authenticated_result()
    evidence = cast(dict[str, Any], json.loads(result._evidence_bytes))
    report = cast(dict[str, Any], evidence["signature_quorum_report"])
    report["accepted_weight"] += 1
    tampered = canonical_json_bytes(evidence)
    object.__setattr__(result, "_evidence_bytes", tampered)
    object.__setattr__(result, "_evidence_sha256", hashlib.sha256(tampered).hexdigest())
    with pytest.raises(
        SpotV7ReleaseRevocationAuthenticationErrorV1,
        match="RETAINED_QUORUM_REPORT_MISMATCH",
    ):
        result._artifacts_for_durable_store_v1()

    clean = _authenticated_result()
    object.__setattr__(clean, "_revocation_record_revision", RECORD_REVISION + 1)
    with pytest.raises(
        SpotV7ReleaseRevocationAuthenticationErrorV1,
        match="AUTHENTICATED_CAPABILITY_FIELD_DRIFT",
    ):
        clean._artifacts_for_durable_store_v1()


def test_payload_kind_is_dedicated_and_external_pins_remain_non_authoritative() -> None:
    material = _envelope_and_signatures()
    assert SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1 in SUPPORTED_PAYLOAD_KINDS_V0
    assert SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1 not in {
        "zrpf_spot_v7_release_selection",
        "zrpf_spot_v7_operational_policy",
    }
    assert material[7].release_governed_registry_pin_authenticated is False
    assert material[7].revocation_authority is False
    assert material[7].release_authority is False
    assert material[7].production_authority is False
