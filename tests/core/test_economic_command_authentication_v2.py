"""Bounded V2 command-intent preparation and occurrence-binding contracts."""

from __future__ import annotations

import hashlib
from dataclasses import replace
from typing import Any, Final

import pytest

from src.core.economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationEnvelopeV1,
)
from src.core.economic_command_authentication_types_v2 import (
    ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2,
    EconomicCommandAuthenticationCandidateV2,
    EconomicCommandIntentV2,
    snapshot_command_authentication_candidate_v2,
    snapshot_economic_command_intent_v2,
)
from src.core.economic_command_authentication_v2 import (
    ECONOMIC_COMMAND_AUTHENTICATION_MESSAGE_SCHEMA_ROOT_V2,
    prepare_isolated_economic_command_authentication_v2,
    require_economic_command_intent_occurrence_v2,
)
from src.core.economic_command_authorization_registry_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    EconomicCommandAuthorizationRegistryV1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
    EconomicCommandSignatureVerifierRegistryV1,
    EconomicCommandSignatureVerifierReleaseV1,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_primitives_v2 import (
    MAX_U64_V2,
    canonical_global_bytes_v2,
    hash_economic_command_body_bytes_v2,
)
from src.core.global_settlement_resource_limits_v2 import (
    MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2,
    StateResourceLimitExceededV2,
)
from src.core.global_settlement_types_v1 import (
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    hash_economic_command_body_bytes_v1,
)
from src.state.canonical import domain_sep_bytes
from tests.core.test_economic_command_authentication_v1 import (
    _fixture as _fixture_v1,
)
from tests.core.test_economic_command_authentication_v1 import (
    _rebuild_profile,
)
from tests.core.test_lane_module_release_route_binding_v1 import _root

_AUTH_SCHEMA_V2: Final = "zenodex/economic-command-authentication/v2"
_MESSAGE_DOMAIN_V2: Final = "economic-command-intent-authentication-message-v2"
_SCHEMA_DOMAIN_V2: Final = "economic-command-intent-authentication-schema-v2"
_INTENT_FIELDS: Final = (
    "chain_id",
    "deployment_root",
    "profile_root",
    "command_kind",
    "command_body_hash",
    "route_release_id",
    "subject_id",
    "grant_root",
    "nonce",
    "consumed_object_ids",
    "valid_from_height",
    "valid_through_height",
)
_MESSAGE_FIELDS: Final = (
    "schema",
    "policy_registry_root",
    "authorization_registry_root",
    "authorization_id",
    "verifier_registry_root",
    "signature_verifier_registry_root",
    "signature_verifier_release_id",
    "intent",
    "command_body_bytes_digest",
    "signature_algorithm",
    "signer_key_id",
    "signer_public_key",
)
_BODY_V2: Final = b'{"economic-command-authentication":"v2"}'


def _shadow_release(
    source: EconomicCommandSignatureVerifierReleaseV1,
    *,
    message_schema_root: str = ECONOMIC_COMMAND_AUTHENTICATION_MESSAGE_SCHEMA_ROOT_V2,
) -> EconomicCommandSignatureVerifierReleaseV1:
    return EconomicCommandSignatureVerifierReleaseV1.build(
        semantic_version=source.semantic_version,
        signature_algorithm=source.signature_algorithm,
        implementation_root=source.implementation_root,
        public_key_schema_root=source.public_key_schema_root,
        signature_schema_root=source.signature_schema_root,
        message_schema_root=message_schema_root,
        specification_root=source.specification_root,
        source_root=source.source_root,
        toolchain_root=source.toolchain_root,
        evidence_manifest_root=source.evidence_manifest_root,
        max_public_key_bytes=source.max_public_key_bytes,
        max_signature_bytes=source.max_signature_bytes,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_authentications=False,
        evidence_statuses=source.evidence_statuses,
    )


def _policy_registry(
    *,
    command_kind: str,
    authorization_root: str,
    verifier_root: str,
) -> EconomicPolicyRegistryV1:
    bindings = (
        EconomicPolicyBindingV1(
            ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
            command_kind,
            authorization_root,
        ),
        EconomicPolicyBindingV1(
            ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
            command_kind,
            verifier_root,
        ),
    )
    return EconomicPolicyRegistryV1(
        tuple(sorted(bindings, key=lambda binding: (binding.policy_kind, binding.command_kind)))
    )


def _candidate_and_occurrence(
    *,
    body: bytes = _BODY_V2,
    intent_body_hash: str | None = None,
    intent_updates: dict[str, Any] | None = None,
    envelope_updates: dict[str, Any] | None = None,
    authorization_updates: dict[str, Any] | None = None,
    authorization_policy_root: str | None = None,
    profile_policy_root: str | None = None,
    profile_status: ProfileStatusV1 = ProfileStatusV1.ACTIVE,
    message_schema_root: str = ECONOMIC_COMMAND_AUTHENTICATION_MESSAGE_SCHEMA_ROOT_V2,
    occurrence_height: int = 11,
) -> tuple[EconomicCommandAuthenticationCandidateV2, EconomicCommandOccurrenceV2]:
    fixture = _fixture_v1()
    envelope = replace(fixture.envelope, command_body_bytes=body)
    if envelope_updates is not None:
        envelope = replace(envelope, **envelope_updates)
    authorization = fixture.authorization
    if authorization_updates is not None:
        authorization = replace(authorization, **authorization_updates)
    authorization_registry = EconomicCommandAuthorizationRegistryV1((authorization,))
    signature_registry = EconomicCommandSignatureVerifierRegistryV1(
        (
            _shadow_release(
                fixture.signature_verifier_registry.releases[0],
                message_schema_root=message_schema_root,
            ),
        )
    )
    policy_registry = _policy_registry(
        command_kind=fixture.intent.command_kind,
        authorization_root=authorization_policy_root or authorization_registry.registry_root,
        verifier_root=signature_registry.registry_root,
    )
    profile = _rebuild_profile(
        fixture.profile,
        profile_policy_root or policy_registry.registry_root,
    )
    if profile_status is not ProfileStatusV1.ACTIVE:
        profile = replace(profile, status=profile_status)
    intent = EconomicCommandIntentV2(
        chain_id=fixture.intent.chain_id,
        deployment_root=fixture.intent.deployment_root,
        profile_root=profile.profile_id,
        command_kind=fixture.intent.command_kind,
        command_body_hash=intent_body_hash or hash_economic_command_body_bytes_v2(body),
        route_release_id=fixture.intent.route_release_id,
        subject_id=fixture.intent.subject_id,
        grant_root=fixture.intent.grant_root,
        nonce=fixture.intent.nonce,
        consumed_object_ids=fixture.intent.consumed_object_ids,
        valid_from_height=fixture.intent.valid_from_height,
        valid_through_height=fixture.intent.valid_through_height,
    )
    if intent_updates is not None:
        intent = replace(intent, **intent_updates)
    candidate = EconomicCommandAuthenticationCandidateV2(
        profile=profile,
        policy_registry=policy_registry,
        authorization_registry=authorization_registry,
        signature_verifier_registry=signature_registry,
        intent=intent,
        envelope=envelope,
    )
    occurrence = EconomicCommandOccurrenceV2(
        chain_id=intent.chain_id,
        deployment_root=intent.deployment_root,
        height=occurrence_height,
        tx_index=2,
        op_index=3,
        command_kind=intent.command_kind,
        command_body_hash=intent.command_body_hash,
        route_release_id=intent.route_release_id,
        subject_id=intent.subject_id,
        grant_root=intent.grant_root,
        nonce=intent.nonce,
        profile_root=intent.profile_root,
        pre_state_root=_root(2),
        consumed_object_ids=intent.consumed_object_ids,
    )
    return candidate, occurrence


def _expected_schema_root() -> str:
    descriptor = {
        "schema": _AUTH_SCHEMA_V2,
        "message_domain": _MESSAGE_DOMAIN_V2,
        "intent_fields": _INTENT_FIELDS,
        "message_fields": _MESSAGE_FIELDS,
    }
    digest = hashlib.sha256()
    digest.update(domain_sep_bytes(_SCHEMA_DOMAIN_V2, version=2))
    digest.update(canonical_global_bytes_v2(descriptor))
    return "0x" + digest.hexdigest()


def _expected_message(
    candidate: EconomicCommandAuthenticationCandidateV2,
    release: EconomicCommandSignatureVerifierReleaseV1,
) -> bytes:
    intent = candidate.intent
    authorization = candidate.authorization_registry.authorizations[0]
    body = {
        "schema": _AUTH_SCHEMA_V2,
        "policy_registry_root": candidate.policy_registry.registry_root,
        "authorization_registry_root": candidate.authorization_registry.registry_root,
        "authorization_id": authorization.authorization_id,
        "verifier_registry_root": candidate.profile.verifier_registry_root,
        "signature_verifier_registry_root": candidate.signature_verifier_registry.registry_root,
        "signature_verifier_release_id": release.release_id,
        "intent": {
            "schema": _AUTH_SCHEMA_V2,
            "chain_id": intent.chain_id,
            "deployment_root": intent.deployment_root,
            "profile_root": intent.profile_root,
            "command_kind": intent.command_kind,
            "command_body_hash": intent.command_body_hash,
            "route_release_id": intent.route_release_id,
            "subject_id": intent.subject_id,
            "grant_root": intent.grant_root,
            "nonce": intent.nonce,
            "consumed_object_ids": intent.consumed_object_ids,
            "valid_from_height": intent.valid_from_height,
            "valid_through_height": intent.valid_through_height,
        },
        "command_body_bytes_digest": "0x"
        + hashlib.sha256(candidate.envelope.command_body_bytes).hexdigest(),
        "signature_algorithm": candidate.envelope.signature_algorithm,
        "signer_key_id": candidate.envelope.signer_key_id,
        "signer_public_key": candidate.envelope.signer_public_key,
    }
    return domain_sep_bytes(_MESSAGE_DOMAIN_V2, version=2) + canonical_global_bytes_v2(body)


def _replace_occurrence_field(
    occurrence: EconomicCommandOccurrenceV2,
    field: str,
    replacement: object,
) -> EconomicCommandOccurrenceV2:
    updates: dict[str, Any] = {field: replacement}
    return replace(occurrence, **updates)


def test_prepare_constructs_the_fixed_v2_schema_root_and_exact_message() -> None:
    candidate, _ = _candidate_and_occurrence()

    owned, release, message = prepare_isolated_economic_command_authentication_v2(candidate)

    assert ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2 == _AUTH_SCHEMA_V2
    assert ECONOMIC_COMMAND_AUTHENTICATION_MESSAGE_SCHEMA_ROOT_V2 == _expected_schema_root()
    assert release.message_schema_root == _expected_schema_root()
    assert message == _expected_message(candidate, release)
    assert message == _expected_message(owned, release)
    assert message.startswith(domain_sep_bytes(_MESSAGE_DOMAIN_V2, version=2))
    assert owned.intent.command_body_hash == hash_economic_command_body_bytes_v2(_BODY_V2)
    assert owned.intent.command_body_hash != ("0x" + hashlib.sha256(_BODY_V2).hexdigest())
    assert release.status is ReleaseStatusV1.SHADOW
    assert owned is not candidate
    assert owned.intent is not candidate.intent
    assert owned.envelope is not candidate.envelope


def test_prepare_owns_the_candidate_before_returning_plain_data() -> None:
    candidate, _ = _candidate_and_occurrence()
    owned, release, message = prepare_isolated_economic_command_authentication_v2(candidate)

    object.__setattr__(candidate.intent, "subject_id", "mallory")
    object.__setattr__(candidate.envelope, "signer_public_key", "mallory-key")
    object.__setattr__(candidate, "intent", object())

    assert owned.intent.subject_id == "alice"
    assert owned.envelope.signer_public_key == "bls12-381-g2:alice-public-key"
    assert release.release_id == owned.signature_verifier_registry.releases[0].release_id
    assert message == _expected_message(owned, release)


def test_prepare_rejects_the_v1_body_domain_and_body_substitution() -> None:
    v1_fixture = _fixture_v1()
    v1_body = v1_fixture.envelope.command_body_bytes
    assert hash_economic_command_body_bytes_v1(v1_body) != hash_economic_command_body_bytes_v2(
        v1_body
    )
    wrong_domain, _ = _candidate_and_occurrence(
        body=v1_body,
        intent_body_hash=hash_economic_command_body_bytes_v1(v1_body),
    )
    substituted, _ = _candidate_and_occurrence(
        envelope_updates={"command_body_bytes": b'{"substituted":true}'},
    )

    with pytest.raises(ValueError, match="body hash"):
        prepare_isolated_economic_command_authentication_v2(wrong_domain)
    with pytest.raises(ValueError, match="body hash"):
        prepare_isolated_economic_command_authentication_v2(substituted)


def test_prepare_requires_active_profile_and_governed_registries() -> None:
    inactive, _ = _candidate_and_occurrence(profile_status=ProfileStatusV1.SHADOW)
    wrong_intent_profile, _ = _candidate_and_occurrence(intent_updates={"profile_root": _root(900)})
    profile_mismatch, _ = _candidate_and_occurrence(profile_policy_root=_root(901))
    authorization_mismatch, _ = _candidate_and_occurrence(authorization_policy_root=_root(902))

    with pytest.raises(ValueError, match="ACTIVE profile"):
        prepare_isolated_economic_command_authentication_v2(inactive)
    with pytest.raises(ValueError, match="intent profile mismatch"):
        prepare_isolated_economic_command_authentication_v2(wrong_intent_profile)
    with pytest.raises(ValueError, match="policy registry root mismatch"):
        prepare_isolated_economic_command_authentication_v2(profile_mismatch)
    with pytest.raises(ValueError, match="not profile governed"):
        prepare_isolated_economic_command_authentication_v2(authorization_mismatch)


def test_prepare_requires_governed_route_and_exact_authorization_row() -> None:
    wrong_route, _ = _candidate_and_occurrence(intent_updates={"route_release_id": _root(903)})
    absent_authorization, _ = _candidate_and_occurrence(
        authorization_updates={"signer_key_id": "mallory-key"}
    )

    with pytest.raises(ValueError, match="governed route"):
        prepare_isolated_economic_command_authentication_v2(wrong_route)
    with pytest.raises(ValueError, match="absent"):
        prepare_isolated_economic_command_authentication_v2(absent_authorization)


def test_prepare_requires_authorization_enablement_key_algorithm_and_intervals() -> None:
    disabled, _ = _candidate_and_occurrence(authorization_updates={"enabled": False})
    wrong_key, _ = _candidate_and_occurrence(
        envelope_updates={"signer_public_key": "mallory-public-key"}
    )
    wrong_algorithm, _ = _candidate_and_occurrence(
        envelope_updates={"signature_algorithm": "ED25519"}
    )
    wrong_nonce, _ = _candidate_and_occurrence(intent_updates={"nonce": 11})
    wrong_interval, _ = _candidate_and_occurrence(intent_updates={"valid_from_height": 9})

    with pytest.raises(ValueError, match="disabled"):
        prepare_isolated_economic_command_authentication_v2(disabled)
    with pytest.raises(ValueError, match="public key"):
        prepare_isolated_economic_command_authentication_v2(wrong_key)
    with pytest.raises(ValueError, match="algorithm"):
        prepare_isolated_economic_command_authentication_v2(wrong_algorithm)
    with pytest.raises(ValueError, match="nonce"):
        prepare_isolated_economic_command_authentication_v2(wrong_nonce)
    with pytest.raises(ValueError, match="exceeds"):
        prepare_isolated_economic_command_authentication_v2(wrong_interval)


def test_prepare_requires_the_selected_release_to_bind_the_v2_message_schema() -> None:
    candidate, _ = _candidate_and_occurrence(message_schema_root=_root(904))

    with pytest.raises(ValueError, match="message schema root"):
        prepare_isolated_economic_command_authentication_v2(candidate)


@pytest.mark.parametrize(
    ("field", "replacement"),
    (
        ("chain_id", "other-chain"),
        ("deployment_root", _root(910)),
        ("profile_root", _root(911)),
        ("command_kind", "OTHER_COMMAND"),
        ("command_body_hash", _root(912)),
        ("route_release_id", _root(913)),
        ("subject_id", "mallory"),
        ("grant_root", _root(914)),
        ("nonce", 10),
        ("consumed_object_ids", ("object-001",)),
    ),
)
def test_occurrence_rejects_every_signed_intent_coordinate(
    field: str,
    replacement: object,
) -> None:
    candidate, occurrence = _candidate_and_occurrence()

    with pytest.raises(ValueError, match="mismatch"):
        require_economic_command_intent_occurrence_v2(
            candidate.intent,
            _replace_occurrence_field(occurrence, field, replacement),
        )


@pytest.mark.parametrize(
    ("height", "accepted"),
    ((9, False), (10, True), (12, True), (13, False)),
)
def test_occurrence_uses_the_signed_height_interval_neighbors(
    height: int,
    accepted: bool,
) -> None:
    candidate, occurrence = _candidate_and_occurrence(occurrence_height=height)

    if accepted:
        require_economic_command_intent_occurrence_v2(candidate.intent, occurrence)
    else:
        with pytest.raises(ValueError, match="outside validity"):
            require_economic_command_intent_occurrence_v2(candidate.intent, occurrence)


def test_occurrence_leaves_sequencer_coordinates_and_predecessor_unsigned() -> None:
    candidate, occurrence = _candidate_and_occurrence()

    require_economic_command_intent_occurrence_v2(
        candidate.intent,
        replace(occurrence, tx_index=99, op_index=17, pre_state_root=_root(915)),
    )


def test_intent_enforces_u64_object_bound_and_exact_snapshot_types() -> None:
    candidate, _ = _candidate_and_occurrence()
    intent = candidate.intent
    object_ids = tuple(
        f"object-{index:03d}" for index in range(MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2)
    )
    endpoint = replace(
        intent,
        nonce=MAX_U64_V2,
        valid_from_height=MAX_U64_V2,
        valid_through_height=MAX_U64_V2,
        consumed_object_ids=object_ids,
    )

    assert snapshot_economic_command_intent_v2(endpoint) == endpoint
    with pytest.raises(ValueError, match="unsigned 64-bit"):
        replace(intent, nonce=MAX_U64_V2 + 1)
    with pytest.raises(StateResourceLimitExceededV2, match="64-item"):
        replace(intent, consumed_object_ids=object_ids + ("object-064",))

    class StringSubclass(str):
        pass

    object.__setattr__(intent, "subject_id", StringSubclass("mallory"))
    with pytest.raises(TypeError, match="exact strings"):
        snapshot_economic_command_intent_v2(intent)


def test_candidate_snapshot_rejects_exact_type_substitution() -> None:
    candidate, _ = _candidate_and_occurrence()

    class CandidateSubclass(EconomicCommandAuthenticationCandidateV2):
        pass

    substituted = CandidateSubclass(
        profile=candidate.profile,
        policy_registry=candidate.policy_registry,
        authorization_registry=candidate.authorization_registry,
        signature_verifier_registry=candidate.signature_verifier_registry,
        intent=candidate.intent,
        envelope=candidate.envelope,
    )
    object.__setattr__(candidate.intent, "nonce", True)

    with pytest.raises(TypeError, match="exact type"):
        snapshot_command_authentication_candidate_v2(substituted)
    with pytest.raises(TypeError, match="exact integers"):
        snapshot_command_authentication_candidate_v2(candidate)


def test_v1_envelope_remains_an_exact_owned_candidate_component() -> None:
    candidate, _ = _candidate_and_occurrence()

    class EnvelopeSubclass(EconomicCommandAuthenticationEnvelopeV1):
        pass

    object.__setattr__(
        candidate,
        "envelope",
        EnvelopeSubclass(
            candidate.envelope.command_body_bytes,
            candidate.envelope.signer_key_id,
            candidate.envelope.signer_public_key,
            candidate.envelope.signature_algorithm,
            candidate.envelope.signature_bytes,
        ),
    )

    with pytest.raises(TypeError, match="exact typed value"):
        snapshot_command_authentication_candidate_v2(candidate)
