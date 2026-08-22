"""Exact owned snapshots for untrusted command-authentication inputs."""

from __future__ import annotations

from .economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationCandidateV1,
    EconomicCommandAuthenticationEnvelopeV1,
    EconomicCommandIntentV1,
)
from .economic_command_authorization_registry_v1 import (
    EconomicCommandAuthorizationRegistryV1,
    EconomicCommandAuthorizationV1,
)
from .economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierRegistryV1,
    EconomicCommandSignatureVerifierReleaseV1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_settlement_types_v1 import (
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
)


def snapshot_command_authentication_candidate_v1(
    candidate: EconomicCommandAuthenticationCandidateV1,
) -> EconomicCommandAuthenticationCandidateV1:
    if type(candidate) is not EconomicCommandAuthenticationCandidateV1:
        raise TypeError("command authentication candidate must have the exact type")
    return EconomicCommandAuthenticationCandidateV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        policy_registry=_snapshot_policy_registry_v1(candidate.policy_registry),
        authorization_registry=_snapshot_authorization_registry_v1(
            candidate.authorization_registry
        ),
        signature_verifier_registry=_snapshot_signature_verifier_registry_v1(
            candidate.signature_verifier_registry
        ),
        intent=snapshot_economic_command_intent_v1(candidate.intent),
        envelope=_snapshot_envelope_v1(candidate.envelope),
    )


def snapshot_economic_command_intent_v1(
    intent: EconomicCommandIntentV1,
) -> EconomicCommandIntentV1:
    if type(intent) is not EconomicCommandIntentV1:
        raise TypeError("economic command intent must have the exact typed value")
    token_values = (
        intent.chain_id,
        intent.deployment_root,
        intent.profile_root,
        intent.command_kind,
        intent.command_body_hash,
        intent.route_release_id,
        intent.subject_id,
        intent.grant_root,
    )
    if any(type(value) is not str for value in token_values):
        raise TypeError("economic command intent token fields must be exact strings")
    numeric_values = (
        intent.nonce,
        intent.valid_from_height,
        intent.valid_through_height,
    )
    if any(type(value) is not int for value in numeric_values):
        raise TypeError("economic command intent numeric fields must be exact integers")
    if type(intent.consumed_object_ids) is not tuple or any(
        type(value) is not str for value in intent.consumed_object_ids
    ):
        raise TypeError("economic command intent objects must be exact strings")
    return EconomicCommandIntentV1(
        chain_id=intent.chain_id,
        deployment_root=intent.deployment_root,
        profile_root=intent.profile_root,
        command_kind=intent.command_kind,
        command_body_hash=intent.command_body_hash,
        route_release_id=intent.route_release_id,
        subject_id=intent.subject_id,
        grant_root=intent.grant_root,
        nonce=intent.nonce,
        consumed_object_ids=tuple(intent.consumed_object_ids),
        valid_from_height=intent.valid_from_height,
        valid_through_height=intent.valid_through_height,
    )


def _snapshot_policy_registry_v1(
    registry: EconomicPolicyRegistryV1,
) -> EconomicPolicyRegistryV1:
    if type(registry) is not EconomicPolicyRegistryV1 or type(registry.bindings) is not tuple:
        raise TypeError("economic policy registry must have the exact typed value")
    if any(type(binding) is not EconomicPolicyBindingV1 for binding in registry.bindings):
        raise TypeError("economic policy registry bindings must have exact typed values")
    snapshots = []
    for binding in registry.bindings:
        if any(
            type(value) is not str
            for value in (binding.policy_kind, binding.command_kind, binding.policy_root)
        ):
            raise TypeError("economic policy binding fields must be exact strings")
        snapshots.append(
            EconomicPolicyBindingV1(
                binding.policy_kind,
                binding.command_kind,
                binding.policy_root,
            )
        )
    return EconomicPolicyRegistryV1(tuple(snapshots))


def _snapshot_authorization_v1(
    authorization: EconomicCommandAuthorizationV1,
) -> EconomicCommandAuthorizationV1:
    if type(authorization) is not EconomicCommandAuthorizationV1:
        raise TypeError("command authorization must have the exact typed value")
    tokens = (
        authorization.command_kind,
        authorization.subject_id,
        authorization.grant_root,
        authorization.route_release_id,
        authorization.signer_key_id,
        authorization.signer_public_key,
        authorization.signature_algorithm,
    )
    intervals = (
        authorization.valid_from_height,
        authorization.valid_through_height,
        authorization.min_nonce,
        authorization.max_nonce,
    )
    if any(type(value) is not str for value in tokens):
        raise TypeError("command authorization token fields must be exact strings")
    if any(type(value) is not int for value in intervals):
        raise TypeError("command authorization interval fields must be exact integers")
    if type(authorization.enabled) is not bool:
        raise TypeError("command authorization enabled field must be exact bool")
    return EconomicCommandAuthorizationV1(
        command_kind=authorization.command_kind,
        subject_id=authorization.subject_id,
        grant_root=authorization.grant_root,
        route_release_id=authorization.route_release_id,
        signer_key_id=authorization.signer_key_id,
        signer_public_key=authorization.signer_public_key,
        signature_algorithm=authorization.signature_algorithm,
        valid_from_height=authorization.valid_from_height,
        valid_through_height=authorization.valid_through_height,
        min_nonce=authorization.min_nonce,
        max_nonce=authorization.max_nonce,
        enabled=authorization.enabled,
    )


def _snapshot_authorization_registry_v1(
    registry: EconomicCommandAuthorizationRegistryV1,
) -> EconomicCommandAuthorizationRegistryV1:
    if (
        type(registry) is not EconomicCommandAuthorizationRegistryV1
        or type(registry.authorizations) is not tuple
    ):
        raise TypeError("command authorization registry must have the exact typed value")
    return EconomicCommandAuthorizationRegistryV1(
        tuple(_snapshot_authorization_v1(item) for item in registry.authorizations)
    )


def _snapshot_signature_verifier_registry_v1(
    registry: EconomicCommandSignatureVerifierRegistryV1,
) -> EconomicCommandSignatureVerifierRegistryV1:
    if (
        type(registry) is not EconomicCommandSignatureVerifierRegistryV1
        or type(registry.releases) is not tuple
    ):
        raise TypeError("command signature verifier registry must be exactly typed")
    releases: list[EconomicCommandSignatureVerifierReleaseV1] = []
    for release in registry.releases:
        if type(release) is not EconomicCommandSignatureVerifierReleaseV1:
            raise TypeError("command signature verifier release must be exactly typed")
        string_fields = (
            release.release_id,
            release.semantic_version,
            release.signature_algorithm,
            release.implementation_root,
            release.public_key_schema_root,
            release.signature_schema_root,
            release.message_schema_root,
            release.specification_root,
            release.source_root,
            release.toolchain_root,
            release.evidence_manifest_root,
        )
        if any(type(value) is not str for value in string_fields):
            raise TypeError("command signature verifier string fields must be exact")
        if (
            type(release.max_public_key_bytes) is not int
            or type(release.max_signature_bytes) is not int
        ):
            raise TypeError("command signature verifier ceilings must be exact integers")
        if type(release.accepts_new_authentications) is not bool:
            raise TypeError("command signature verifier active flag must be exact bool")
        if type(release.evidence_statuses) is not tuple:
            raise TypeError("command signature verifier evidence must be an exact tuple")
        releases.append(
            EconomicCommandSignatureVerifierReleaseV1(
                release_id=release.release_id,
                semantic_version=release.semantic_version,
                signature_algorithm=release.signature_algorithm,
                implementation_root=release.implementation_root,
                public_key_schema_root=release.public_key_schema_root,
                signature_schema_root=release.signature_schema_root,
                message_schema_root=release.message_schema_root,
                specification_root=release.specification_root,
                source_root=release.source_root,
                toolchain_root=release.toolchain_root,
                evidence_manifest_root=release.evidence_manifest_root,
                max_public_key_bytes=release.max_public_key_bytes,
                max_signature_bytes=release.max_signature_bytes,
                status=release.status,
                accepts_new_authentications=release.accepts_new_authentications,
                evidence_statuses=tuple(release.evidence_statuses),
            )
        )
    return EconomicCommandSignatureVerifierRegistryV1(tuple(releases))


def _snapshot_envelope_v1(
    envelope: EconomicCommandAuthenticationEnvelopeV1,
) -> EconomicCommandAuthenticationEnvelopeV1:
    if type(envelope) is not EconomicCommandAuthenticationEnvelopeV1:
        raise TypeError("command authentication envelope must have the exact typed value")
    if (
        type(envelope.command_body_bytes) is not bytes
        or type(envelope.signature_bytes) is not bytes
    ):
        raise TypeError("command authentication envelope byte fields must be exact bytes")
    if any(
        type(value) is not str
        for value in (
            envelope.signer_key_id,
            envelope.signer_public_key,
            envelope.signature_algorithm,
        )
    ):
        raise TypeError("command authentication envelope token fields must be exact strings")
    return EconomicCommandAuthenticationEnvelopeV1(
        command_body_bytes=envelope.command_body_bytes,
        signer_key_id=envelope.signer_key_id,
        signer_public_key=envelope.signer_public_key,
        signature_algorithm=envelope.signature_algorithm,
        signature_bytes=envelope.signature_bytes,
    )


__all__ = [
    "snapshot_command_authentication_candidate_v1",
    "snapshot_economic_command_intent_v1",
]
