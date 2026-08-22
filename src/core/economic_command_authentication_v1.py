"""Two-stage authentication for whole-economy command admission.

The user signs an economic intent before sequencing. A deterministic binder
later attaches the authenticated intent to the exact sequenced occurrence.
An opaque deployment binding joins the selected release to a measured artifact,
evidence manifest, profile, and backend capability before verification. This
functional core grants no publication authority by itself.
"""

from __future__ import annotations

import hashlib

from ..state.canonical import domain_sep_bytes
from .economic_command_authentication_snapshot_v1 import (
    snapshot_command_authentication_candidate_v1,
)
from .economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationCandidateV1,
    EconomicCommandAuthenticationEnvelopeV1,
    EconomicCommandIntentV1,
)
from .economic_command_authentication_witness_v1 import (
    _AUTHENTICATED_COMMAND_TOKEN,
    _AUTHENTICATED_INTENT_TOKEN,
    AuthenticatedEconomicCommandIntentV1,
    AuthenticatedEconomicCommandV1,
    _AuthenticatedCommandFieldsV1,
    _AuthenticatedIntentFieldsV1,
)
from .economic_command_authorization_registry_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
    EconomicCommandAuthorizationRegistryV1,
    EconomicCommandAuthorizationV1,
)
from .economic_command_signature_verifier_deployment_v1 import (
    BoundEconomicCommandSignatureVerifierV1,
)
from .economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierReleaseV1,
    select_profile_governed_command_signature_verifier_release_v1,
)
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_economic_refinement_snapshot_v1 import _snapshot_occurrence_v1
from .global_settlement_types_v1 import (
    ProfileStatusV1,
    canonical_global_bytes_v1,
    hash_economic_command_body_bytes_v1,
)


def economic_command_authentication_message_bytes_v1(
    candidate: EconomicCommandAuthenticationCandidateV1,
    authorization: EconomicCommandAuthorizationV1,
) -> bytes:
    release = _select_signature_verifier_release_v1(candidate)
    return _authentication_message_bytes_v1(candidate, authorization, release)


def _authentication_message_bytes_v1(
    candidate: EconomicCommandAuthenticationCandidateV1,
    authorization: EconomicCommandAuthorizationV1,
    release: EconomicCommandSignatureVerifierReleaseV1,
) -> bytes:
    body = {
        "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
        "policy_registry_root": candidate.policy_registry.registry_root,
        "authorization_registry_root": candidate.authorization_registry.registry_root,
        "authorization_id": authorization.authorization_id,
        "verifier_registry_root": candidate.profile.verifier_registry_root,
        "signature_verifier_registry_root": (candidate.signature_verifier_registry.registry_root),
        "signature_verifier_release_id": release.release_id,
        "intent": candidate.intent,
        "command_body_bytes_digest": _sha256_root(candidate.envelope.command_body_bytes),
        "signature_algorithm": candidate.envelope.signature_algorithm,
        "signer_key_id": candidate.envelope.signer_key_id,
        "signer_public_key": candidate.envelope.signer_public_key,
    }
    return domain_sep_bytes(
        "economic-command-intent-authentication-message-v1",
        version=1,
    ) + canonical_global_bytes_v1(body)


def authenticate_economic_command_intent_v1(
    candidate: EconomicCommandAuthenticationCandidateV1,
    signature_verifier: BoundEconomicCommandSignatureVerifierV1,
) -> AuthenticatedEconomicCommandIntentV1:
    if type(signature_verifier) is not BoundEconomicCommandSignatureVerifierV1:
        raise TypeError("command signature verifier must be an exact deployment binding")
    owned = snapshot_command_authentication_candidate_v1(candidate)
    authorization = _select_authorization_v1(owned)
    _validate_authorization_for_intent_v1(owned.intent, owned.envelope, authorization)
    release = _select_signature_verifier_release_v1(owned)
    message_bytes = _authentication_message_bytes_v1(
        owned,
        authorization,
        release,
    )
    signature_verifier.require_binding(
        release_id=release.release_id,
        deployment_root=owned.intent.deployment_root,
        profile_root=owned.intent.profile_root,
    )
    verified = signature_verifier.verify_command_signature(
        signature_algorithm=owned.envelope.signature_algorithm,
        signer_public_key=owned.envelope.signer_public_key,
        message_bytes=message_bytes,
        signature_bytes=owned.envelope.signature_bytes,
    )
    if verified is not True:
        raise ValueError("command authentication signature rejected")
    return _authenticated_intent_v1(
        owned,
        authorization,
        release,
        signature_verifier,
        message_bytes,
    )


def bind_authenticated_intent_to_occurrence_v1(
    authenticated_intent: AuthenticatedEconomicCommandIntentV1,
    occurrence: EconomicCommandOccurrenceV1,
) -> AuthenticatedEconomicCommandV1:
    if type(authenticated_intent) is not AuthenticatedEconomicCommandIntentV1:
        raise TypeError("authenticated intent must have the exact opaque type")
    intent = authenticated_intent.intent
    owned_occurrence = _snapshot_occurrence_v1(occurrence)
    signed_fields = (
        ("chain", intent.chain_id, owned_occurrence.chain_id),
        ("deployment", intent.deployment_root, owned_occurrence.deployment_root),
        ("profile", intent.profile_root, owned_occurrence.profile_root),
        ("command kind", intent.command_kind, owned_occurrence.command_kind),
        ("command body", intent.command_body_hash, owned_occurrence.command_body_hash),
        ("route", intent.route_release_id, owned_occurrence.route_release_id),
        ("subject", intent.subject_id, owned_occurrence.subject_id),
        ("grant", intent.grant_root, owned_occurrence.grant_root),
        ("nonce", intent.nonce, owned_occurrence.nonce),
        ("consumed objects", intent.consumed_object_ids, owned_occurrence.consumed_object_ids),
    )
    for label, expected, actual in signed_fields:
        if type(expected) is not type(actual) or expected != actual:
            raise ValueError(f"authenticated intent occurrence {label} mismatch")
    if not intent.valid_from_height <= owned_occurrence.height <= (intent.valid_through_height):
        raise ValueError("authenticated intent occurrence height is outside validity")
    return AuthenticatedEconomicCommandV1(
        _AUTHENTICATED_COMMAND_TOKEN,
        _AuthenticatedCommandFieldsV1(
            occurrence=owned_occurrence,
            occurrence_id=owned_occurrence.occurrence_id,
            authenticated_intent_binding_root=authenticated_intent.binding_root,
            authentication_message_digest=(authenticated_intent.authentication_message_digest),
        ),
    )


def _authenticated_intent_v1(
    candidate: EconomicCommandAuthenticationCandidateV1,
    authorization: EconomicCommandAuthorizationV1,
    release: EconomicCommandSignatureVerifierReleaseV1,
    signature_verifier: BoundEconomicCommandSignatureVerifierV1,
    message_bytes: bytes,
) -> AuthenticatedEconomicCommandIntentV1:
    intent = candidate.intent
    envelope = candidate.envelope
    return AuthenticatedEconomicCommandIntentV1(
        _AUTHENTICATED_INTENT_TOKEN,
        _AuthenticatedIntentFieldsV1(
            intent=intent,
            intent_id=intent.intent_id,
            policy_registry_root=candidate.policy_registry.registry_root,
            authorization_registry_root=candidate.authorization_registry.registry_root,
            authorization_id=authorization.authorization_id,
            verifier_registry_root=candidate.profile.verifier_registry_root,
            signature_verifier_registry_root=(candidate.signature_verifier_registry.registry_root),
            signature_verifier_release_id=release.release_id,
            signature_verifier_deployment_binding_root=(signature_verifier.binding_root),
            command_body_bytes_digest=_sha256_root(envelope.command_body_bytes),
            authentication_message_digest=_sha256_root(message_bytes),
            signature_digest=_sha256_root(envelope.signature_bytes),
        ),
    )


def _validate_authorization_for_intent_v1(
    intent: EconomicCommandIntentV1,
    envelope: EconomicCommandAuthenticationEnvelopeV1,
    authorization: EconomicCommandAuthorizationV1,
) -> None:
    if not authorization.enabled:
        raise ValueError("command authorization is disabled")
    if authorization.signer_public_key != envelope.signer_public_key:
        raise ValueError("command authentication signer public key mismatch")
    if authorization.signature_algorithm != envelope.signature_algorithm:
        raise ValueError("command authentication signature algorithm mismatch")
    if not authorization.min_nonce <= intent.nonce <= authorization.max_nonce:
        raise ValueError("command authorization nonce is outside its interval")
    if intent.valid_from_height < authorization.valid_from_height or (
        intent.valid_through_height > authorization.valid_through_height
    ):
        raise ValueError("command intent validity exceeds its authorization interval")


def _select_authorization_v1(
    candidate: EconomicCommandAuthenticationCandidateV1,
) -> EconomicCommandAuthorizationV1:
    profile = candidate.profile
    intent = candidate.intent
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("command authentication requires an ACTIVE profile")
    if profile.policy_registry_root != candidate.policy_registry.registry_root:
        raise ValueError("command authentication policy registry root mismatch")
    binding = candidate.policy_registry.require_binding(
        policy_kind=ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
        command_kind=intent.command_kind,
    )
    if binding.policy_root != candidate.authorization_registry.registry_root:
        raise ValueError("command authorization registry is not profile governed")
    if intent.profile_root != profile.profile_id:
        raise ValueError("command authentication intent profile mismatch")
    profile.route_registry.route_for_command(
        intent.command_kind,
        claimed_route_release_id=intent.route_release_id,
    )
    if (
        hash_economic_command_body_bytes_v1(candidate.envelope.command_body_bytes)
        != intent.command_body_hash
    ):
        raise ValueError("command authentication body hash mismatch")
    return candidate.authorization_registry.authorization_for_fields(
        command_kind=intent.command_kind,
        route_release_id=intent.route_release_id,
        subject_id=intent.subject_id,
        grant_root=intent.grant_root,
        signer_key_id=candidate.envelope.signer_key_id,
    )


def _select_signature_verifier_release_v1(
    candidate: EconomicCommandAuthenticationCandidateV1,
) -> EconomicCommandSignatureVerifierReleaseV1:
    return select_profile_governed_command_signature_verifier_release_v1(
        policy_registry=candidate.policy_registry,
        verifier_registry=candidate.signature_verifier_registry,
        command_kind=candidate.intent.command_kind,
        signature_algorithm=candidate.envelope.signature_algorithm,
        signer_public_key=candidate.envelope.signer_public_key,
        signature_bytes=candidate.envelope.signature_bytes,
    )


def _sha256_root(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


__all__ = [
    "AuthenticatedEconomicCommandIntentV1",
    "AuthenticatedEconomicCommandV1",
    "ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1",
    "ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1",
    "EconomicCommandAuthenticationCandidateV1",
    "EconomicCommandAuthenticationEnvelopeV1",
    "EconomicCommandAuthorizationRegistryV1",
    "EconomicCommandAuthorizationV1",
    "EconomicCommandIntentV1",
    "BoundEconomicCommandSignatureVerifierV1",
    "authenticate_economic_command_intent_v1",
    "bind_authenticated_intent_to_occurrence_v1",
    "economic_command_authentication_message_bytes_v1",
]
