"""Two-stage authentication for whole-economy command admission.

The user signs an economic intent before sequencing. A deterministic binder
later attaches the authenticated intent to the exact sequenced occurrence.
The injected signature verifier remains an outer release-selected dependency;
this functional core grants no publication authority by itself.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from ..state.canonical import domain_sep_bytes
from .economic_command_authentication_snapshot_v1 import (
    snapshot_command_authentication_candidate_v1,
    snapshot_economic_command_intent_v1,
)
from .economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationCandidateV1,
    EconomicCommandAuthenticationEnvelopeV1,
    EconomicCommandIntentV1,
    EconomicCommandSignatureVerifierV1,
)
from .economic_command_authorization_registry_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
    EconomicCommandAuthorizationRegistryV1,
    EconomicCommandAuthorizationV1,
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
    hash_global_v1,
)

_AUTHENTICATED_INTENT_TOKEN = object()
_AUTHENTICATED_COMMAND_TOKEN = object()


@dataclass(frozen=True, slots=True)
class _AuthenticatedIntentFieldsV1:
    intent: EconomicCommandIntentV1
    intent_id: str
    policy_registry_root: str
    authorization_registry_root: str
    authorization_id: str
    verifier_registry_root: str
    signature_verifier_registry_root: str
    signature_verifier_release_id: str
    command_body_bytes_digest: str
    authentication_message_digest: str
    signature_digest: str


class AuthenticatedEconomicCommandIntentV1:
    _fields: _AuthenticatedIntentFieldsV1
    __slots__ = ("_fields",)

    def __init__(self, token: object, fields: _AuthenticatedIntentFieldsV1) -> None:
        if token is not _AUTHENTICATED_INTENT_TOKEN:
            raise TypeError("AuthenticatedEconomicCommandIntentV1 is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("AuthenticatedEconomicCommandIntentV1 is immutable")

    @property
    def intent(self) -> EconomicCommandIntentV1:
        if self._fields.intent.intent_id != self._fields.intent_id:
            raise ValueError("authenticated command intent was mutated")
        return snapshot_economic_command_intent_v1(self._fields.intent)

    @property
    def authentication_message_digest(self) -> str:
        return self._fields.authentication_message_digest

    @property
    def binding_root(self) -> str:
        _ = self.intent
        return hash_global_v1(
            "authenticated-economic-command-intent-v1",
            {
                "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
                "intent_id": self._fields.intent_id,
                "policy_registry_root": self._fields.policy_registry_root,
                "authorization_registry_root": self._fields.authorization_registry_root,
                "authorization_id": self._fields.authorization_id,
                "verifier_registry_root": self._fields.verifier_registry_root,
                "signature_verifier_registry_root": (self._fields.signature_verifier_registry_root),
                "signature_verifier_release_id": (self._fields.signature_verifier_release_id),
                "command_body_bytes_digest": self._fields.command_body_bytes_digest,
                "authentication_message_digest": self._fields.authentication_message_digest,
                "signature_digest": self._fields.signature_digest,
            },
        )


@dataclass(frozen=True, slots=True)
class _AuthenticatedCommandFieldsV1:
    occurrence: EconomicCommandOccurrenceV1
    occurrence_id: str
    authenticated_intent_binding_root: str
    authentication_message_digest: str


class AuthenticatedEconomicCommandV1:
    _fields: _AuthenticatedCommandFieldsV1
    __slots__ = ("_fields",)

    def __init__(self, token: object, fields: _AuthenticatedCommandFieldsV1) -> None:
        if token is not _AUTHENTICATED_COMMAND_TOKEN:
            raise TypeError("AuthenticatedEconomicCommandV1 is binder-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("AuthenticatedEconomicCommandV1 is immutable")

    @property
    def occurrence(self) -> EconomicCommandOccurrenceV1:
        if self._fields.occurrence.occurrence_id != self._fields.occurrence_id:
            raise ValueError("authenticated command occurrence was mutated")
        return _snapshot_occurrence_v1(self._fields.occurrence)

    @property
    def occurrence_id(self) -> str:
        _ = self.occurrence
        return self._fields.occurrence_id

    @property
    def authentication_message_digest(self) -> str:
        return self._fields.authentication_message_digest

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "authenticated-economic-command-v1",
            {
                "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
                "occurrence_id": self.occurrence_id,
                "authenticated_intent_binding_root": (
                    self._fields.authenticated_intent_binding_root
                ),
            },
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
    signature_verifier: EconomicCommandSignatureVerifierV1,
) -> AuthenticatedEconomicCommandIntentV1:
    owned = snapshot_command_authentication_candidate_v1(candidate)
    authorization = _select_authorization_v1(owned)
    _validate_authorization_for_intent_v1(owned.intent, owned.envelope, authorization)
    release = _select_signature_verifier_release_v1(owned)
    message_bytes = _authentication_message_bytes_v1(
        owned,
        authorization,
        release,
    )
    claimed_release_id = signature_verifier.verifier_release_id
    if type(claimed_release_id) is not str or claimed_release_id != release.release_id:
        raise ValueError("command signature verifier release mismatch")
    verified = signature_verifier.verify_command_signature(
        signature_algorithm=owned.envelope.signature_algorithm,
        signer_public_key=owned.envelope.signer_public_key,
        message_bytes=message_bytes,
        signature_bytes=owned.envelope.signature_bytes,
    )
    if verified is not True:
        raise ValueError("command authentication signature rejected")
    return _authenticated_intent_v1(owned, authorization, release, message_bytes)


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
    "EconomicCommandSignatureVerifierV1",
    "authenticate_economic_command_intent_v1",
    "bind_authenticated_intent_to_occurrence_v1",
    "economic_command_authentication_message_bytes_v1",
]
