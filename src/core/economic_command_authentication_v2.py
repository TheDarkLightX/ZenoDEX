"""Pure V2 signing-message preparation and sequenced-occurrence binding.

The functions here select existing V1 governance records and construct plain
bytes for an external verifier.  They neither verify a signature nor create an
authentication witness or runtime admission authority.
"""

from __future__ import annotations

import hashlib
from typing import Final

from ..state.canonical import domain_sep_bytes
from .economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationEnvelopeV1,
)
from .economic_command_authentication_types_v2 import (
    ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2,
    EconomicCommandAuthenticationCandidateV2,
    EconomicCommandIntentV2,
    snapshot_command_authentication_candidate_v2,
    snapshot_economic_command_intent_v2,
)
from .economic_command_authorization_registry_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    EconomicCommandAuthorizationV1,
)
from .economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierReleaseV1,
    EconomicCommandSignatureVerifierSelectionPurposeV1,
    select_profile_governed_command_signature_verifier_release_v1,
)
from .global_economic_proof_v2 import EconomicCommandOccurrenceV2, _snapshot_occurrence_v2
from .global_settlement_primitives_v2 import (
    canonical_global_bytes_v2,
    hash_economic_command_body_bytes_v2,
    hash_global_v2,
)
from .global_settlement_types_v1 import ProfileStatusV1

_AUTHENTICATION_MESSAGE_DOMAIN_V2: Final = "economic-command-intent-authentication-message-v2"
_INTENT_FIELDS_V2: Final = (
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
_MESSAGE_FIELDS_V2: Final = (
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
ECONOMIC_COMMAND_AUTHENTICATION_MESSAGE_SCHEMA_ROOT_V2: Final = hash_global_v2(
    "economic-command-intent-authentication-schema-v2",
    {
        "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2,
        "message_domain": _AUTHENTICATION_MESSAGE_DOMAIN_V2,
        "intent_fields": _INTENT_FIELDS_V2,
        "message_fields": _MESSAGE_FIELDS_V2,
    },
)


def prepare_isolated_economic_command_authentication_v2(
    candidate: EconomicCommandAuthenticationCandidateV2,
) -> tuple[
    EconomicCommandAuthenticationCandidateV2,
    EconomicCommandSignatureVerifierReleaseV1,
    bytes,
]:
    """Own a V2 request and prepare the isolated-verifier message bytes."""

    owned = snapshot_command_authentication_candidate_v2(candidate)
    authorization = _select_authorization_v2(owned)
    _validate_authorization_for_intent_v2(owned.intent, owned.envelope, authorization)
    release = _select_isolated_signature_verifier_release_v2(owned)
    return owned, release, _authentication_message_bytes_v2(owned, authorization, release)


def require_economic_command_intent_occurrence_v2(
    intent: EconomicCommandIntentV2,
    occurrence: EconomicCommandOccurrenceV2,
) -> None:
    """Require an exact sequenced occurrence for a previously signed V2 intent."""

    owned_intent = snapshot_economic_command_intent_v2(intent)
    owned_occurrence = _snapshot_occurrence_v2(occurrence)
    signed_fields = (
        ("chain", owned_intent.chain_id, owned_occurrence.chain_id),
        ("deployment", owned_intent.deployment_root, owned_occurrence.deployment_root),
        ("profile", owned_intent.profile_root, owned_occurrence.profile_root),
        ("command kind", owned_intent.command_kind, owned_occurrence.command_kind),
        ("command body", owned_intent.command_body_hash, owned_occurrence.command_body_hash),
        ("route", owned_intent.route_release_id, owned_occurrence.route_release_id),
        ("subject", owned_intent.subject_id, owned_occurrence.subject_id),
        ("grant", owned_intent.grant_root, owned_occurrence.grant_root),
        ("nonce", owned_intent.nonce, owned_occurrence.nonce),
        (
            "consumed objects",
            owned_intent.consumed_object_ids,
            owned_occurrence.consumed_object_ids,
        ),
    )
    for label, expected, actual in signed_fields:
        if type(expected) is not type(actual) or expected != actual:
            raise ValueError(f"economic command intent occurrence {label} mismatch")
    if not (
        owned_intent.valid_from_height
        <= owned_occurrence.height
        <= owned_intent.valid_through_height
    ):
        raise ValueError("economic command intent occurrence height is outside validity")


def _select_authorization_v2(
    candidate: EconomicCommandAuthenticationCandidateV2,
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
    if hash_economic_command_body_bytes_v2(candidate.envelope.command_body_bytes) != (
        intent.command_body_hash
    ):
        raise ValueError("command authentication body hash mismatch")
    return candidate.authorization_registry.authorization_for_fields(
        command_kind=intent.command_kind,
        route_release_id=intent.route_release_id,
        subject_id=intent.subject_id,
        grant_root=intent.grant_root,
        signer_key_id=candidate.envelope.signer_key_id,
    )


def _validate_authorization_for_intent_v2(
    intent: EconomicCommandIntentV2,
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


def _select_isolated_signature_verifier_release_v2(
    candidate: EconomicCommandAuthenticationCandidateV2,
) -> EconomicCommandSignatureVerifierReleaseV1:
    release = select_profile_governed_command_signature_verifier_release_v1(
        policy_registry=candidate.policy_registry,
        verifier_registry=candidate.signature_verifier_registry,
        command_kind=candidate.intent.command_kind,
        signature_algorithm=candidate.envelope.signature_algorithm,
        signer_public_key=candidate.envelope.signer_public_key,
        signature_bytes=candidate.envelope.signature_bytes,
        selection_purpose=(
            EconomicCommandSignatureVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
        ),
    )
    if release.message_schema_root != ECONOMIC_COMMAND_AUTHENTICATION_MESSAGE_SCHEMA_ROOT_V2:
        raise ValueError("command signature verifier message schema root mismatch")
    return release


def _authentication_message_bytes_v2(
    candidate: EconomicCommandAuthenticationCandidateV2,
    authorization: EconomicCommandAuthorizationV1,
    release: EconomicCommandSignatureVerifierReleaseV1,
) -> bytes:
    body = {
        "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2,
        "policy_registry_root": candidate.policy_registry.registry_root,
        "authorization_registry_root": candidate.authorization_registry.registry_root,
        "authorization_id": authorization.authorization_id,
        "verifier_registry_root": candidate.profile.verifier_registry_root,
        "signature_verifier_registry_root": candidate.signature_verifier_registry.registry_root,
        "signature_verifier_release_id": release.release_id,
        "intent": candidate.intent,
        "command_body_bytes_digest": _raw_sha256_root(candidate.envelope.command_body_bytes),
        "signature_algorithm": candidate.envelope.signature_algorithm,
        "signer_key_id": candidate.envelope.signer_key_id,
        "signer_public_key": candidate.envelope.signer_public_key,
    }
    return domain_sep_bytes(
        _AUTHENTICATION_MESSAGE_DOMAIN_V2,
        version=2,
    ) + canonical_global_bytes_v2(body)


def _raw_sha256_root(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


__all__ = [
    "ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2",
    "ECONOMIC_COMMAND_AUTHENTICATION_MESSAGE_SCHEMA_ROOT_V2",
    "EconomicCommandAuthenticationCandidateV2",
    "EconomicCommandIntentV2",
    "prepare_isolated_economic_command_authentication_v2",
    "require_economic_command_intent_occurrence_v2",
]
