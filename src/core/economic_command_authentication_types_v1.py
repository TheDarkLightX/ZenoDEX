"""Owned value types for two-stage economic-command authentication."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from .economic_command_authorization_registry_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
    EconomicCommandAuthorizationRegistryV1,
)
from .economic_command_signature_verifier_registry_v1 import (
    MAX_COMMAND_SIGNATURE_BYTES_V1,
    EconomicCommandSignatureVerifierRegistryV1,
)
from .global_settlement_types_v1 import (
    MAX_JOURNAL_BYTES_V1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    _require_nonnegative_int,
    _require_root,
    _require_sorted_unique_tokens,
    _require_token,
    hash_global_v1,
)


@dataclass(frozen=True, slots=True)
class EconomicCommandIntentV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    command_kind: str
    command_body_hash: str
    route_release_id: str
    subject_id: str
    grant_root: str
    nonce: int
    consumed_object_ids: tuple[str, ...]
    valid_from_height: int
    valid_through_height: int

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="command intent chain id")
        _require_root(self.deployment_root, name="command intent deployment root")
        _require_root(self.profile_root, name="command intent profile root")
        _require_token(self.command_kind, name="command intent kind")
        _require_root(self.command_body_hash, name="command intent body hash")
        _require_root(self.route_release_id, name="command intent route")
        _require_token(self.subject_id, name="command intent subject")
        _require_root(self.grant_root, name="command intent grant")
        _require_nonnegative_int(self.nonce, name="command intent nonce")
        _require_sorted_unique_tokens(
            self.consumed_object_ids,
            name="command intent consumed object ids",
        )
        _require_nonnegative_int(
            self.valid_from_height,
            name="command intent valid-from height",
        )
        _require_nonnegative_int(
            self.valid_through_height,
            name="command intent valid-through height",
        )
        if self.valid_from_height > self.valid_through_height:
            raise ValueError("command intent height interval is inverted")

    @property
    def intent_id(self) -> str:
        return hash_global_v1("economic-command-intent-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "command_kind": self.command_kind,
            "command_body_hash": self.command_body_hash,
            "route_release_id": self.route_release_id,
            "subject_id": self.subject_id,
            "grant_root": self.grant_root,
            "nonce": self.nonce,
            "consumed_object_ids": self.consumed_object_ids,
            "valid_from_height": self.valid_from_height,
            "valid_through_height": self.valid_through_height,
        }


@dataclass(frozen=True, slots=True)
class EconomicCommandAuthenticationEnvelopeV1:
    command_body_bytes: bytes
    signer_key_id: str
    signer_public_key: str
    signature_algorithm: str
    signature_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.command_body_bytes) is not bytes:
            raise TypeError("command authentication body must be exact bytes")
        if not 1 <= len(self.command_body_bytes) <= MAX_JOURNAL_BYTES_V1:
            raise ValueError("command authentication body byte length is out of bounds")
        _require_token(self.signer_key_id, name="command authentication signer key id")
        _require_token(self.signer_public_key, name="command authentication public key")
        _require_token(self.signature_algorithm, name="command authentication algorithm")
        if type(self.signature_bytes) is not bytes:
            raise TypeError("command authentication signature must be exact bytes")
        if not 1 <= len(self.signature_bytes) <= MAX_COMMAND_SIGNATURE_BYTES_V1:
            raise ValueError("command authentication signature byte length is out of bounds")


@dataclass(frozen=True, slots=True)
class EconomicCommandAuthenticationCandidateV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    authorization_registry: EconomicCommandAuthorizationRegistryV1
    signature_verifier_registry: EconomicCommandSignatureVerifierRegistryV1
    intent: EconomicCommandIntentV1
    envelope: EconomicCommandAuthenticationEnvelopeV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "profile"),
            (self.policy_registry, EconomicPolicyRegistryV1, "policy registry"),
            (
                self.authorization_registry,
                EconomicCommandAuthorizationRegistryV1,
                "authorization registry",
            ),
            (
                self.signature_verifier_registry,
                EconomicCommandSignatureVerifierRegistryV1,
                "signature verifier registry",
            ),
            (self.intent, EconomicCommandIntentV1, "intent"),
            (self.envelope, EconomicCommandAuthenticationEnvelopeV1, "envelope"),
        )
        for value, expected_type, label in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"command authentication candidate {label} must be exactly typed")


class EconomicCommandSignatureVerifierV1(Protocol):
    @property
    def verifier_release_id(self) -> str: ...

    def verify_command_signature(
        self,
        *,
        signature_algorithm: str,
        signer_public_key: str,
        message_bytes: bytes,
        signature_bytes: bytes,
    ) -> bool: ...


__all__ = [
    "EconomicCommandAuthenticationCandidateV1",
    "EconomicCommandAuthenticationEnvelopeV1",
    "EconomicCommandIntentV1",
    "EconomicCommandSignatureVerifierV1",
]
