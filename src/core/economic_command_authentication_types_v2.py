"""Owned V2 input values for isolated economic-command authentication.

These values bind a signer request to V2 command-body bytes.  They do not
verify a signature, create authority, or admit a command to any runtime.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .economic_command_authentication_snapshot_v1 import (
    _snapshot_authorization_registry_v1,
    _snapshot_envelope_v1,
    _snapshot_policy_registry_v1,
    _snapshot_signature_verifier_registry_v1,
)
from .economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationEnvelopeV1,
)
from .economic_command_authorization_registry_v1 import (
    EconomicCommandAuthorizationRegistryV1,
)
from .economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierRegistryV1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_settlement_primitives_v2 import (
    _require_nonnegative_int_v2,
    _require_root_v2,
    _require_sorted_unique_tokens_v2,
    _require_token_v2,
)
from .global_settlement_resource_limits_v2 import (
    MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2,
    require_raw_tuple_ceiling_v2,
)
from .global_settlement_types_v1 import EconomicPolicyRegistryV1, EconomicProfileSnapshotV1

ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2: Final = "zenodex/economic-command-authentication/v2"
MAX_ECONOMIC_COMMAND_INTENT_CONSUMED_OBJECT_IDS_V2: Final = (
    MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2
)


@dataclass(frozen=True, slots=True)
class EconomicCommandIntentV2:
    """The complete signer-owned V2 intent before a sequencer occurrence exists."""

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
        require_raw_tuple_ceiling_v2(
            self.consumed_object_ids,
            name="command intent consumed object ids",
            ceiling=MAX_ECONOMIC_COMMAND_INTENT_CONSUMED_OBJECT_IDS_V2,
        )
        _require_token_v2(self.chain_id, name="command intent chain id")
        _require_root_v2(self.deployment_root, name="command intent deployment root")
        _require_root_v2(self.profile_root, name="command intent profile root")
        _require_token_v2(self.command_kind, name="command intent kind")
        _require_root_v2(self.command_body_hash, name="command intent body hash")
        _require_root_v2(self.route_release_id, name="command intent route")
        _require_token_v2(self.subject_id, name="command intent subject")
        _require_root_v2(self.grant_root, name="command intent grant")
        _require_nonnegative_int_v2(self.nonce, name="command intent nonce")
        _require_sorted_unique_tokens_v2(
            self.consumed_object_ids,
            name="command intent consumed object ids",
        )
        _require_nonnegative_int_v2(
            self.valid_from_height,
            name="command intent valid-from height",
        )
        _require_nonnegative_int_v2(
            self.valid_through_height,
            name="command intent valid-through height",
        )
        if self.valid_from_height > self.valid_through_height:
            raise ValueError("command intent height interval is inverted")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2,
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
class EconomicCommandAuthenticationCandidateV2:
    """Plain V2 authentication inputs, with existing V1 governance records."""

    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    authorization_registry: EconomicCommandAuthorizationRegistryV1
    signature_verifier_registry: EconomicCommandSignatureVerifierRegistryV1
    intent: EconomicCommandIntentV2
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
            (self.intent, EconomicCommandIntentV2, "intent"),
            (self.envelope, EconomicCommandAuthenticationEnvelopeV1, "envelope"),
        )
        for value, expected_type, label in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"command authentication candidate {label} must be exactly typed")


def snapshot_economic_command_intent_v2(
    intent: EconomicCommandIntentV2,
) -> EconomicCommandIntentV2:
    """Copy an exact V2 intent after its bounded scalar fields are rechecked."""

    if type(intent) is not EconomicCommandIntentV2:
        raise TypeError("economic command intent must have the exact typed value")
    string_values = (
        intent.chain_id,
        intent.deployment_root,
        intent.profile_root,
        intent.command_kind,
        intent.command_body_hash,
        intent.route_release_id,
        intent.subject_id,
        intent.grant_root,
    )
    if any(type(value) is not str for value in string_values):
        raise TypeError("economic command intent token fields must be exact strings")
    integer_values = (
        intent.nonce,
        intent.valid_from_height,
        intent.valid_through_height,
    )
    if any(type(value) is not int for value in integer_values):
        raise TypeError("economic command intent numeric fields must be exact integers")
    require_raw_tuple_ceiling_v2(
        intent.consumed_object_ids,
        name="command intent consumed object ids",
        ceiling=MAX_ECONOMIC_COMMAND_INTENT_CONSUMED_OBJECT_IDS_V2,
    )
    if any(type(value) is not str for value in intent.consumed_object_ids):
        raise TypeError("economic command intent objects must be exact strings")
    return EconomicCommandIntentV2(
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


def snapshot_command_authentication_candidate_v2(
    candidate: EconomicCommandAuthenticationCandidateV2,
) -> EconomicCommandAuthenticationCandidateV2:
    """Own V2 intent inputs while reusing the established V1 registry snapshots."""

    if type(candidate) is not EconomicCommandAuthenticationCandidateV2:
        raise TypeError("command authentication candidate must have the exact type")
    return EconomicCommandAuthenticationCandidateV2(
        profile=snapshot_economic_profile_v1(candidate.profile),
        policy_registry=_snapshot_policy_registry_v1(candidate.policy_registry),
        authorization_registry=_snapshot_authorization_registry_v1(
            candidate.authorization_registry
        ),
        signature_verifier_registry=_snapshot_signature_verifier_registry_v1(
            candidate.signature_verifier_registry
        ),
        intent=snapshot_economic_command_intent_v2(candidate.intent),
        envelope=_snapshot_envelope_v1(candidate.envelope),
    )


__all__ = [
    "ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2",
    "MAX_ECONOMIC_COMMAND_INTENT_CONSUMED_OBJECT_IDS_V2",
    "EconomicCommandAuthenticationCandidateV2",
    "EconomicCommandIntentV2",
    "snapshot_command_authentication_candidate_v2",
    "snapshot_economic_command_intent_v2",
]
