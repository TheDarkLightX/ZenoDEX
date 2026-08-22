"""Governed signer authorizations for whole-economy command intents."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_settlement_types_v1 import (
    _require_bool,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1: Final = (
    "zenodex/economic-command-authentication/v1"
)
ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1: Final = (
    "command_authentication_registry"
)
MAX_COMMAND_AUTHORIZATIONS_V1: Final = 1_024


@dataclass(frozen=True, slots=True, order=True)
class EconomicCommandAuthorizationV1:
    command_kind: str
    subject_id: str
    grant_root: str
    route_release_id: str
    signer_key_id: str
    signer_public_key: str
    signature_algorithm: str
    valid_from_height: int
    valid_through_height: int
    min_nonce: int
    max_nonce: int
    enabled: bool

    def __post_init__(self) -> None:
        _require_token(self.command_kind, name="command authorization kind")
        _require_token(self.subject_id, name="command authorization subject")
        _require_root(self.grant_root, name="command authorization grant")
        _require_root(self.route_release_id, name="command authorization route")
        _require_token(self.signer_key_id, name="command authorization signer key id")
        _require_token(
            self.signer_public_key,
            name="command authorization signer public key",
        )
        _require_token(
            self.signature_algorithm,
            name="command authorization signature algorithm",
        )
        _require_nonnegative_int(
            self.valid_from_height,
            name="command authorization valid-from height",
        )
        _require_nonnegative_int(
            self.valid_through_height,
            name="command authorization valid-through height",
        )
        _require_nonnegative_int(self.min_nonce, name="command authorization min nonce")
        _require_nonnegative_int(self.max_nonce, name="command authorization max nonce")
        _require_bool(self.enabled, name="command authorization enabled")
        if self.valid_from_height > self.valid_through_height:
            raise ValueError("command authorization height interval is inverted")
        if self.min_nonce > self.max_nonce:
            raise ValueError("command authorization nonce interval is inverted")

    @property
    def key(self) -> tuple[str, str, str, str, str]:
        return (
            self.command_kind,
            self.subject_id,
            self.grant_root,
            self.route_release_id,
            self.signer_key_id,
        )

    @property
    def authorization_id(self) -> str:
        return hash_global_v1("economic-command-authorization-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
            "command_kind": self.command_kind,
            "subject_id": self.subject_id,
            "grant_root": self.grant_root,
            "route_release_id": self.route_release_id,
            "signer_key_id": self.signer_key_id,
            "signer_public_key": self.signer_public_key,
            "signature_algorithm": self.signature_algorithm,
            "valid_from_height": self.valid_from_height,
            "valid_through_height": self.valid_through_height,
            "min_nonce": self.min_nonce,
            "max_nonce": self.max_nonce,
            "enabled": self.enabled,
        }


@dataclass(frozen=True, slots=True)
class EconomicCommandAuthorizationRegistryV1:
    authorizations: tuple[EconomicCommandAuthorizationV1, ...]

    def __post_init__(self) -> None:
        if type(self.authorizations) is not tuple:
            raise TypeError("command authorization registry must be an exact tuple")
        if not 1 <= len(self.authorizations) <= MAX_COMMAND_AUTHORIZATIONS_V1:
            raise ValueError("command authorization registry requires 1 to 1024 entries")
        if any(
            type(authorization) is not EconomicCommandAuthorizationV1
            for authorization in self.authorizations
        ):
            raise TypeError("command authorization registry contains an invalid entry")
        keys = tuple(authorization.key for authorization in self.authorizations)
        if keys != tuple(sorted(set(keys))):
            raise ValueError("command authorization registry must be sorted and unique")

    @property
    def registry_root(self) -> str:
        return hash_global_v1(
            "economic-command-authorization-registry-v1",
            self.to_canonical(),
        )

    def authorization_for(
        self,
        occurrence: EconomicCommandOccurrenceV1,
        *,
        signer_key_id: str,
    ) -> EconomicCommandAuthorizationV1:
        return self.authorization_for_fields(
            command_kind=occurrence.command_kind,
            subject_id=occurrence.subject_id,
            grant_root=occurrence.grant_root,
            route_release_id=occurrence.route_release_id,
            signer_key_id=signer_key_id,
        )

    def authorization_for_fields(
        self,
        *,
        command_kind: str,
        subject_id: str,
        grant_root: str,
        route_release_id: str,
        signer_key_id: str,
    ) -> EconomicCommandAuthorizationV1:
        _require_token(command_kind, name="command authorization kind")
        _require_token(subject_id, name="command authorization subject")
        _require_root(grant_root, name="command authorization grant")
        _require_root(route_release_id, name="command authorization route")
        _require_token(signer_key_id, name="command authentication signer key id")
        key = (
            command_kind,
            subject_id,
            grant_root,
            route_release_id,
            signer_key_id,
        )
        for authorization in self.authorizations:
            if authorization.key == key:
                return authorization
        raise ValueError("command authorization is absent from the governed registry")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
            "authorizations": self.authorizations,
        }


__all__ = [
    "ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1",
    "ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1",
    "EconomicCommandAuthorizationRegistryV1",
    "EconomicCommandAuthorizationV1",
]
