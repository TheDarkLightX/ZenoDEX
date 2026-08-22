"""Process-local opaque witnesses for authenticated economic commands."""

from __future__ import annotations

from dataclasses import dataclass
from threading import Lock
from weakref import WeakKeyDictionary

from .economic_command_authentication_snapshot_v1 import (
    snapshot_economic_command_intent_v1,
)
from .economic_command_authentication_types_v1 import EconomicCommandIntentV1
from .economic_command_authorization_registry_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
)
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_economic_refinement_snapshot_v1 import _snapshot_occurrence_v1
from .global_settlement_types_v1 import _require_root, hash_global_v1

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
    signature_verifier_deployment_binding_root: str
    command_body_bytes_digest: str
    authentication_message_digest: str
    signature_digest: str


class AuthenticatedEconomicCommandIntentV1:
    """Data-slot-free handle for verifier-owned intent authority."""

    __slots__ = ("__weakref__",)

    def __init__(self, token: object, fields: _AuthenticatedIntentFieldsV1) -> None:
        if token is not _AUTHENTICATED_INTENT_TOKEN:
            raise TypeError("AuthenticatedEconomicCommandIntentV1 is verifier-constructed")
        _register_authenticated_intent_authority_v1(self, fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("AuthenticatedEconomicCommandIntentV1 is immutable")

    @property
    def intent(self) -> EconomicCommandIntentV1:
        authority = _snapshot_authenticated_intent_authority_v1(
            _authenticated_intent_authority_v1(self)
        )
        return snapshot_economic_command_intent_v1(authority.intent)

    @property
    def authentication_message_digest(self) -> str:
        return _snapshot_authenticated_intent_authority_v1(
            _authenticated_intent_authority_v1(self)
        ).authentication_message_digest

    @property
    def binding_root(self) -> str:
        return _authenticated_intent_binding_root_v1(
            _snapshot_authenticated_intent_authority_v1(
                _authenticated_intent_authority_v1(self)
            )
        )


@dataclass(frozen=True, slots=True)
class _AuthenticatedCommandFieldsV1:
    occurrence: EconomicCommandOccurrenceV1
    occurrence_id: str
    authenticated_intent_binding_root: str
    authentication_message_digest: str


class AuthenticatedEconomicCommandV1:
    """Data-slot-free handle for binder-owned occurrence authority."""

    __slots__ = ("__weakref__",)

    def __init__(self, token: object, fields: _AuthenticatedCommandFieldsV1) -> None:
        if token is not _AUTHENTICATED_COMMAND_TOKEN:
            raise TypeError("AuthenticatedEconomicCommandV1 is binder-constructed")
        _register_authenticated_command_authority_v1(self, fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("AuthenticatedEconomicCommandV1 is immutable")

    @property
    def occurrence(self) -> EconomicCommandOccurrenceV1:
        authority = _snapshot_authenticated_command_authority_v1(
            _authenticated_command_authority_v1(self)
        )
        return _snapshot_occurrence_v1(authority.occurrence)

    @property
    def occurrence_id(self) -> str:
        return _snapshot_authenticated_command_authority_v1(
            _authenticated_command_authority_v1(self)
        ).occurrence_id

    @property
    def authentication_message_digest(self) -> str:
        return _snapshot_authenticated_command_authority_v1(
            _authenticated_command_authority_v1(self)
        ).authentication_message_digest

    @property
    def binding_root(self) -> str:
        return _authenticated_command_binding_root_v1(
            _snapshot_authenticated_command_authority_v1(
                _authenticated_command_authority_v1(self)
            )
        )


_AUTHENTICATED_INTENT_AUTHORITY_LOCK_V1 = Lock()
_AUTHENTICATED_INTENT_AUTHORITIES_V1: WeakKeyDictionary[
    AuthenticatedEconomicCommandIntentV1,
    _AuthenticatedIntentFieldsV1,
] = WeakKeyDictionary()
_AUTHENTICATED_COMMAND_AUTHORITY_LOCK_V1 = Lock()
_AUTHENTICATED_COMMAND_AUTHORITIES_V1: WeakKeyDictionary[
    AuthenticatedEconomicCommandV1,
    _AuthenticatedCommandFieldsV1,
] = WeakKeyDictionary()


def _register_authenticated_intent_authority_v1(
    witness: AuthenticatedEconomicCommandIntentV1,
    authority: _AuthenticatedIntentFieldsV1,
) -> None:
    owned = _snapshot_authenticated_intent_authority_v1(authority)
    with _AUTHENTICATED_INTENT_AUTHORITY_LOCK_V1:
        if witness in _AUTHENTICATED_INTENT_AUTHORITIES_V1:
            raise RuntimeError("authenticated command intent is already registered")
        _AUTHENTICATED_INTENT_AUTHORITIES_V1[witness] = owned


def _authenticated_intent_authority_v1(
    witness: AuthenticatedEconomicCommandIntentV1,
) -> _AuthenticatedIntentFieldsV1:
    if type(witness) is not AuthenticatedEconomicCommandIntentV1:
        raise TypeError("authenticated command intent type is not closed")
    with _AUTHENTICATED_INTENT_AUTHORITY_LOCK_V1:
        authority = _AUTHENTICATED_INTENT_AUTHORITIES_V1.get(witness)
    if authority is None:
        raise TypeError("authenticated command intent is not verifier-registered")
    return authority


def _register_authenticated_command_authority_v1(
    witness: AuthenticatedEconomicCommandV1,
    authority: _AuthenticatedCommandFieldsV1,
) -> None:
    owned = _snapshot_authenticated_command_authority_v1(authority)
    with _AUTHENTICATED_COMMAND_AUTHORITY_LOCK_V1:
        if witness in _AUTHENTICATED_COMMAND_AUTHORITIES_V1:
            raise RuntimeError("authenticated command is already registered")
        _AUTHENTICATED_COMMAND_AUTHORITIES_V1[witness] = owned


def _authenticated_command_authority_v1(
    witness: AuthenticatedEconomicCommandV1,
) -> _AuthenticatedCommandFieldsV1:
    if type(witness) is not AuthenticatedEconomicCommandV1:
        raise TypeError("authenticated command type is not closed")
    with _AUTHENTICATED_COMMAND_AUTHORITY_LOCK_V1:
        authority = _AUTHENTICATED_COMMAND_AUTHORITIES_V1.get(witness)
    if authority is None:
        raise TypeError("authenticated command is not binder-registered")
    return authority


def _snapshot_authenticated_intent_authority_v1(
    authority: _AuthenticatedIntentFieldsV1,
) -> _AuthenticatedIntentFieldsV1:
    if type(authority) is not _AuthenticatedIntentFieldsV1:
        raise TypeError("authenticated command intent authority must be exactly typed")
    intent = snapshot_economic_command_intent_v1(authority.intent)
    roots = (
        ("intent id", authority.intent_id),
        ("policy registry", authority.policy_registry_root),
        ("authorization registry", authority.authorization_registry_root),
        ("authorization id", authority.authorization_id),
        ("verifier registry", authority.verifier_registry_root),
        ("signature verifier registry", authority.signature_verifier_registry_root),
        ("signature verifier release", authority.signature_verifier_release_id),
        (
            "signature verifier deployment binding",
            authority.signature_verifier_deployment_binding_root,
        ),
        ("command body bytes digest", authority.command_body_bytes_digest),
        ("authentication message digest", authority.authentication_message_digest),
        ("signature digest", authority.signature_digest),
    )
    for label, root in roots:
        if type(root) is not str:
            raise TypeError(f"authenticated command intent {label} must be exact str")
        _require_root(root, name=f"authenticated command intent {label}")
    if intent.intent_id != authority.intent_id:
        raise ValueError("authenticated command intent baseline root mismatch")
    return _AuthenticatedIntentFieldsV1(
        intent=intent,
        intent_id=authority.intent_id,
        policy_registry_root=authority.policy_registry_root,
        authorization_registry_root=authority.authorization_registry_root,
        authorization_id=authority.authorization_id,
        verifier_registry_root=authority.verifier_registry_root,
        signature_verifier_registry_root=authority.signature_verifier_registry_root,
        signature_verifier_release_id=authority.signature_verifier_release_id,
        signature_verifier_deployment_binding_root=(
            authority.signature_verifier_deployment_binding_root
        ),
        command_body_bytes_digest=authority.command_body_bytes_digest,
        authentication_message_digest=authority.authentication_message_digest,
        signature_digest=authority.signature_digest,
    )


def _snapshot_authenticated_command_authority_v1(
    authority: _AuthenticatedCommandFieldsV1,
) -> _AuthenticatedCommandFieldsV1:
    if type(authority) is not _AuthenticatedCommandFieldsV1:
        raise TypeError("authenticated command authority must be exactly typed")
    occurrence = _snapshot_occurrence_v1(authority.occurrence)
    for label, root in (
        ("occurrence id", authority.occurrence_id),
        ("intent binding root", authority.authenticated_intent_binding_root),
        ("authentication message digest", authority.authentication_message_digest),
    ):
        if type(root) is not str:
            raise TypeError(f"authenticated command {label} must be exact str")
        _require_root(root, name=f"authenticated command {label}")
    if occurrence.occurrence_id != authority.occurrence_id:
        raise ValueError("authenticated command occurrence baseline root mismatch")
    return _AuthenticatedCommandFieldsV1(
        occurrence=occurrence,
        occurrence_id=authority.occurrence_id,
        authenticated_intent_binding_root=authority.authenticated_intent_binding_root,
        authentication_message_digest=authority.authentication_message_digest,
    )


def _authenticated_intent_binding_root_v1(authority: _AuthenticatedIntentFieldsV1) -> str:
    return hash_global_v1(
        "authenticated-economic-command-intent-v1",
        {
            "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
            "intent_id": authority.intent_id,
            "policy_registry_root": authority.policy_registry_root,
            "authorization_registry_root": authority.authorization_registry_root,
            "authorization_id": authority.authorization_id,
            "verifier_registry_root": authority.verifier_registry_root,
            "signature_verifier_registry_root": authority.signature_verifier_registry_root,
            "signature_verifier_release_id": authority.signature_verifier_release_id,
            "signature_verifier_deployment_binding_root": (
                authority.signature_verifier_deployment_binding_root
            ),
            "command_body_bytes_digest": authority.command_body_bytes_digest,
            "authentication_message_digest": authority.authentication_message_digest,
            "signature_digest": authority.signature_digest,
        },
    )


def _authenticated_command_binding_root_v1(authority: _AuthenticatedCommandFieldsV1) -> str:
    return hash_global_v1(
        "authenticated-economic-command-v1",
        {
            "schema": ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1,
            "occurrence_id": authority.occurrence_id,
            "authenticated_intent_binding_root": authority.authenticated_intent_binding_root,
        },
    )


__all__ = [
    "AuthenticatedEconomicCommandIntentV1",
    "AuthenticatedEconomicCommandV1",
]
