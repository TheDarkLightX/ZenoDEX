"""Opaque process-local capability for a bound signature verifier backend."""

from __future__ import annotations

from dataclasses import dataclass
from threading import Lock
from typing import Final, Protocol
from weakref import WeakKeyDictionary

from .economic_command_signature_verifier_registry_v1 import (
    MAX_COMMAND_SIGNATURE_BYTES_V1,
)
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_JOURNAL_BYTES_V1,
    MAX_TOKEN_BYTES_V1,
    _require_positive_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

_DEPLOYMENT_BINDING_ROOT_DOMAIN_V1: Final = (
    "economic-command-signature-verifier-deployment-binding-v1"
)


class EconomicCommandSignatureVerifierBackendV1(Protocol):
    """Untrusted implementation port wrapped by a measured deployment binding."""

    def verify_command_signature(
        self,
        *,
        signature_algorithm: str,
        signer_public_key: str,
        message_bytes: bytes,
        signature_bytes: bytes,
    ) -> bool: ...


@dataclass(frozen=True, slots=True)
class _BoundVerifierAuthorityV1:
    release_id: str
    deployment_root: str
    profile_root: str
    implementation_root: str
    evidence_manifest_root: str
    backend_protocol_root: str
    signature_algorithm: str
    max_public_key_bytes: int
    max_signature_bytes: int
    backend: EconomicCommandSignatureVerifierBackendV1


_BOUND_VERIFIER_TOKEN_V1: Final = object()


class BoundEconomicCommandSignatureVerifierV1:
    """Data-slot-free handle for separately owned deployment authority."""

    __slots__ = ("__weakref__",)

    def __init__(self, token: object, authority: _BoundVerifierAuthorityV1) -> None:
        if token is not _BOUND_VERIFIER_TOKEN_V1:
            raise TypeError("bound command signature verifier must be loader-constructed")
        _register_bound_verifier_authority_v1(self, authority)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("bound command signature verifier is immutable")

    @property
    def release_id(self) -> str:
        return _bound_verifier_authority_v1(self).release_id

    @property
    def deployment_root(self) -> str:
        return _bound_verifier_authority_v1(self).deployment_root

    @property
    def profile_root(self) -> str:
        return _bound_verifier_authority_v1(self).profile_root

    @property
    def binding_root(self) -> str:
        return _bound_verifier_binding_root_v1(_bound_verifier_authority_v1(self))

    def require_binding(
        self,
        *,
        release_id: str,
        deployment_root: str,
        profile_root: str,
    ) -> None:
        authority = _snapshot_bound_verifier_authority_v1(
            _bound_verifier_authority_v1(self)
        )
        if type(release_id) is not str or release_id != authority.release_id:
            raise ValueError("command signature verifier release binding mismatch")
        if type(deployment_root) is not str or deployment_root != authority.deployment_root:
            raise ValueError("command signature verifier deployment binding mismatch")
        if type(profile_root) is not str or profile_root != authority.profile_root:
            raise ValueError("command signature verifier profile binding mismatch")

    def verify_command_signature(
        self,
        *,
        signature_algorithm: str,
        signer_public_key: str,
        message_bytes: bytes,
        signature_bytes: bytes,
    ) -> bool:
        authority = _snapshot_bound_verifier_authority_v1(
            _bound_verifier_authority_v1(self)
        )
        if type(signature_algorithm) is not str or (
            signature_algorithm != authority.signature_algorithm
        ):
            raise ValueError("command signature verifier algorithm binding mismatch")
        if type(signer_public_key) is not str:
            raise TypeError("command signature verifier public key must be exact str")
        if len(signer_public_key.encode("utf-8")) > authority.max_public_key_bytes:
            raise ValueError("command signature verifier public key exceeds bound ceiling")
        if type(message_bytes) is not bytes or not 1 <= len(message_bytes) <= MAX_JOURNAL_BYTES_V1:
            raise ValueError("command signature verifier message byte length is out of bounds")
        if type(signature_bytes) is not bytes or not (
            1 <= len(signature_bytes) <= authority.max_signature_bytes
        ):
            raise ValueError("command signature verifier signature byte length is out of bounds")
        baseline = _bound_verifier_authority_baseline_v1(authority)
        backend = authority.backend
        result = backend.verify_command_signature(
            signature_algorithm=signature_algorithm,
            signer_public_key=signer_public_key,
            message_bytes=message_bytes,
            signature_bytes=signature_bytes,
        )
        retained = _snapshot_bound_verifier_authority_v1(
            _bound_verifier_authority_v1(self)
        )
        if retained.backend is not backend or (
            _bound_verifier_authority_baseline_v1(retained) != baseline
        ):
            raise ValueError("command signature verifier authority changed during verification")
        return result


_BOUND_VERIFIER_AUTHORITY_LOCK_V1 = Lock()
_BOUND_VERIFIER_AUTHORITIES_V1: WeakKeyDictionary[
    BoundEconomicCommandSignatureVerifierV1,
    _BoundVerifierAuthorityV1,
] = WeakKeyDictionary()


def _register_bound_verifier_authority_v1(
    witness: BoundEconomicCommandSignatureVerifierV1,
    authority: _BoundVerifierAuthorityV1,
) -> None:
    owned = _snapshot_bound_verifier_authority_v1(authority)
    with _BOUND_VERIFIER_AUTHORITY_LOCK_V1:
        if witness in _BOUND_VERIFIER_AUTHORITIES_V1:
            raise RuntimeError("bound command signature verifier is already registered")
        _BOUND_VERIFIER_AUTHORITIES_V1[witness] = owned


def _bound_verifier_authority_v1(
    witness: BoundEconomicCommandSignatureVerifierV1,
) -> _BoundVerifierAuthorityV1:
    if type(witness) is not BoundEconomicCommandSignatureVerifierV1:
        raise TypeError("bound command signature verifier type is not closed")
    with _BOUND_VERIFIER_AUTHORITY_LOCK_V1:
        authority = _BOUND_VERIFIER_AUTHORITIES_V1.get(witness)
    if authority is None:
        raise TypeError("bound command signature verifier is not loader-registered")
    return authority


def _snapshot_bound_verifier_authority_v1(
    authority: _BoundVerifierAuthorityV1,
) -> _BoundVerifierAuthorityV1:
    if type(authority) is not _BoundVerifierAuthorityV1:
        raise TypeError("bound command signature verifier authority must be exactly typed")
    exact_strings = (
        authority.release_id,
        authority.deployment_root,
        authority.profile_root,
        authority.implementation_root,
        authority.evidence_manifest_root,
        authority.backend_protocol_root,
        authority.signature_algorithm,
    )
    if any(type(value) is not str for value in exact_strings):
        raise TypeError("bound command signature verifier authority strings must be exact")
    for label, root in (
        ("release", authority.release_id),
        ("deployment", authority.deployment_root),
        ("profile", authority.profile_root),
        ("implementation", authority.implementation_root),
        ("evidence manifest", authority.evidence_manifest_root),
        ("backend protocol", authority.backend_protocol_root),
    ):
        _require_root(root, name=f"bound command signature verifier {label} root")
    _require_token(
        authority.signature_algorithm,
        name="bound command signature verifier algorithm",
    )
    _require_positive_int(
        authority.max_public_key_bytes,
        name="bound command signature verifier public-key ceiling",
    )
    _require_positive_int(
        authority.max_signature_bytes,
        name="bound command signature verifier signature ceiling",
    )
    if authority.max_public_key_bytes > MAX_TOKEN_BYTES_V1:
        raise ValueError("bound command signature verifier public-key ceiling is too large")
    if authority.max_signature_bytes > MAX_COMMAND_SIGNATURE_BYTES_V1:
        raise ValueError("bound command signature verifier signature ceiling is too large")
    if authority.backend is None:
        raise TypeError("bound command signature verifier backend is required")
    return _BoundVerifierAuthorityV1(
        release_id=authority.release_id,
        deployment_root=authority.deployment_root,
        profile_root=authority.profile_root,
        implementation_root=authority.implementation_root,
        evidence_manifest_root=authority.evidence_manifest_root,
        backend_protocol_root=authority.backend_protocol_root,
        signature_algorithm=authority.signature_algorithm,
        max_public_key_bytes=authority.max_public_key_bytes,
        max_signature_bytes=authority.max_signature_bytes,
        backend=authority.backend,
    )


def _bound_verifier_authority_baseline_v1(
    authority: _BoundVerifierAuthorityV1,
) -> tuple[object, ...]:
    return (
        authority.release_id,
        authority.deployment_root,
        authority.profile_root,
        authority.implementation_root,
        authority.evidence_manifest_root,
        authority.backend_protocol_root,
        authority.signature_algorithm,
        authority.max_public_key_bytes,
        authority.max_signature_bytes,
        _bound_verifier_binding_root_v1(authority),
    )


def _bound_verifier_binding_root_v1(authority: _BoundVerifierAuthorityV1) -> str:
    return hash_global_v1(
        _DEPLOYMENT_BINDING_ROOT_DOMAIN_V1,
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "release_id": authority.release_id,
            "deployment_root": authority.deployment_root,
            "profile_root": authority.profile_root,
            "implementation_root": authority.implementation_root,
            "evidence_manifest_root": authority.evidence_manifest_root,
            "backend_protocol_root": authority.backend_protocol_root,
        },
    )


__all__ = [
    "BoundEconomicCommandSignatureVerifierV1",
    "EconomicCommandSignatureVerifierBackendV1",
]
