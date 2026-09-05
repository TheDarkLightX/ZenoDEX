"""Concrete BLS verification for the existing economic-command message port.

G2Basic verifies the exact bytes supplied by the core's economic-intent message
constructor. There is no additional SHA256 prehash or legacy DEX-intent domain.
Public keys are canonical lowercase 0x-prefixed compressed G1 (48 bytes);
signatures are compressed G2 (96 bytes), using the existing py_ecc dependency.

The convenience binder selects this backend and delegates artifact acquisition
and release/manifest/scope checks to the existing loader. Loaded Python code,
its dependencies and their correspondence to the selected artifact remain a
trusted-process premise. This module creates no release evidence, policy,
authenticated-command witness, replay consumption or publication authority.
"""

from __future__ import annotations

from pathlib import Path
from typing import Final, Protocol, cast

from src.core.economic_command_signature_verifier_deployment_v1 import (
    BoundEconomicCommandSignatureVerifierV1,
    EconomicCommandSignatureVerifierBackendV1,
    EconomicCommandSignatureVerifierEvidenceManifestV1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierReleaseV1,
)
from src.core.global_settlement_types_v1 import MAX_JOURNAL_BYTES_V1
from src.integration.economic_command_signature_verifier_deployment_v1 import (
    bind_deployed_economic_command_signature_verifier_v1,
)

BLS_ECONOMIC_COMMAND_SIGNATURE_ALGORITHM_V1: Final = "BLS12_381_G2_BASIC_V1"
BLS_ECONOMIC_COMMAND_PUBLIC_KEY_BYTES_V1: Final = 48
BLS_ECONOMIC_COMMAND_SIGNATURE_BYTES_V1: Final = 96
_PUBLIC_KEY_HEX_BYTES_V1: Final = 2 + 2 * BLS_ECONOMIC_COMMAND_PUBLIC_KEY_BYTES_V1


class _BlsLibraryV1(Protocol):
    def Verify(self, public_key: bytes, message: bytes, signature: bytes) -> bool: ...


_BLS_BACKEND_V1: _BlsLibraryV1 | None
try:
    from py_ecc.bls import G2Basic as _ImportedG2Basic

    _BLS_BACKEND_V1 = cast(_BlsLibraryV1, _ImportedG2Basic)
except ImportError:
    _BLS_BACKEND_V1 = None


class EconomicCommandBlsBackendUnavailableErrorV1(RuntimeError):
    """The configured process lacks the existing BLS implementation."""


def _require_bls_backend_v1() -> _BlsLibraryV1:
    backend = _BLS_BACKEND_V1
    if backend is None:
        raise EconomicCommandBlsBackendUnavailableErrorV1(
            "economic command signature verification requires py_ecc.bls.G2Basic"
        )
    return backend


class _BlsEconomicCommandSignatureVerifierBackendV1:
    __slots__ = ()

    def verify_command_signature(
        self,
        *,
        signature_algorithm: str,
        signer_public_key: str,
        message_bytes: bytes,
        signature_bytes: bytes,
    ) -> bool:
        if type(signature_algorithm) is not str or (
            signature_algorithm != BLS_ECONOMIC_COMMAND_SIGNATURE_ALGORITHM_V1
        ):
            return False
        if type(signer_public_key) is not str or (
            len(signer_public_key) != _PUBLIC_KEY_HEX_BYTES_V1
            or not signer_public_key.startswith("0x")
            or any(character not in "0123456789abcdef" for character in signer_public_key[2:])
        ):
            return False
        if type(message_bytes) is not bytes or not 1 <= len(message_bytes) <= MAX_JOURNAL_BYTES_V1:
            return False
        if (
            type(signature_bytes) is not bytes
            or len(signature_bytes) != BLS_ECONOMIC_COMMAND_SIGNATURE_BYTES_V1
        ):
            return False
        backend = _require_bls_backend_v1()
        public_key_bytes = bytes.fromhex(signer_public_key[2:])
        return backend.Verify(public_key_bytes, message_bytes, signature_bytes) is True


def make_bls_economic_command_signature_verifier_backend_v1() -> (
    EconomicCommandSignatureVerifierBackendV1
):
    """Select the existing G2Basic implementation without backend injection."""

    _require_bls_backend_v1()
    return _BlsEconomicCommandSignatureVerifierBackendV1()


def bind_deployed_bls_economic_command_signature_verifier_v1(
    *,
    artifact_path: Path,
    release: EconomicCommandSignatureVerifierReleaseV1,
    evidence_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    deployment_root: str,
    profile_root: str,
) -> BoundEconomicCommandSignatureVerifierV1:
    """Delegate measurement/binding to the loader with the fixed BLS backend."""

    if type(release) is not EconomicCommandSignatureVerifierReleaseV1:
        raise TypeError("BLS command signature verifier release must be exactly typed")
    if release.signature_algorithm != BLS_ECONOMIC_COMMAND_SIGNATURE_ALGORITHM_V1:
        raise ValueError("BLS command signature verifier release algorithm mismatch")
    if release.max_public_key_bytes < _PUBLIC_KEY_HEX_BYTES_V1 or (
        release.max_signature_bytes < BLS_ECONOMIC_COMMAND_SIGNATURE_BYTES_V1
    ):
        raise ValueError("BLS command signature verifier release ceilings are incompatible")
    return bind_deployed_economic_command_signature_verifier_v1(
        artifact_path=artifact_path,
        release=release,
        evidence_manifest=evidence_manifest,
        deployment_root=deployment_root,
        profile_root=profile_root,
        backend=make_bls_economic_command_signature_verifier_backend_v1(),
    )


__all__ = [
    "BLS_ECONOMIC_COMMAND_PUBLIC_KEY_BYTES_V1",
    "BLS_ECONOMIC_COMMAND_SIGNATURE_ALGORITHM_V1",
    "BLS_ECONOMIC_COMMAND_SIGNATURE_BYTES_V1",
    "EconomicCommandBlsBackendUnavailableErrorV1",
    "bind_deployed_bls_economic_command_signature_verifier_v1",
    "make_bls_economic_command_signature_verifier_backend_v1",
]
