"""Release-bound deployment capability for command-signature verification.

The deterministic layer binds an exact artifact measurement and canonical
evidence manifest to one governed release and deployment/profile scope.  The
imperative shell owns artifact acquisition.  The injected backend remains an
external premise until a mounted loader constructs it from the measured
artifact in one trusted process boundary.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final

from ..state.canonical import domain_sep_bytes
from .economic_command_signature_verifier_capability_v1 import (
    _BOUND_VERIFIER_TOKEN_V1,
    BoundEconomicCommandSignatureVerifierV1,
    EconomicCommandSignatureVerifierBackendV1,
    _BoundVerifierAuthorityV1,
)
from .economic_command_signature_verifier_registry_v1 import (
    MAX_COMMAND_SIGNATURE_BYTES_V1,
    CommandSignatureVerifierEvidenceStatusV1,
    EconomicCommandSignatureVerifierReleaseV1,
)
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_TOKEN_BYTES_V1,
    _require_positive_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1: Final = 16 * 1024 * 1024
_IMPLEMENTATION_ROOT_DOMAIN_V1: Final = (
    "economic-command-signature-verifier-implementation-v1"
)
_EVIDENCE_MANIFEST_ROOT_DOMAIN_V1: Final = (
    "economic-command-signature-verifier-evidence-manifest-v1"
)
_BACKEND_PROTOCOL_ROOT_DOMAIN_V1: Final = (
    "economic-command-signature-verifier-backend-protocol-v1"
)


@dataclass(frozen=True, slots=True)
class CommandSignatureVerifierEvidenceArtifactV1:
    status: CommandSignatureVerifierEvidenceStatusV1
    artifact_root: str

    def __post_init__(self) -> None:
        if type(self.status) is not CommandSignatureVerifierEvidenceStatusV1:
            raise TypeError("command signature verifier evidence status is not closed")
        if type(self.artifact_root) is not str:
            raise TypeError("command signature verifier evidence artifact root must be exact str")
        _require_root(
            self.artifact_root,
            name="command signature verifier evidence artifact root",
        )

    @property
    def key(self) -> str:
        return self.status.value

    def to_canonical(self) -> dict[str, object]:
        return {"status": self.status, "artifact_root": self.artifact_root}


@dataclass(frozen=True, slots=True)
class EconomicCommandSignatureVerifierEvidenceManifestV1:
    signature_algorithm: str
    implementation_root: str
    public_key_schema_root: str
    signature_schema_root: str
    message_schema_root: str
    specification_root: str
    source_root: str
    toolchain_root: str
    backend_protocol_root: str
    max_public_key_bytes: int
    max_signature_bytes: int
    evidence_artifacts: tuple[CommandSignatureVerifierEvidenceArtifactV1, ...]

    def __post_init__(self) -> None:
        exact_string_fields = (
            "signature_algorithm",
            "implementation_root",
            "public_key_schema_root",
            "signature_schema_root",
            "message_schema_root",
            "specification_root",
            "source_root",
            "toolchain_root",
            "backend_protocol_root",
        )
        if any(type(getattr(self, field_name)) is not str for field_name in exact_string_fields):
            raise TypeError("command signature verifier manifest strings must be exact strings")
        _require_token(
            self.signature_algorithm,
            name="command signature verifier manifest algorithm",
        )
        for field_name in exact_string_fields[1:]:
            _require_root(
                getattr(self, field_name),
                name=f"command signature verifier manifest {field_name}",
            )
        _require_positive_int(
            self.max_public_key_bytes,
            name="command signature verifier manifest public-key ceiling",
        )
        _require_positive_int(
            self.max_signature_bytes,
            name="command signature verifier manifest signature ceiling",
        )
        if self.max_public_key_bytes > MAX_TOKEN_BYTES_V1:
            raise ValueError("command signature verifier manifest public-key ceiling is too large")
        if self.max_signature_bytes > MAX_COMMAND_SIGNATURE_BYTES_V1:
            raise ValueError("command signature verifier manifest signature ceiling is too large")
        if type(self.evidence_artifacts) is not tuple or any(
            type(row) is not CommandSignatureVerifierEvidenceArtifactV1
            for row in self.evidence_artifacts
        ):
            raise TypeError("command signature verifier manifest has an invalid evidence artifact")
        keys = tuple(row.key for row in self.evidence_artifacts)
        if not keys or keys != tuple(sorted(set(keys))):
            raise ValueError(
                "command signature verifier evidence artifacts must be sorted and unique"
            )

    @property
    def manifest_root(self) -> str:
        self.validate_current()
        return hash_global_v1(_EVIDENCE_MANIFEST_ROOT_DOMAIN_V1, self.to_canonical())

    def validate_current(self) -> None:
        if type(self) is not EconomicCommandSignatureVerifierEvidenceManifestV1:
            raise TypeError("command signature verifier evidence manifest must be exactly typed")
        EconomicCommandSignatureVerifierEvidenceManifestV1(
            signature_algorithm=self.signature_algorithm,
            implementation_root=self.implementation_root,
            public_key_schema_root=self.public_key_schema_root,
            signature_schema_root=self.signature_schema_root,
            message_schema_root=self.message_schema_root,
            specification_root=self.specification_root,
            source_root=self.source_root,
            toolchain_root=self.toolchain_root,
            backend_protocol_root=self.backend_protocol_root,
            max_public_key_bytes=self.max_public_key_bytes,
            max_signature_bytes=self.max_signature_bytes,
            evidence_artifacts=tuple(
                CommandSignatureVerifierEvidenceArtifactV1(
                    status=row.status,
                    artifact_root=row.artifact_root,
                )
                for row in self.evidence_artifacts
            ),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "signature_algorithm": self.signature_algorithm,
            "implementation_root": self.implementation_root,
            "public_key_schema_root": self.public_key_schema_root,
            "signature_schema_root": self.signature_schema_root,
            "message_schema_root": self.message_schema_root,
            "specification_root": self.specification_root,
            "source_root": self.source_root,
            "toolchain_root": self.toolchain_root,
            "backend_protocol_root": self.backend_protocol_root,
            "max_public_key_bytes": self.max_public_key_bytes,
            "max_signature_bytes": self.max_signature_bytes,
            "evidence_artifacts": self.evidence_artifacts,
        }


def command_signature_verifier_backend_protocol_root_v1() -> str:
    return hash_global_v1(
        _BACKEND_PROTOCOL_ROOT_DOMAIN_V1,
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "request_fields": (
                "signature_algorithm",
                "signer_public_key",
                "message_bytes",
                "signature_bytes",
            ),
            "response_semantics": "EXACT_TRUE_ACCEPTS_OTHERWISE_REJECTS",
        },
    )


def command_signature_verifier_implementation_root_v1(artifact_bytes: bytes) -> str:
    if type(artifact_bytes) is not bytes:
        raise TypeError("command signature verifier artifact must be exact bytes")
    if not 1 <= len(artifact_bytes) <= MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1:
        raise ValueError("command signature verifier artifact byte length is out of bounds")
    digest = hashlib.sha256()
    digest.update(domain_sep_bytes(_IMPLEMENTATION_ROOT_DOMAIN_V1, version=1))
    digest.update(artifact_bytes)
    return "0x" + digest.hexdigest()


def bind_economic_command_signature_verifier_deployment_v1(
    *,
    release: EconomicCommandSignatureVerifierReleaseV1,
    evidence_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    measured_artifact_bytes: bytes,
    deployment_root: str,
    profile_root: str,
    backend: EconomicCommandSignatureVerifierBackendV1,
) -> BoundEconomicCommandSignatureVerifierV1:
    """Bind one measured verifier artifact to one governed deployment scope."""

    owned_release = _snapshot_signature_verifier_release_v1(release)
    owned_manifest = _snapshot_signature_verifier_manifest_v1(evidence_manifest)
    if owned_manifest.manifest_root != owned_release.evidence_manifest_root:
        raise ValueError("command signature verifier evidence manifest root mismatch")
    _require_manifest_release_coordinates_v1(owned_manifest, owned_release)
    if owned_manifest.backend_protocol_root != command_signature_verifier_backend_protocol_root_v1():
        raise ValueError("command signature verifier backend protocol root mismatch")
    measured_root = command_signature_verifier_implementation_root_v1(measured_artifact_bytes)
    if measured_root != owned_release.implementation_root:
        raise ValueError("command signature verifier measured implementation root mismatch")
    if type(deployment_root) is not str or type(profile_root) is not str:
        raise TypeError("command signature verifier scope roots must be exact strings")
    _require_root(deployment_root, name="command signature verifier deployment root")
    _require_root(profile_root, name="command signature verifier profile root")
    if backend is None:
        raise TypeError("command signature verifier backend is required")
    return BoundEconomicCommandSignatureVerifierV1(
        _BOUND_VERIFIER_TOKEN_V1,
        _BoundVerifierAuthorityV1(
            release_id=owned_release.release_id,
            deployment_root=deployment_root,
            profile_root=profile_root,
            implementation_root=owned_release.implementation_root,
            evidence_manifest_root=owned_release.evidence_manifest_root,
            backend_protocol_root=owned_manifest.backend_protocol_root,
            signature_algorithm=owned_release.signature_algorithm,
            max_public_key_bytes=owned_release.max_public_key_bytes,
            max_signature_bytes=owned_release.max_signature_bytes,
            backend=backend,
        ),
    )


def _snapshot_signature_verifier_release_v1(
    release: EconomicCommandSignatureVerifierReleaseV1,
) -> EconomicCommandSignatureVerifierReleaseV1:
    if type(release) is not EconomicCommandSignatureVerifierReleaseV1:
        raise TypeError("command signature verifier release must be exactly typed")
    if type(release.evidence_statuses) is not tuple:
        raise TypeError("command signature verifier release evidence must be exact tuple")
    return EconomicCommandSignatureVerifierReleaseV1(
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


def _snapshot_signature_verifier_manifest_v1(
    manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
) -> EconomicCommandSignatureVerifierEvidenceManifestV1:
    if type(manifest) is not EconomicCommandSignatureVerifierEvidenceManifestV1:
        raise TypeError("command signature verifier evidence manifest must be exactly typed")
    if type(manifest.evidence_artifacts) is not tuple:
        raise TypeError("command signature verifier evidence artifacts must be exact tuple")
    if any(
        type(row) is not CommandSignatureVerifierEvidenceArtifactV1
        for row in manifest.evidence_artifacts
    ):
        raise TypeError("command signature verifier manifest has an invalid evidence artifact")
    return EconomicCommandSignatureVerifierEvidenceManifestV1(
        signature_algorithm=manifest.signature_algorithm,
        implementation_root=manifest.implementation_root,
        public_key_schema_root=manifest.public_key_schema_root,
        signature_schema_root=manifest.signature_schema_root,
        message_schema_root=manifest.message_schema_root,
        specification_root=manifest.specification_root,
        source_root=manifest.source_root,
        toolchain_root=manifest.toolchain_root,
        backend_protocol_root=manifest.backend_protocol_root,
        max_public_key_bytes=manifest.max_public_key_bytes,
        max_signature_bytes=manifest.max_signature_bytes,
        evidence_artifacts=tuple(
            CommandSignatureVerifierEvidenceArtifactV1(
                status=row.status,
                artifact_root=row.artifact_root,
            )
            for row in manifest.evidence_artifacts
        ),
    )


def _require_manifest_release_coordinates_v1(
    manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    release: EconomicCommandSignatureVerifierReleaseV1,
) -> None:
    coordinates = (
        (manifest.signature_algorithm, release.signature_algorithm),
        (manifest.implementation_root, release.implementation_root),
        (manifest.public_key_schema_root, release.public_key_schema_root),
        (manifest.signature_schema_root, release.signature_schema_root),
        (manifest.message_schema_root, release.message_schema_root),
        (manifest.specification_root, release.specification_root),
        (manifest.source_root, release.source_root),
        (manifest.toolchain_root, release.toolchain_root),
        (manifest.max_public_key_bytes, release.max_public_key_bytes),
        (manifest.max_signature_bytes, release.max_signature_bytes),
        (
            tuple(row.status for row in manifest.evidence_artifacts),
            release.evidence_statuses,
        ),
    )
    if any(type(left) is not type(right) or left != right for left, right in coordinates):
        raise ValueError("command signature verifier manifest release coordinate mismatch")


__all__ = [
    "BoundEconomicCommandSignatureVerifierV1",
    "CommandSignatureVerifierEvidenceArtifactV1",
    "EconomicCommandSignatureVerifierBackendV1",
    "EconomicCommandSignatureVerifierEvidenceManifestV1",
    "MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1",
    "bind_economic_command_signature_verifier_deployment_v1",
    "command_signature_verifier_backend_protocol_root_v1",
    "command_signature_verifier_implementation_root_v1",
]
