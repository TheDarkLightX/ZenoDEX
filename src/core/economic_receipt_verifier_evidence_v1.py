"""Canonical evidence and artifact measurement for receipt-verifier releases."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final

from ..state.canonical import domain_sep_bytes
from .economic_receipt_verifier_registry_v1 import (
    MAX_ECONOMIC_RECEIPT_BYTES_V1,
    EconomicReceiptVerifierEvidenceStatusV1,
    EconomicReceiptVerifierReleaseV1,
)
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_JOURNAL_BYTES_V1,
    _require_positive_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

MAX_ECONOMIC_RECEIPT_VERIFIER_ARTIFACT_BYTES_V1: Final = 32 * 1024 * 1024
_IMPLEMENTATION_ROOT_DOMAIN_V1: Final = "economic-receipt-verifier-implementation-v1"
_EVIDENCE_MANIFEST_ROOT_DOMAIN_V1: Final = (
    "economic-receipt-verifier-evidence-manifest-v1"
)
_BACKEND_PROTOCOL_ROOT_DOMAIN_V1: Final = "economic-receipt-verifier-backend-protocol-v1"


@dataclass(frozen=True, slots=True)
class EconomicReceiptVerifierEvidenceArtifactV1:
    status: EconomicReceiptVerifierEvidenceStatusV1
    artifact_root: str

    def __post_init__(self) -> None:
        if type(self.status) is not EconomicReceiptVerifierEvidenceStatusV1:
            raise TypeError("economic receipt verifier evidence status is not closed")
        if type(self.artifact_root) is not str:
            raise TypeError("economic receipt verifier artifact root must be exact str")
        _require_root(self.artifact_root, name="economic receipt verifier artifact root")

    @property
    def key(self) -> str:
        return self.status.value

    def to_canonical(self) -> dict[str, object]:
        return {"status": self.status, "artifact_root": self.artifact_root}


@dataclass(frozen=True, slots=True)
class EconomicReceiptVerifierEvidenceManifestV1:
    proof_system: str
    implementation_root: str
    receipt_schema_root: str
    journal_schema_root: str
    root_image_id: str
    specification_root: str
    source_root: str
    toolchain_root: str
    backend_protocol_root: str
    max_receipt_bytes: int
    max_journal_bytes: int
    evidence_artifacts: tuple[EconomicReceiptVerifierEvidenceArtifactV1, ...]

    def __post_init__(self) -> None:
        string_fields = (
            "proof_system",
            "implementation_root",
            "receipt_schema_root",
            "journal_schema_root",
            "root_image_id",
            "specification_root",
            "source_root",
            "toolchain_root",
            "backend_protocol_root",
        )
        if any(type(getattr(self, name)) is not str for name in string_fields):
            raise TypeError("economic receipt verifier manifest strings must be exact")
        _require_token(self.proof_system, name="economic receipt verifier proof system")
        for name in string_fields[1:]:
            _require_root(
                getattr(self, name),
                name=f"economic receipt verifier manifest {name}",
            )
        _require_positive_int(
            self.max_receipt_bytes,
            name="economic receipt verifier manifest receipt ceiling",
        )
        _require_positive_int(
            self.max_journal_bytes,
            name="economic receipt verifier manifest journal ceiling",
        )
        if self.max_receipt_bytes > MAX_ECONOMIC_RECEIPT_BYTES_V1:
            raise ValueError("economic receipt verifier manifest receipt ceiling is too large")
        if self.max_journal_bytes > MAX_JOURNAL_BYTES_V1:
            raise ValueError("economic receipt verifier manifest journal ceiling is too large")
        if type(self.evidence_artifacts) is not tuple or any(
            type(row) is not EconomicReceiptVerifierEvidenceArtifactV1
            for row in self.evidence_artifacts
        ):
            raise TypeError("economic receipt verifier manifest artifacts are not closed")
        keys = tuple(row.key for row in self.evidence_artifacts)
        if not keys or keys != tuple(sorted(set(keys))):
            raise ValueError(
                "economic receipt verifier evidence artifacts must be sorted and unique"
            )

    @property
    def manifest_root(self) -> str:
        self.validate_current()
        return hash_global_v1(_EVIDENCE_MANIFEST_ROOT_DOMAIN_V1, self.to_canonical())

    def validate_current(self) -> None:
        if type(self) is not EconomicReceiptVerifierEvidenceManifestV1:
            raise TypeError("economic receipt verifier manifest must be exactly typed")
        _snapshot_economic_receipt_verifier_manifest_v1(self)

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "proof_system": self.proof_system,
            "implementation_root": self.implementation_root,
            "receipt_schema_root": self.receipt_schema_root,
            "journal_schema_root": self.journal_schema_root,
            "root_image_id": self.root_image_id,
            "specification_root": self.specification_root,
            "source_root": self.source_root,
            "toolchain_root": self.toolchain_root,
            "backend_protocol_root": self.backend_protocol_root,
            "max_receipt_bytes": self.max_receipt_bytes,
            "max_journal_bytes": self.max_journal_bytes,
            "evidence_artifacts": self.evidence_artifacts,
        }


def economic_receipt_verifier_backend_protocol_root_v1() -> str:
    return hash_global_v1(
        _BACKEND_PROTOCOL_ROOT_DOMAIN_V1,
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "request_fields": (
                "receipt_bytes",
                "expected_image_id",
                "expected_journal_bytes",
            ),
            "response_semantics": "EXACT_NONE_ACCEPTS_EXCEPTION_REJECTS",
        },
    )


def economic_receipt_verifier_implementation_root_v1(artifact_bytes: bytes) -> str:
    if type(artifact_bytes) is not bytes:
        raise TypeError("economic receipt verifier artifact must be exact bytes")
    if not 1 <= len(artifact_bytes) <= MAX_ECONOMIC_RECEIPT_VERIFIER_ARTIFACT_BYTES_V1:
        raise ValueError("economic receipt verifier artifact byte length is out of bounds")
    digest = hashlib.sha256()
    digest.update(domain_sep_bytes(_IMPLEMENTATION_ROOT_DOMAIN_V1, version=1))
    digest.update(artifact_bytes)
    return "0x" + digest.hexdigest()


def _snapshot_economic_receipt_verifier_manifest_v1(
    manifest: EconomicReceiptVerifierEvidenceManifestV1,
) -> EconomicReceiptVerifierEvidenceManifestV1:
    if type(manifest) is not EconomicReceiptVerifierEvidenceManifestV1:
        raise TypeError("economic receipt verifier manifest must be exactly typed")
    return EconomicReceiptVerifierEvidenceManifestV1(
        proof_system=manifest.proof_system,
        implementation_root=manifest.implementation_root,
        receipt_schema_root=manifest.receipt_schema_root,
        journal_schema_root=manifest.journal_schema_root,
        root_image_id=manifest.root_image_id,
        specification_root=manifest.specification_root,
        source_root=manifest.source_root,
        toolchain_root=manifest.toolchain_root,
        backend_protocol_root=manifest.backend_protocol_root,
        max_receipt_bytes=manifest.max_receipt_bytes,
        max_journal_bytes=manifest.max_journal_bytes,
        evidence_artifacts=tuple(
            EconomicReceiptVerifierEvidenceArtifactV1(
                status=row.status,
                artifact_root=row.artifact_root,
            )
            for row in manifest.evidence_artifacts
        ),
    )


def _require_manifest_release_coordinates_v1(
    manifest: EconomicReceiptVerifierEvidenceManifestV1,
    release: EconomicReceiptVerifierReleaseV1,
) -> None:
    coordinates = (
        (manifest.proof_system, release.proof_system),
        (manifest.implementation_root, release.implementation_root),
        (manifest.receipt_schema_root, release.receipt_schema_root),
        (manifest.journal_schema_root, release.journal_schema_root),
        (manifest.root_image_id, release.root_image_id),
        (manifest.specification_root, release.specification_root),
        (manifest.source_root, release.source_root),
        (manifest.toolchain_root, release.toolchain_root),
        (manifest.backend_protocol_root, release.backend_protocol_root),
        (manifest.max_receipt_bytes, release.max_receipt_bytes),
        (manifest.max_journal_bytes, release.max_journal_bytes),
        (
            tuple(row.status for row in manifest.evidence_artifacts),
            release.evidence_statuses,
        ),
    )
    if any(type(left) is not type(right) or left != right for left, right in coordinates):
        raise ValueError("economic receipt verifier manifest release coordinate mismatch")


__all__ = [
    "EconomicReceiptVerifierEvidenceArtifactV1",
    "EconomicReceiptVerifierEvidenceManifestV1",
    "MAX_ECONOMIC_RECEIPT_VERIFIER_ARTIFACT_BYTES_V1",
    "economic_receipt_verifier_backend_protocol_root_v1",
    "economic_receipt_verifier_implementation_root_v1",
]
