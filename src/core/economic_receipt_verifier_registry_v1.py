"""Profile-governed releases for global economic receipt verification."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_JOURNAL_BYTES_V1,
    EconomicProfileSnapshotV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    _require_bool,
    _require_positive_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

MAX_ECONOMIC_RECEIPT_VERIFIER_RELEASES_V1: Final = 32
MAX_ECONOMIC_RECEIPT_BYTES_V1: Final = 16 * 1024 * 1024


class EconomicReceiptVerifierEvidenceStatusV1(str, Enum):
    SPECIFIED = "SPECIFIED"
    IMPLEMENTED = "IMPLEMENTED"
    TESTED = "TESTED"
    SOURCE_PINNED = "SOURCE_PINNED"
    TOOLCHAIN_PINNED = "TOOLCHAIN_PINNED"
    IMPLEMENTATION_REPLAYED = "IMPLEMENTATION_REPLAYED"
    INDEPENDENTLY_REVIEWED = "INDEPENDENTLY_REVIEWED"
    DEPLOYMENT_BOUND = "DEPLOYMENT_BOUND"
    NO_BYPASS = "NO_BYPASS"
    RELEASE_BACKED = "RELEASE_BACKED"


REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1: Final = frozenset(
    {
        EconomicReceiptVerifierEvidenceStatusV1.SPECIFIED,
        EconomicReceiptVerifierEvidenceStatusV1.IMPLEMENTED,
        EconomicReceiptVerifierEvidenceStatusV1.TESTED,
        EconomicReceiptVerifierEvidenceStatusV1.SOURCE_PINNED,
        EconomicReceiptVerifierEvidenceStatusV1.TOOLCHAIN_PINNED,
    }
)
REQUIRED_ACTIVE_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1: Final = frozenset(
    EconomicReceiptVerifierEvidenceStatusV1
)


class EconomicReceiptVerifierSelectionPurposeV1(str, Enum):
    """Closed authority purpose; shadow selection can never imply production."""

    RESEARCH_SHADOW = "RESEARCH_SHADOW"
    PRODUCTION_NEW = "PRODUCTION_NEW"


@dataclass(frozen=True, slots=True)
class EconomicReceiptVerifierReleaseV1:
    release_id: str
    semantic_version: str
    proof_system: str
    implementation_root: str
    receipt_schema_root: str
    journal_schema_root: str
    root_image_id: str
    specification_root: str
    source_root: str
    toolchain_root: str
    evidence_manifest_root: str
    backend_protocol_root: str
    max_receipt_bytes: int
    max_journal_bytes: int
    status: ReleaseStatusV1
    accepts_new_receipts: bool
    evidence_statuses: tuple[EconomicReceiptVerifierEvidenceStatusV1, ...]

    def __post_init__(self) -> None:
        string_fields = (
            "release_id",
            "semantic_version",
            "proof_system",
            "implementation_root",
            "receipt_schema_root",
            "journal_schema_root",
            "root_image_id",
            "specification_root",
            "source_root",
            "toolchain_root",
            "evidence_manifest_root",
            "backend_protocol_root",
        )
        if any(type(getattr(self, name)) is not str for name in string_fields):
            raise TypeError("economic receipt verifier release strings must be exact")
        _require_root(self.release_id, name="economic receipt verifier release id")
        _require_token(
            self.semantic_version,
            name="economic receipt verifier semantic version",
        )
        _require_token(self.proof_system, name="economic receipt verifier proof system")
        for name in string_fields[3:]:
            _require_root(
                getattr(self, name),
                name=f"economic receipt verifier {name}",
            )
        _require_positive_int(
            self.max_receipt_bytes,
            name="economic receipt verifier receipt byte ceiling",
        )
        _require_positive_int(
            self.max_journal_bytes,
            name="economic receipt verifier journal byte ceiling",
        )
        if self.max_receipt_bytes > MAX_ECONOMIC_RECEIPT_BYTES_V1:
            raise ValueError("economic receipt verifier receipt ceiling is too large")
        if self.max_journal_bytes > MAX_JOURNAL_BYTES_V1:
            raise ValueError("economic receipt verifier journal ceiling is too large")
        if type(self.status) is not ReleaseStatusV1:
            raise TypeError("economic receipt verifier status is not closed")
        _require_bool(
            self.accepts_new_receipts,
            name="economic receipt verifier accepts new receipts",
        )
        if type(self.evidence_statuses) is not tuple or any(
            type(status) is not EconomicReceiptVerifierEvidenceStatusV1
            for status in self.evidence_statuses
        ):
            raise TypeError("economic receipt verifier evidence is not closed")
        evidence = tuple(
            sorted(set(self.evidence_statuses), key=lambda status: status.value)
        )
        if self.evidence_statuses != evidence:
            raise ValueError("economic receipt verifier evidence must be sorted and unique")
        active = self.status is ReleaseStatusV1.ACTIVE_NEW
        if self.accepts_new_receipts != active:
            raise ValueError("economic receipt verifier active status is inconsistent")
        if active and set(evidence) != (
            REQUIRED_ACTIVE_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1
        ):
            raise ValueError("active economic receipt verifier lacks release evidence")
        if self.status is ReleaseStatusV1.SHADOW and not (
            REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1
            <= set(evidence)
        ):
            raise ValueError("shadow economic receipt verifier lacks baseline evidence")
        if self.release_id != self.derived_release_id:
            raise ValueError("economic receipt verifier release id is not content-derived")

    @classmethod
    def build(
        cls,
        *,
        semantic_version: str,
        proof_system: str,
        implementation_root: str,
        receipt_schema_root: str,
        journal_schema_root: str,
        root_image_id: str,
        specification_root: str,
        source_root: str,
        toolchain_root: str,
        evidence_manifest_root: str,
        backend_protocol_root: str,
        max_receipt_bytes: int,
        max_journal_bytes: int,
        status: ReleaseStatusV1,
        accepts_new_receipts: bool,
        evidence_statuses: tuple[EconomicReceiptVerifierEvidenceStatusV1, ...],
    ) -> EconomicReceiptVerifierReleaseV1:
        content = cls._content_body(
            proof_system=proof_system,
            implementation_root=implementation_root,
            receipt_schema_root=receipt_schema_root,
            journal_schema_root=journal_schema_root,
            root_image_id=root_image_id,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            evidence_manifest_root=evidence_manifest_root,
            backend_protocol_root=backend_protocol_root,
            max_receipt_bytes=max_receipt_bytes,
            max_journal_bytes=max_journal_bytes,
        )
        return cls(
            release_id=hash_global_v1(
                "economic-receipt-verifier-release-content-v1",
                content,
            ),
            semantic_version=semantic_version,
            proof_system=proof_system,
            implementation_root=implementation_root,
            receipt_schema_root=receipt_schema_root,
            journal_schema_root=journal_schema_root,
            root_image_id=root_image_id,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            evidence_manifest_root=evidence_manifest_root,
            backend_protocol_root=backend_protocol_root,
            max_receipt_bytes=max_receipt_bytes,
            max_journal_bytes=max_journal_bytes,
            status=status,
            accepts_new_receipts=accepts_new_receipts,
            evidence_statuses=evidence_statuses,
        )

    @staticmethod
    def _content_body(**values: object) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, **values}

    @property
    def derived_release_id(self) -> str:
        return hash_global_v1(
            "economic-receipt-verifier-release-content-v1",
            self._content_body(
                proof_system=self.proof_system,
                implementation_root=self.implementation_root,
                receipt_schema_root=self.receipt_schema_root,
                journal_schema_root=self.journal_schema_root,
                root_image_id=self.root_image_id,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                evidence_manifest_root=self.evidence_manifest_root,
                backend_protocol_root=self.backend_protocol_root,
                max_receipt_bytes=self.max_receipt_bytes,
                max_journal_bytes=self.max_journal_bytes,
            ),
        )

    @property
    def key(self) -> tuple[str, str]:
        return self.proof_system, self.release_id

    def validate_current(self) -> None:
        if type(self) is not EconomicReceiptVerifierReleaseV1:
            raise TypeError("economic receipt verifier release must be exactly typed")
        EconomicReceiptVerifierReleaseV1(
            release_id=self.release_id,
            semantic_version=self.semantic_version,
            proof_system=self.proof_system,
            implementation_root=self.implementation_root,
            receipt_schema_root=self.receipt_schema_root,
            journal_schema_root=self.journal_schema_root,
            root_image_id=self.root_image_id,
            specification_root=self.specification_root,
            source_root=self.source_root,
            toolchain_root=self.toolchain_root,
            evidence_manifest_root=self.evidence_manifest_root,
            backend_protocol_root=self.backend_protocol_root,
            max_receipt_bytes=self.max_receipt_bytes,
            max_journal_bytes=self.max_journal_bytes,
            status=self.status,
            accepts_new_receipts=self.accepts_new_receipts,
            evidence_statuses=tuple(self.evidence_statuses),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._content_body(
                proof_system=self.proof_system,
                implementation_root=self.implementation_root,
                receipt_schema_root=self.receipt_schema_root,
                journal_schema_root=self.journal_schema_root,
                root_image_id=self.root_image_id,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                evidence_manifest_root=self.evidence_manifest_root,
                backend_protocol_root=self.backend_protocol_root,
                max_receipt_bytes=self.max_receipt_bytes,
                max_journal_bytes=self.max_journal_bytes,
            ),
            "release_id": self.release_id,
            "semantic_version": self.semantic_version,
            "status": self.status,
            "accepts_new_receipts": self.accepts_new_receipts,
            "evidence_statuses": self.evidence_statuses,
        }


@dataclass(frozen=True, slots=True)
class EconomicReceiptVerifierRegistryV1:
    releases: tuple[EconomicReceiptVerifierReleaseV1, ...]

    def __post_init__(self) -> None:
        if type(self.releases) is not tuple:
            raise TypeError("economic receipt verifier registry must be an exact tuple")
        if not 1 <= len(self.releases) <= MAX_ECONOMIC_RECEIPT_VERIFIER_RELEASES_V1:
            raise ValueError("economic receipt verifier registry size is out of bounds")
        if any(type(row) is not EconomicReceiptVerifierReleaseV1 for row in self.releases):
            raise TypeError("economic receipt verifier registry contains an invalid release")
        keys = tuple(row.key for row in self.releases)
        if keys != tuple(sorted(set(keys))):
            raise ValueError("economic receipt verifier registry must be sorted and unique")

    @property
    def registry_root(self) -> str:
        self.validate_current()
        return hash_global_v1(
            "economic-receipt-verifier-registry-v1",
            self.to_canonical(),
        )

    def release_for(
        self,
        purpose: EconomicReceiptVerifierSelectionPurposeV1,
    ) -> EconomicReceiptVerifierReleaseV1:
        self.validate_current()
        if type(purpose) is not EconomicReceiptVerifierSelectionPurposeV1:
            raise TypeError("economic receipt verifier selection purpose is not closed")
        if purpose is EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW:
            matches = tuple(
                row for row in self.releases if row.status is ReleaseStatusV1.SHADOW
            )
            expected = "one shadow verifier release"
        else:
            matches = tuple(
                row
                for row in self.releases
                if row.status is ReleaseStatusV1.ACTIVE_NEW
                and row.accepts_new_receipts
            )
            expected = "one active verifier release"
        if len(matches) != 1:
            raise ValueError(f"economic receipt profile requires {expected}")
        return matches[0]

    def validate_current(self) -> None:
        if type(self) is not EconomicReceiptVerifierRegistryV1:
            raise TypeError("economic receipt verifier registry must be exactly typed")
        for release in self.releases:
            release.validate_current()
        EconomicReceiptVerifierRegistryV1(tuple(self.releases))

    def to_canonical(self) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, "releases": self.releases}


def select_profile_governed_economic_receipt_verifier_release_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    verifier_registry: EconomicReceiptVerifierRegistryV1,
    selection_purpose: EconomicReceiptVerifierSelectionPurposeV1,
) -> EconomicReceiptVerifierReleaseV1:
    """Resolve exactly one profile-committed verifier release for one purpose."""

    if type(verifier_registry) is not EconomicReceiptVerifierRegistryV1:
        raise TypeError("economic receipt verifier registry must be exactly typed")
    owned_profile = snapshot_economic_profile_v1(profile)
    verifier_registry.validate_current()
    if (
        selection_purpose is EconomicReceiptVerifierSelectionPurposeV1.PRODUCTION_NEW
        and owned_profile.status is not ProfileStatusV1.ACTIVE
    ):
        raise ValueError("production receipt verifier requires an active profile")
    if owned_profile.verifier_registry_root != verifier_registry.registry_root:
        raise ValueError("economic receipt verifier registry is not profile governed")
    release = verifier_registry.release_for(selection_purpose)
    if release.root_image_id != owned_profile.root_image_id:
        raise ValueError("economic receipt verifier root image is not profile selected")
    return release


__all__ = [
    "EconomicReceiptVerifierEvidenceStatusV1",
    "EconomicReceiptVerifierRegistryV1",
    "EconomicReceiptVerifierReleaseV1",
    "EconomicReceiptVerifierSelectionPurposeV1",
    "MAX_ECONOMIC_RECEIPT_BYTES_V1",
    "MAX_ECONOMIC_RECEIPT_VERIFIER_RELEASES_V1",
    "REQUIRED_ACTIVE_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1",
    "REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1",
    "select_profile_governed_economic_receipt_verifier_release_v1",
]
