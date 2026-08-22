"""Profile-governed command-signature verifier releases."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_TOKEN_BYTES_V1,
    EconomicPolicyRegistryV1,
    ReleaseStatusV1,
    _require_bool,
    _require_positive_int,
    _require_root,
    _require_token,
    hash_global_v1,
)

ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1: Final = "command_signature_verifier_registry"
MAX_COMMAND_SIGNATURE_VERIFIER_RELEASES_V1: Final = 32
MAX_COMMAND_SIGNATURE_BYTES_V1: Final = 4_096


class CommandSignatureVerifierEvidenceStatusV1(str, Enum):
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


REQUIRED_ACTIVE_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1: Final = frozenset(
    CommandSignatureVerifierEvidenceStatusV1
)


@dataclass(frozen=True, slots=True)
class EconomicCommandSignatureVerifierReleaseV1:
    release_id: str
    semantic_version: str
    signature_algorithm: str
    implementation_root: str
    public_key_schema_root: str
    signature_schema_root: str
    message_schema_root: str
    specification_root: str
    source_root: str
    toolchain_root: str
    evidence_manifest_root: str
    max_public_key_bytes: int
    max_signature_bytes: int
    status: ReleaseStatusV1
    accepts_new_authentications: bool
    evidence_statuses: tuple[CommandSignatureVerifierEvidenceStatusV1, ...]

    def __post_init__(self) -> None:
        _require_root(self.release_id, name="command signature verifier release id")
        _require_token(self.semantic_version, name="command signature verifier version")
        _require_token(self.signature_algorithm, name="command signature algorithm")
        for field_name in (
            "implementation_root",
            "public_key_schema_root",
            "signature_schema_root",
            "message_schema_root",
            "specification_root",
            "source_root",
            "toolchain_root",
            "evidence_manifest_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"command signature verifier {field_name}",
            )
        _require_positive_int(
            self.max_public_key_bytes,
            name="command signature verifier max public-key bytes",
        )
        _require_positive_int(
            self.max_signature_bytes,
            name="command signature verifier max signature bytes",
        )
        if self.max_public_key_bytes > MAX_TOKEN_BYTES_V1:
            raise ValueError("command signature verifier public-key ceiling is too large")
        if self.max_signature_bytes > MAX_COMMAND_SIGNATURE_BYTES_V1:
            raise ValueError("command signature verifier signature ceiling is too large")
        if type(self.status) is not ReleaseStatusV1:
            raise TypeError("command signature verifier status is not closed")
        _require_bool(
            self.accepts_new_authentications,
            name="command signature verifier accepts new authentications",
        )
        if type(self.evidence_statuses) is not tuple or any(
            type(status) is not CommandSignatureVerifierEvidenceStatusV1
            for status in self.evidence_statuses
        ):
            raise TypeError("command signature verifier evidence statuses are not closed")
        evidence = tuple(sorted(set(self.evidence_statuses), key=lambda status: status.value))
        if self.evidence_statuses != evidence:
            raise ValueError("command signature verifier evidence must be sorted and unique")
        is_active = self.status is ReleaseStatusV1.ACTIVE_NEW
        if self.accepts_new_authentications != is_active:
            raise ValueError("command signature verifier active status is inconsistent")
        if is_active and set(evidence) != (REQUIRED_ACTIVE_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1):
            raise ValueError("active command signature verifier lacks release evidence")
        if self.release_id != self.derived_release_id:
            raise ValueError("command signature verifier release id is not content-derived")

    @classmethod
    def build(
        cls,
        *,
        semantic_version: str,
        signature_algorithm: str,
        implementation_root: str,
        public_key_schema_root: str,
        signature_schema_root: str,
        message_schema_root: str,
        specification_root: str,
        source_root: str,
        toolchain_root: str,
        evidence_manifest_root: str,
        max_public_key_bytes: int,
        max_signature_bytes: int,
        status: ReleaseStatusV1,
        accepts_new_authentications: bool,
        evidence_statuses: tuple[CommandSignatureVerifierEvidenceStatusV1, ...],
    ) -> EconomicCommandSignatureVerifierReleaseV1:
        content = cls._content_body(
            signature_algorithm=signature_algorithm,
            implementation_root=implementation_root,
            public_key_schema_root=public_key_schema_root,
            signature_schema_root=signature_schema_root,
            message_schema_root=message_schema_root,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            evidence_manifest_root=evidence_manifest_root,
            max_public_key_bytes=max_public_key_bytes,
            max_signature_bytes=max_signature_bytes,
        )
        return cls(
            release_id=hash_global_v1(
                "economic-command-signature-verifier-release-content-v1",
                content,
            ),
            semantic_version=semantic_version,
            signature_algorithm=signature_algorithm,
            implementation_root=implementation_root,
            public_key_schema_root=public_key_schema_root,
            signature_schema_root=signature_schema_root,
            message_schema_root=message_schema_root,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            evidence_manifest_root=evidence_manifest_root,
            max_public_key_bytes=max_public_key_bytes,
            max_signature_bytes=max_signature_bytes,
            status=status,
            accepts_new_authentications=accepts_new_authentications,
            evidence_statuses=evidence_statuses,
        )

    @staticmethod
    def _content_body(**values: object) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, **values}

    @property
    def derived_release_id(self) -> str:
        return hash_global_v1(
            "economic-command-signature-verifier-release-content-v1",
            self._content_body(
                signature_algorithm=self.signature_algorithm,
                implementation_root=self.implementation_root,
                public_key_schema_root=self.public_key_schema_root,
                signature_schema_root=self.signature_schema_root,
                message_schema_root=self.message_schema_root,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                evidence_manifest_root=self.evidence_manifest_root,
                max_public_key_bytes=self.max_public_key_bytes,
                max_signature_bytes=self.max_signature_bytes,
            ),
        )

    @property
    def key(self) -> tuple[str, str]:
        return self.signature_algorithm, self.release_id

    def validate_current(self) -> None:
        if type(self) is not EconomicCommandSignatureVerifierReleaseV1:
            raise TypeError("command signature verifier release must be exactly typed")
        EconomicCommandSignatureVerifierReleaseV1(
            release_id=self.release_id,
            semantic_version=self.semantic_version,
            signature_algorithm=self.signature_algorithm,
            implementation_root=self.implementation_root,
            public_key_schema_root=self.public_key_schema_root,
            signature_schema_root=self.signature_schema_root,
            message_schema_root=self.message_schema_root,
            specification_root=self.specification_root,
            source_root=self.source_root,
            toolchain_root=self.toolchain_root,
            evidence_manifest_root=self.evidence_manifest_root,
            max_public_key_bytes=self.max_public_key_bytes,
            max_signature_bytes=self.max_signature_bytes,
            status=self.status,
            accepts_new_authentications=self.accepts_new_authentications,
            evidence_statuses=tuple(self.evidence_statuses),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._content_body(
                signature_algorithm=self.signature_algorithm,
                implementation_root=self.implementation_root,
                public_key_schema_root=self.public_key_schema_root,
                signature_schema_root=self.signature_schema_root,
                message_schema_root=self.message_schema_root,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                evidence_manifest_root=self.evidence_manifest_root,
                max_public_key_bytes=self.max_public_key_bytes,
                max_signature_bytes=self.max_signature_bytes,
            ),
            "release_id": self.release_id,
            "semantic_version": self.semantic_version,
            "status": self.status,
            "accepts_new_authentications": self.accepts_new_authentications,
            "evidence_statuses": self.evidence_statuses,
        }


@dataclass(frozen=True, slots=True)
class EconomicCommandSignatureVerifierRegistryV1:
    releases: tuple[EconomicCommandSignatureVerifierReleaseV1, ...]

    def __post_init__(self) -> None:
        if type(self.releases) is not tuple:
            raise TypeError("command signature verifier registry must be an exact tuple")
        if not 1 <= len(self.releases) <= MAX_COMMAND_SIGNATURE_VERIFIER_RELEASES_V1:
            raise ValueError("command signature verifier registry size is out of bounds")
        if any(
            type(release) is not EconomicCommandSignatureVerifierReleaseV1
            for release in self.releases
        ):
            raise TypeError("command signature verifier registry contains an invalid release")
        keys = tuple(release.key for release in self.releases)
        if keys != tuple(sorted(set(keys))):
            raise ValueError("command signature verifier registry must be sorted and unique")

    @property
    def registry_root(self) -> str:
        self.validate_current()
        return hash_global_v1(
            "economic-command-signature-verifier-registry-v1",
            self.to_canonical(),
        )

    def release_for_new_authentication(
        self,
        signature_algorithm: str,
    ) -> EconomicCommandSignatureVerifierReleaseV1:
        self.validate_current()
        _require_token(signature_algorithm, name="command signature algorithm")
        matches = tuple(
            release
            for release in self.releases
            if release.signature_algorithm == signature_algorithm
            and release.status is ReleaseStatusV1.ACTIVE_NEW
            and release.accepts_new_authentications
        )
        if len(matches) != 1:
            raise ValueError("command signature algorithm requires one active verifier release")
        return matches[0]

    def validate_current(self) -> None:
        if type(self) is not EconomicCommandSignatureVerifierRegistryV1:
            raise TypeError("command signature verifier registry must be exactly typed")
        for release in self.releases:
            release.validate_current()
        EconomicCommandSignatureVerifierRegistryV1(tuple(self.releases))

    def to_canonical(self) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, "releases": self.releases}


def select_profile_governed_command_signature_verifier_release_v1(
    *,
    policy_registry: EconomicPolicyRegistryV1,
    verifier_registry: EconomicCommandSignatureVerifierRegistryV1,
    command_kind: str,
    signature_algorithm: str,
    signer_public_key: str,
    signature_bytes: bytes,
) -> EconomicCommandSignatureVerifierReleaseV1:
    binding = policy_registry.require_binding(
        policy_kind=ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
        command_kind=command_kind,
    )
    if binding.policy_root != verifier_registry.registry_root:
        raise ValueError("command signature verifier registry is not profile governed")
    release = verifier_registry.release_for_new_authentication(signature_algorithm)
    if len(signer_public_key.encode("utf-8")) > release.max_public_key_bytes:
        raise ValueError("command signature public key exceeds release ceiling")
    if len(signature_bytes) > release.max_signature_bytes:
        raise ValueError("command signature exceeds release ceiling")
    return release


__all__ = [
    "CommandSignatureVerifierEvidenceStatusV1",
    "ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1",
    "EconomicCommandSignatureVerifierRegistryV1",
    "EconomicCommandSignatureVerifierReleaseV1",
    "REQUIRED_ACTIVE_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1",
    "select_profile_governed_command_signature_verifier_release_v1",
]
