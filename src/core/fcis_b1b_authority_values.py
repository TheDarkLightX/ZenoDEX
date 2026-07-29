"""Exact untrusted carriers for the unmounted FCIS B1B-1 checkpoint.

These values are canonical data only.  They cannot construct a pinned verifier,
a migration candidate, a committed V2 state, a state-bound configuration, a
transition, a receipt, a bundle, a proof input, publication authority, or a
runtime mount.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, final

FCIS_B1B_AUTHORITY_SCHEMA_REVISION_V2 = "zenodex/fcis/b1b-authority-carriers/v2"
FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2 = "zenodex/fcis/state/authority-header/v2"
DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2 = (
    "zenodex/fcis/deployment/bootstrap-anchor-claim/v2"
)
V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2 = "zenodex/fcis/migration/v1-to-v2-manifest/v2"

MAX_B1B_TEXT_CHARACTERS_V2 = 4_096
MAX_B1B_TEXT_UTF8_BYTES_V2 = 16_384
MAX_B1B_CANONICAL_BYTES_V2 = 65_536
MAX_U256_V2 = (1 << 256) - 1


class FCISB1BAuthorityRecordTagV2(Enum):
    AUTHORITY_HEADER = "fcis_authority_header_v2"
    BOOTSTRAP_ANCHOR_CLAIM = "deployment_bootstrap_anchor_claim_v2"
    V1_TO_V2_MIGRATION_MANIFEST = "v1_to_v2_migration_manifest_v2"


class B1BAuthorityAdmissionCodeV2(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    BYTE_LIMIT = "byte_limit"
    INVALID_UTF8 = "invalid_utf8"
    INVALID_JSON = "invalid_json"
    DUPLICATE_FIELD = "duplicate_field"
    UNKNOWN_FIELD = "unknown_field"
    MISSING_FIELD = "missing_field"
    UNKNOWN_SCHEMA = "unknown_schema"
    NONCANONICAL_ENCODING = "noncanonical_encoding"
    INVALID_VALUE = "invalid_value"


@final
@dataclass(frozen=True, slots=True)
class FCISAuthorityHeaderSourceV2:
    chain_deployment_id: object
    sequence: object
    fee_distribution_configuration_root: object


@final
@dataclass(frozen=True, slots=True)
class DeploymentBootstrapAnchorClaimSourceV2:
    chain_deployment_id: object
    expected_migration_manifest_root: object


@final
@dataclass(frozen=True, slots=True)
class V1ToV2MigrationManifestSourceV2:
    chain_deployment_id: object
    expected_v1_pre_root: object
    fee_distribution_domain_id: object
    expected_initial_configuration_root: object
    initial_sequence: object
    initial_configuration_version: object
    initial_activation_sequence: object
    source_snapshot_version: object
    target_snapshot_version: object


def _require_text_v2(name: str, value: object) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be an exact nonempty string")
    if len(value) > MAX_B1B_TEXT_CHARACTERS_V2:
        raise ValueError(f"{name} exceeds its character bound")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must contain Unicode scalar values") from exc
    if len(encoded) > MAX_B1B_TEXT_UTF8_BYTES_V2:
        raise ValueError(f"{name} exceeds its UTF-8 bound")
    return value


def _require_u256_v2(name: str, value: object, *, positive: bool = False) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    minimum = 1 if positive else 0
    if not minimum <= value <= MAX_U256_V2:
        raise ValueError(f"{name} is outside its U256 domain")
    return value


def _require_digest_v2(name: str, value: object) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise TypeError(f"{name} must be a lowercase 32-byte hex digest")
    return value


@final
@dataclass(frozen=True, slots=True)
class FCISAuthorityHeaderV2:
    """Exact state-header data; never currentness or transition authority."""

    chain_deployment_id: str
    sequence: int
    fee_distribution_configuration_root: str

    def __post_init__(self) -> None:
        _require_text_v2("chain deployment identifier", self.chain_deployment_id)
        _require_u256_v2("protocol sequence", self.sequence)
        _require_digest_v2(
            "fee distribution configuration root",
            self.fee_distribution_configuration_root,
        )


@final
@dataclass(frozen=True, slots=True)
class DeploymentBootstrapAnchorClaimV2:
    """Untrusted audit claim; decoding it never constructs the pinned verifier."""

    chain_deployment_id: str
    expected_migration_manifest_root: str

    def __post_init__(self) -> None:
        _require_text_v2("chain deployment identifier", self.chain_deployment_id)
        _require_digest_v2(
            "expected migration manifest root",
            self.expected_migration_manifest_root,
        )


@final
@dataclass(frozen=True, slots=True)
class V1ToV2MigrationManifestV2:
    """Untrusted deterministic migration manifest carrier.

    Fixed values such as snapshot 4 -> 5 and initial 0/1/0 remain semantic
    migration checks.  The carrier admits the complete structural U256 domain.
    """

    chain_deployment_id: str
    expected_v1_pre_root: str
    fee_distribution_domain_id: str
    expected_initial_configuration_root: str
    initial_sequence: int
    initial_configuration_version: int
    initial_activation_sequence: int
    source_snapshot_version: int
    target_snapshot_version: int

    def __post_init__(self) -> None:
        _require_text_v2("chain deployment identifier", self.chain_deployment_id)
        _require_digest_v2("expected V1 pre-root", self.expected_v1_pre_root)
        _require_text_v2(
            "fee distribution domain identifier",
            self.fee_distribution_domain_id,
        )
        _require_digest_v2(
            "expected initial configuration root",
            self.expected_initial_configuration_root,
        )
        _require_u256_v2("initial protocol sequence", self.initial_sequence)
        _require_u256_v2(
            "initial configuration version",
            self.initial_configuration_version,
            positive=True,
        )
        _require_u256_v2(
            "initial activation sequence",
            self.initial_activation_sequence,
        )
        _require_u256_v2("source snapshot version", self.source_snapshot_version)
        _require_u256_v2("target snapshot version", self.target_snapshot_version)


@final
@dataclass(frozen=True, slots=True)
class B1BAuthorityAdmissionRejectV2:
    code: B1BAuthorityAdmissionCodeV2
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not B1BAuthorityAdmissionCodeV2:
            raise TypeError("B1B admission code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("B1B admission path must be an exact string tuple")


B1BAuthorityValueV2: TypeAlias = (
    FCISAuthorityHeaderV2
    | DeploymentBootstrapAnchorClaimV2
    | V1ToV2MigrationManifestV2
)
B1BAuthorityAdmissionResultV2: TypeAlias = B1BAuthorityValueV2 | B1BAuthorityAdmissionRejectV2
B1BAuthoritySourceV2: TypeAlias = (
    FCISAuthorityHeaderSourceV2
    | DeploymentBootstrapAnchorClaimSourceV2
    | V1ToV2MigrationManifestSourceV2
)


__all__ = (
    "B1BAuthorityAdmissionCodeV2",
    "B1BAuthorityAdmissionRejectV2",
    "B1BAuthorityAdmissionResultV2",
    "B1BAuthoritySourceV2",
    "B1BAuthorityValueV2",
    "DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2",
    "DeploymentBootstrapAnchorClaimSourceV2",
    "DeploymentBootstrapAnchorClaimV2",
    "FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2",
    "FCIS_B1B_AUTHORITY_SCHEMA_REVISION_V2",
    "FCISAuthorityHeaderSourceV2",
    "FCISAuthorityHeaderV2",
    "FCISB1BAuthorityRecordTagV2",
    "MAX_B1B_CANONICAL_BYTES_V2",
    "MAX_B1B_TEXT_CHARACTERS_V2",
    "MAX_B1B_TEXT_UTF8_BYTES_V2",
    "MAX_U256_V2",
    "V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2",
    "V1ToV2MigrationManifestSourceV2",
    "V1ToV2MigrationManifestV2",
)
