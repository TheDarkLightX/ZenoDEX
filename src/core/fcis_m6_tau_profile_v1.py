"""Canonical, non-authoritative values for one pinned Tau integration profile.

These values describe source and semantics.  Construction does not establish
that the source was observed, built, verified, current, compatible, or selected
as a writer.  The integration verifier owns those later receipts.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from hashlib import sha256
from typing import Final, final

from ..state.canonical import canonical_json_bytes

TAU_INTEGRATION_PROFILE_SCHEMA_V1: Final = "zenodex/fcis/m6/tau-integration-profile/v1"
MAX_TAU_PROFILE_TEXT_BYTES_V1: Final = 512
MAX_TAU_PROFILE_CAPABILITIES_V1: Final = 64

_HEX = frozenset("0123456789abcdef")
_CAPABILITY_CHARACTERS = frozenset("abcdefghijklmnopqrstuvwxyz0123456789_.:/-")


class TauProfileValueError(ValueError):
    """Raised when a profile value is outside its closed canonical language."""


class TauIntegrationObservationV1(str, Enum):
    """Externally observed Tau-profile states understood by the M6 gate."""

    VERIFIED_COMPATIBLE = "verified_compatible"
    UNAVAILABLE = "unavailable"
    CENSORING = "censoring"
    CHANGED = "changed"
    EQUIVOCAL = "equivocal"
    INCOMPATIBLE = "incompatible"


class TauOperationClassV1(str, Enum):
    """Operation classes with distinct Tau continuity requirements."""

    TAU_INDEPENDENT = "tau_independent"
    TAU_DEPENDENT = "tau_dependent"
    TAU_NATIVE_ASSET = "tau_native_asset"


class TauSubstrateDispositionV1(str, Enum):
    """Closed substrate choices for one requested operation."""

    USE_TAU = "use_tau"
    USE_ZENO_LEDGER = "use_zeno_ledger"
    REJECT_OR_PEND = "reject_or_pend"


def _text(value: object, name: str, *, maximum_bytes: int = MAX_TAU_PROFILE_TEXT_BYTES_V1) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be nonempty exact text")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise TypeError(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise TauProfileValueError(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise TauProfileValueError(f"{name} contains a control character")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if (
        len(checked) != 64
        or checked != checked.lower()
        or any(character not in _HEX for character in checked)
    ):
        raise TypeError(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _git_oid(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=40)
    if (
        len(checked) != 40
        or checked != checked.lower()
        or any(character not in _HEX for character in checked)
    ):
        raise TypeError(f"{name} must be a lowercase 40-hex Git object ID")
    return checked


def _capability(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=128)
    if checked != checked.lower() or any(
        character not in _CAPABILITY_CHARACTERS for character in checked
    ):
        raise TypeError(f"{name} must be a canonical lowercase capability ID")
    return checked


def validate_capabilities_v1(value: object, name: str) -> tuple[str, ...]:
    """Validate one sorted, unique, bounded capability tuple."""

    if type(value) is not tuple:
        raise TypeError(f"{name} must be an exact tuple")
    if len(value) > MAX_TAU_PROFILE_CAPABILITIES_V1:
        raise TauProfileValueError(f"{name} exceeds its collection bound")
    checked = tuple(_capability(item, f"{name}[{index}]") for index, item in enumerate(value))
    if checked != tuple(sorted(set(checked))):
        raise TauProfileValueError(f"{name} must be canonical, sorted, and unique")
    return checked


def capability_manifest_root_v1(capabilities: object) -> str:
    """Derive the exact identity of a canonical capability tuple."""

    checked = validate_capabilities_v1(capabilities, "capabilities")
    return sha256(
        b"zenodex/fcis/m6/tau-capability-manifest/v1\x00" + canonical_json_bytes(list(checked))
    ).hexdigest()


def _profile_body(profile: "TauIntegrationProfileV1") -> dict[str, object]:
    return {
        "schema": TAU_INTEGRATION_PROFILE_SCHEMA_V1,
        "network_id": profile.network_id,
        "protocol_version": profile.protocol_version,
        "source_origin": profile.source_origin,
        "source_commit": profile.source_commit,
        "source_tree": profile.source_tree,
        "parser_origin": profile.parser_origin,
        "parser_commit": profile.parser_commit,
        "version_output": profile.version_output,
        "binary_sha256": profile.binary_sha256,
        "language_semantics_root": profile.language_semantics_root,
        "governance_root": profile.governance_root,
        "rule_history_root": profile.rule_history_root,
        "capabilities": list(profile.capabilities),
        "capability_manifest_root": profile.capability_manifest_root,
        "refinement_root": profile.refinement_root,
        "resource_envelope_root": profile.resource_envelope_root,
        "proof_format_root": profile.proof_format_root,
        "asset_semantics_root": profile.asset_semantics_root,
        "finality_semantics_root": profile.finality_semantics_root,
        "rule_change_procedure_root": profile.rule_change_procedure_root,
    }


def derive_tau_integration_profile_root_v1(profile: "TauIntegrationProfileV1") -> str:
    """Derive one profile identity from every governed profile field."""

    return sha256(
        b"zenodex/fcis/m6/tau-integration-profile/v1\x00"
        + canonical_json_bytes(_profile_body(profile))
    ).hexdigest()


@final
@dataclass(frozen=True, slots=True)
class TauIntegrationProfileV1:
    """Pinned Tau semantics and source identity; never runtime authority."""

    network_id: str
    protocol_version: str
    source_origin: str
    source_commit: str
    source_tree: str
    parser_origin: str
    parser_commit: str
    version_output: str
    binary_sha256: str
    language_semantics_root: str
    governance_root: str
    rule_history_root: str
    capabilities: tuple[str, ...]
    capability_manifest_root: str
    refinement_root: str
    resource_envelope_root: str
    proof_format_root: str
    asset_semantics_root: str
    finality_semantics_root: str
    rule_change_procedure_root: str
    profile_root: str

    def __post_init__(self) -> None:
        for name in (
            "network_id",
            "protocol_version",
            "source_origin",
            "parser_origin",
            "version_output",
        ):
            _text(object.__getattribute__(self, name), name)
        _git_oid(self.source_commit, "source_commit")
        _git_oid(self.source_tree, "source_tree")
        _git_oid(self.parser_commit, "parser_commit")
        for name in (
            "binary_sha256",
            "language_semantics_root",
            "governance_root",
            "rule_history_root",
            "capability_manifest_root",
            "refinement_root",
            "resource_envelope_root",
            "proof_format_root",
            "asset_semantics_root",
            "finality_semantics_root",
            "rule_change_procedure_root",
            "profile_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        capabilities = validate_capabilities_v1(self.capabilities, "capabilities")
        if self.capability_manifest_root != capability_manifest_root_v1(capabilities):
            raise TauProfileValueError("capability_manifest_root does not rederive")
        if self.profile_root != derive_tau_integration_profile_root_v1(self):
            raise TauProfileValueError("profile_root does not rederive")

    @property
    def writer_profile_root(self) -> str:
        """Return the J07-compatible exact profile identity."""

        self.__post_init__()
        return self.profile_root

    def to_wire(self) -> dict[str, object]:
        """Return the closed canonical profile projection."""

        self.__post_init__()
        return {**_profile_body(self), "profile_root": self.profile_root}


def build_tau_integration_profile_v1(
    *,
    network_id: str,
    protocol_version: str,
    source_origin: str,
    source_commit: str,
    source_tree: str,
    parser_origin: str,
    parser_commit: str,
    version_output: str,
    binary_sha256: str,
    language_semantics_root: str,
    governance_root: str,
    rule_history_root: str,
    capabilities: tuple[str, ...],
    refinement_root: str,
    resource_envelope_root: str,
    proof_format_root: str,
    asset_semantics_root: str,
    finality_semantics_root: str,
    rule_change_procedure_root: str,
) -> TauIntegrationProfileV1:
    """Build a self-consistent profile value without granting verification."""

    capability_root = capability_manifest_root_v1(capabilities)
    placeholder = TauIntegrationProfileV1.__new__(TauIntegrationProfileV1)
    values: dict[str, object] = {
        "network_id": network_id,
        "protocol_version": protocol_version,
        "source_origin": source_origin,
        "source_commit": source_commit,
        "source_tree": source_tree,
        "parser_origin": parser_origin,
        "parser_commit": parser_commit,
        "version_output": version_output,
        "binary_sha256": binary_sha256,
        "language_semantics_root": language_semantics_root,
        "governance_root": governance_root,
        "rule_history_root": rule_history_root,
        "capabilities": capabilities,
        "capability_manifest_root": capability_root,
        "refinement_root": refinement_root,
        "resource_envelope_root": resource_envelope_root,
        "proof_format_root": proof_format_root,
        "asset_semantics_root": asset_semantics_root,
        "finality_semantics_root": finality_semantics_root,
        "rule_change_procedure_root": rule_change_procedure_root,
    }
    for name, value in values.items():
        object.__setattr__(placeholder, name, value)
    object.__setattr__(placeholder, "profile_root", "0" * 64)
    profile_root = derive_tau_integration_profile_root_v1(placeholder)
    return TauIntegrationProfileV1(
        **values,  # type: ignore[arg-type]
        profile_root=profile_root,
    )


__all__ = (
    "MAX_TAU_PROFILE_CAPABILITIES_V1",
    "MAX_TAU_PROFILE_TEXT_BYTES_V1",
    "TAU_INTEGRATION_PROFILE_SCHEMA_V1",
    "TauIntegrationObservationV1",
    "TauIntegrationProfileV1",
    "TauOperationClassV1",
    "TauProfileValueError",
    "TauSubstrateDispositionV1",
    "build_tau_integration_profile_v1",
    "capability_manifest_root_v1",
    "derive_tau_integration_profile_root_v1",
    "validate_capabilities_v1",
)
