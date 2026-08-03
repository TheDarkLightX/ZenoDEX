"""Fail-closed legacy-path seal for the unmounted FCIS M6 boundary.

K06 turns the reviewed K03 scan, D05 topology root, K01 entrypoint root, and
J07 switch relation into one verifier-owned seal.  A seal can only be minted
by the module's bounded builder.  Point-of-use verification rechecks every
field and a private snapshot registry, so a caller-created or mutated object
cannot be treated as build or runtime authority.

This is a research model.  It does not authenticate a production process,
remove a symbol from a deployed image, or authorize value movement.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Final, TypeAlias

from src.core import fcis_durable_retraction as dra
from src.state.canonical import canonical_json_bytes

FCIS_M6_K06_SCHEMA_V1: Final = "zenodex/fcis/m6/k06/legacy-seal/v1"
FCIS_M6_K06_POLICY_SCHEMA_V1: Final = "zenodex/fcis/m6/k06/seal-policy/v1"
FCIS_M6_K06_FEATURE_SCHEMA_V1: Final = "zenodex/fcis/m6/k06/feature-flag/v1"
FCIS_M6_K06_SEAL_ROOT_SCHEMA_V1: Final = "zenodex/fcis/m6/k06/seal-root/v1"
FCIS_M6_K06_ADMISSION_ROOT_SCHEMA_V1: Final = "zenodex/fcis/m6/k06/runtime-admission/v1"
K06_MAX_SYMBOLS_V1: Final = 128
K06_MAX_WRITERS_V1: Final = 16
K06_MAX_EPOCH_V1: Final = (1 << 32) - 1
K06_LEGACY_FLAG_ID_V1: Final = "legacy_publishers_enabled"
K06_FINAL_PHASE_V1: Final = dra.MigrationPhaseV1.LEGACY_DISABLED
_HEX: Final = frozenset("0123456789abcdef")


class K06Error(ValueError):
    """Raised when a K06 research value is outside its closed language."""


class K06WriterV1(str, Enum):
    """The only writer identities admitted by the bounded runtime gate."""

    LEGACY = "LEGACY"
    TARGET = "TARGET"


class K06RejectCodeV1(str, Enum):
    """Typed fail-closed outcomes for build and runtime admission."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    SEAL_UNVERIFIED = "seal_unverified"
    WRONG_PHASE = "wrong_phase"
    STALE_EPOCH = "stale_epoch"
    TOPOLOGY_ROOT_MISMATCH = "topology_root_mismatch"
    INVENTORY_ROOT_MISMATCH = "inventory_root_mismatch"
    FEATURE_FLAG_MISMATCH = "feature_flag_mismatch"
    LEGACY_WRITER_DISABLED = "legacy_writer_disabled"
    WRITER_PROFILE_MISMATCH = "writer_profile_mismatch"
    UNKNOWN_WRITER = "unknown_writer"
    SOURCE_SCAN_FAILED = "source_scan_failed"
    UPSTREAM_ROOT_MISMATCH = "upstream_root_mismatch"


def _text(value: object, name: str, *, maximum_bytes: int = 512) -> str:
    if type(value) is not str or not value:
        raise K06Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise K06Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise K06Error(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise K06Error(f"{name} contains a control character")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if (
        len(checked) != 64
        or checked != checked.lower()
        or any(character not in _HEX for character in checked)
    ):
        raise K06Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _u32(value: object, name: str, *, positive: bool = False) -> int:
    minimum = 1 if positive else 0
    if type(value) is not int or value < minimum or value > K06_MAX_EPOCH_V1:
        raise K06Error(f"{name} is outside its closed u32 bound")
    return value


def _ordered_strings(
    value: object,
    name: str,
    *,
    maximum: int,
    allow_empty: bool = False,
    path: bool = False,
) -> tuple[str, ...]:
    if type(value) is not tuple:
        raise K06Error(f"{name} must be an exact tuple")
    if not allow_empty and not value:
        raise K06Error(f"{name} must be nonempty")
    if len(value) > maximum:
        raise K06Error(f"{name} exceeds its closed collection bound")
    checked = tuple(
        _text(item, f"{name}[{index}]", maximum_bytes=512) for index, item in enumerate(value)
    )
    if path:
        for item in checked:
            if "\\" in item or item.startswith("/") or ".." in item.split("/"):
                raise K06Error(f"{name} contains an unsafe repository path")
            if any(part in {"", "."} for part in item.split("/")):
                raise K06Error(f"{name} contains a noncanonical repository path")
    if len(set(checked)) != len(checked):
        raise K06Error(f"{name} contains duplicates")
    if checked != tuple(sorted(checked, key=lambda item: item.encode("utf-8"))):
        raise K06Error(f"{name} is not canonically ordered")
    return checked


def _derive(domain: str, payload: dict[str, object]) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(payload)).hexdigest()


@dataclass(frozen=True, slots=True)
class K06LegacySealPolicyV1:
    """Exact source and authority roots covered by one K06 seal."""

    k03_policy_root: str
    k03_scan_root: str
    d05_inventory_root: str
    d05_topology_root: str
    k01_entrypoint_inventory_root: str
    j07_switch_root: str
    j07_post_context_root: str
    target_writer_profile_root: str
    unique_port_id: str
    legacy_symbol_ids: tuple[str, ...]
    legacy_allowed_paths: tuple[str, ...]
    sealed_symbol_ids: tuple[str, ...]
    target_writer_ids: tuple[str, ...]

    def __post_init__(self) -> None:
        for name in (
            "k03_policy_root",
            "k03_scan_root",
            "d05_inventory_root",
            "d05_topology_root",
            "k01_entrypoint_inventory_root",
            "j07_switch_root",
            "j07_post_context_root",
            "target_writer_profile_root",
        ):
            _digest(getattr(self, name), name)
        _text(self.unique_port_id, "unique_port_id")
        legacy = _ordered_strings(
            self.legacy_symbol_ids,
            "legacy_symbol_ids",
            maximum=K06_MAX_SYMBOLS_V1,
        )
        _ordered_strings(
            self.legacy_allowed_paths,
            "legacy_allowed_paths",
            maximum=K06_MAX_SYMBOLS_V1,
            path=True,
        )
        sealed = _ordered_strings(
            self.sealed_symbol_ids,
            "sealed_symbol_ids",
            maximum=K06_MAX_SYMBOLS_V1,
        )
        target = _ordered_strings(
            self.target_writer_ids,
            "target_writer_ids",
            maximum=K06_MAX_WRITERS_V1,
        )
        if sealed != legacy:
            raise K06Error("sealed_symbol_ids must equal legacy_symbol_ids")
        if self.unique_port_id not in target:
            raise K06Error("target_writer_ids must contain the unique port")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_K06_POLICY_SCHEMA_V1,
            "k03_policy_root": self.k03_policy_root,
            "k03_scan_root": self.k03_scan_root,
            "d05_inventory_root": self.d05_inventory_root,
            "d05_topology_root": self.d05_topology_root,
            "k01_entrypoint_inventory_root": self.k01_entrypoint_inventory_root,
            "j07_switch_root": self.j07_switch_root,
            "j07_post_context_root": self.j07_post_context_root,
            "target_writer_profile_root": self.target_writer_profile_root,
            "unique_port_id": self.unique_port_id,
            "legacy_symbol_ids": list(self.legacy_symbol_ids),
            "legacy_allowed_paths": list(self.legacy_allowed_paths),
            "sealed_symbol_ids": list(self.sealed_symbol_ids),
            "target_writer_ids": list(self.target_writer_ids),
        }


def seal_policy_root_v1(policy: K06LegacySealPolicyV1) -> str:
    """Derive the canonical root of the K06 upstream-bound policy."""

    return _derive("zenodex/fcis/m6/k06/policy-root/v1", policy.to_wire())


@dataclass(frozen=True, slots=True)
class K06FeatureFlagV1:
    """Authenticated feature state covered by upstream topology roots."""

    flag_id: str
    enabled: bool
    authority_epoch: int
    seal_policy_root: str
    d05_topology_root: str
    k01_entrypoint_inventory_root: str
    target_writer_profile_root: str

    def __post_init__(self) -> None:
        if self.flag_id != K06_LEGACY_FLAG_ID_V1:
            raise K06Error("feature flag ID is not the exact legacy flag")
        if type(self.enabled) is not bool:
            raise K06Error("feature flag enabled value has the wrong exact type")
        _u32(self.authority_epoch, "feature.authority_epoch", positive=True)
        for name in (
            "seal_policy_root",
            "d05_topology_root",
            "k01_entrypoint_inventory_root",
            "target_writer_profile_root",
        ):
            _digest(getattr(self, name), f"feature.{name}")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_K06_FEATURE_SCHEMA_V1,
            "flag_id": self.flag_id,
            "enabled": self.enabled,
            "authority_epoch": self.authority_epoch,
            "seal_policy_root": self.seal_policy_root,
            "d05_topology_root": self.d05_topology_root,
            "k01_entrypoint_inventory_root": self.k01_entrypoint_inventory_root,
            "target_writer_profile_root": self.target_writer_profile_root,
        }


def feature_flag_root_v1(flag: K06FeatureFlagV1) -> str:
    """Derive the root bound into build and runtime feature checks."""

    return _derive("zenodex/fcis/m6/k06/feature-root/v1", flag.to_wire())


_K06_SEAL_CONSTRUCTION_TOKEN_V1 = object()
_K06_REGISTERED_SEALS: dict[str, list[tuple[object, bytes]]] = {}


@dataclass(frozen=True, slots=True)
class K06LegacySealCertificateV1:
    """Verifier-owned certificate that legacy symbols are sealed."""

    policy: K06LegacySealPolicyV1
    feature_flag: K06FeatureFlagV1
    phase: dra.MigrationPhaseV1
    authority_epoch: int
    reachable_legacy_symbol_ids: tuple[str, ...]
    sealed_symbol_ids: tuple[str, ...]
    source_scan_issues: tuple[str, ...]
    seal_root: str
    _construction_token: InitVar[object | None] = None

    def _validate(self) -> None:
        if type(self.policy) is not K06LegacySealPolicyV1:
            raise K06Error("seal policy has the wrong exact type")
        if type(self.feature_flag) is not K06FeatureFlagV1:
            raise K06Error("seal feature flag has the wrong exact type")
        if type(self.phase) is not dra.MigrationPhaseV1:
            raise K06Error("seal phase has the wrong exact type")
        if self.phase is not K06_FINAL_PHASE_V1:
            raise K06Error("seal must be issued only at LEGACY_DISABLED")
        _u32(self.authority_epoch, "seal.authority_epoch", positive=True)
        reachable = _ordered_strings(
            self.reachable_legacy_symbol_ids,
            "reachable_legacy_symbol_ids",
            maximum=K06_MAX_SYMBOLS_V1,
            allow_empty=True,
        )
        sealed = _ordered_strings(
            self.sealed_symbol_ids,
            "seal.sealed_symbol_ids",
            maximum=K06_MAX_SYMBOLS_V1,
        )
        issues = _ordered_strings(
            self.source_scan_issues,
            "source_scan_issues",
            maximum=K06_MAX_SYMBOLS_V1,
            allow_empty=True,
        )
        if reachable:
            raise K06Error("legacy symbols remain reachable")
        if sealed != self.policy.sealed_symbol_ids:
            raise K06Error("seal symbols differ from the policy")
        if issues:
            raise K06Error("K03 source scan contains issues")
        if self.feature_flag.enabled:
            raise K06Error("legacy feature flag must be disabled")
        if self.feature_flag.authority_epoch != self.authority_epoch:
            raise K06Error("feature flag epoch differs from seal epoch")
        if self.feature_flag.seal_policy_root != seal_policy_root_v1(self.policy):
            raise K06Error("feature flag policy root differs from seal policy")
        if self.feature_flag.d05_topology_root != self.policy.d05_topology_root:
            raise K06Error("feature flag topology root differs from policy")
        if (
            self.feature_flag.k01_entrypoint_inventory_root
            != self.policy.k01_entrypoint_inventory_root
        ):
            raise K06Error("feature flag inventory root differs from policy")
        if self.feature_flag.target_writer_profile_root != self.policy.target_writer_profile_root:
            raise K06Error("feature flag writer root differs from policy")
        expected_root = _seal_root_from_values(
            self.policy,
            self.feature_flag,
            self.phase,
            self.authority_epoch,
            reachable,
            sealed,
            issues,
        )
        if self.seal_root != expected_root:
            raise K06Error("seal root does not bind the complete certificate")
        _digest(self.seal_root, "seal_root")

    def __post_init__(self, construction_token: object | None) -> None:
        self._validate()
        if construction_token is not _K06_SEAL_CONSTRUCTION_TOKEN_V1:
            raise K06Error("only the verifier may construct a K06 seal")

    def to_wire(self) -> dict[str, object]:
        self._validate()
        return {
            "schema": FCIS_M6_K06_SCHEMA_V1,
            "policy": self.policy.to_wire(),
            "policy_root": seal_policy_root_v1(self.policy),
            "feature_flag": self.feature_flag.to_wire(),
            "feature_flag_root": feature_flag_root_v1(self.feature_flag),
            "phase": self.phase.value,
            "authority_epoch": self.authority_epoch,
            "reachable_legacy_symbol_ids": list(self.reachable_legacy_symbol_ids),
            "sealed_symbol_ids": list(self.sealed_symbol_ids),
            "source_scan_issues": list(self.source_scan_issues),
            "seal_root": self.seal_root,
        }


def _seal_body_from_values(
    policy: K06LegacySealPolicyV1,
    feature_flag: K06FeatureFlagV1,
    phase: dra.MigrationPhaseV1,
    authority_epoch: int,
    reachable: tuple[str, ...],
    sealed: tuple[str, ...],
    issues: tuple[str, ...],
) -> dict[str, object]:
    return {
        "schema": FCIS_M6_K06_SCHEMA_V1,
        "policy": policy.to_wire(),
        "policy_root": seal_policy_root_v1(policy),
        "feature_flag": feature_flag.to_wire(),
        "feature_flag_root": feature_flag_root_v1(feature_flag),
        "phase": phase.value,
        "authority_epoch": authority_epoch,
        "reachable_legacy_symbol_ids": list(reachable),
        "sealed_symbol_ids": list(sealed),
        "source_scan_issues": list(issues),
    }


def _seal_root_from_values(
    policy: K06LegacySealPolicyV1,
    feature_flag: K06FeatureFlagV1,
    phase: dra.MigrationPhaseV1,
    authority_epoch: int,
    reachable: tuple[str, ...],
    sealed: tuple[str, ...],
    issues: tuple[str, ...],
) -> str:
    return _derive(
        FCIS_M6_K06_SEAL_ROOT_SCHEMA_V1,
        _seal_body_from_values(
            policy, feature_flag, phase, authority_epoch, reachable, sealed, issues
        ),
    )


def _mint_legacy_seal_v1(
    *,
    policy: K06LegacySealPolicyV1,
    feature_flag: K06FeatureFlagV1,
    phase: dra.MigrationPhaseV1,
    authority_epoch: int,
    reachable_legacy_symbol_ids: tuple[str, ...] = (),
    sealed_symbol_ids: tuple[str, ...],
    source_scan_issues: tuple[str, ...] = (),
) -> K06LegacySealCertificateV1:
    """Verifier-only minting function used by the checked builder."""

    root = _seal_root_from_values(
        policy,
        feature_flag,
        phase,
        authority_epoch,
        reachable_legacy_symbol_ids,
        sealed_symbol_ids,
        source_scan_issues,
    )
    certificate = K06LegacySealCertificateV1(
        policy=policy,
        feature_flag=feature_flag,
        phase=phase,
        authority_epoch=authority_epoch,
        reachable_legacy_symbol_ids=reachable_legacy_symbol_ids,
        sealed_symbol_ids=sealed_symbol_ids,
        source_scan_issues=source_scan_issues,
        seal_root=root,
        _construction_token=_K06_SEAL_CONSTRUCTION_TOKEN_V1,
    )
    snapshot = canonical_json_bytes(
        _seal_body_from_values(
            policy,
            feature_flag,
            phase,
            authority_epoch,
            reachable_legacy_symbol_ids,
            sealed_symbol_ids,
            source_scan_issues,
        )
    )
    existing = _K06_REGISTERED_SEALS.setdefault(root, [])
    if any(entry[1] != snapshot for entry in existing):
        raise K06Error("seal root collision")
    existing.append((certificate, snapshot))
    return certificate


def is_verified_legacy_seal_v1(value: object) -> bool:
    """Revalidate a seal and require the verifier-owned snapshot."""

    if type(value) is not K06LegacySealCertificateV1:
        return False
    certificate = value
    try:
        certificate._validate()
        body = _seal_body_from_values(
            certificate.policy,
            certificate.feature_flag,
            certificate.phase,
            certificate.authority_epoch,
            certificate.reachable_legacy_symbol_ids,
            certificate.sealed_symbol_ids,
            certificate.source_scan_issues,
        )
        registered = _K06_REGISTERED_SEALS.get(certificate.seal_root, [])
        snapshot = canonical_json_bytes(body)
        return any(entry[0] is certificate and entry[1] == snapshot for entry in registered)
    except (AttributeError, KeyError, TypeError, ValueError):
        return False


@dataclass(frozen=True, slots=True)
class K06WriterAcceptedV1:
    """A bounded successful target-writer admission result."""

    writer: K06WriterV1
    writer_id: str
    writer_profile_root: str
    authority_epoch: int
    seal_root: str
    feature_flag_root: str
    admission_root: str

    def __post_init__(self) -> None:
        if type(self.writer) is not K06WriterV1 or self.writer is not K06WriterV1.TARGET:
            raise K06Error("accepted writer must be the exact target writer")
        _text(self.writer_id, "accepted.writer_id")
        _digest(self.writer_profile_root, "accepted.writer_profile_root")
        _u32(self.authority_epoch, "accepted.authority_epoch", positive=True)
        _digest(self.seal_root, "accepted.seal_root")
        _digest(self.feature_flag_root, "accepted.feature_flag_root")
        _digest(self.admission_root, "accepted.admission_root")


@dataclass(frozen=True, slots=True)
class K06WriterRejectV1:
    """A typed, immutable fail-closed writer rejection."""

    code: K06RejectCodeV1
    detail: str

    def __post_init__(self) -> None:
        if type(self.code) is not K06RejectCodeV1:
            raise K06Error("rejection code has the wrong exact type")
        _text(self.detail, "rejection.detail", maximum_bytes=256)


K06WriterDecisionV1: TypeAlias = K06WriterAcceptedV1 | K06WriterRejectV1


def _reject(code: K06RejectCodeV1, detail: str) -> K06WriterRejectV1:
    return K06WriterRejectV1(code=code, detail=detail)


def authorize_writer_v1(
    certificate: object,
    *,
    writer: object,
    writer_id: object,
    writer_profile_root: object,
    current_phase: object,
    current_authority_epoch: object,
    current_d05_topology_root: object,
    current_k01_inventory_root: object,
    current_feature_flag: object,
) -> K06WriterDecisionV1:
    """Apply the post-switch build/runtime gate at point of use."""

    if type(certificate) is not K06LegacySealCertificateV1:
        return _reject(K06RejectCodeV1.WRONG_EXACT_TYPE, "certificate type is not K06")
    if not is_verified_legacy_seal_v1(certificate):
        return _reject(K06RejectCodeV1.SEAL_UNVERIFIED, "seal failed fresh verification")
    if type(writer) is not K06WriterV1:
        return _reject(K06RejectCodeV1.UNKNOWN_WRITER, "writer has the wrong exact type")
    if type(current_phase) is not dra.MigrationPhaseV1:
        return _reject(K06RejectCodeV1.WRONG_EXACT_TYPE, "phase has the wrong exact type")
    if type(current_feature_flag) is not K06FeatureFlagV1:
        return _reject(K06RejectCodeV1.WRONG_EXACT_TYPE, "feature flag has the wrong exact type")
    try:
        checked_writer_id = _text(writer_id, "writer_id")
        checked_profile = _digest(writer_profile_root, "writer_profile_root")
        checked_epoch = _u32(current_authority_epoch, "current_authority_epoch", positive=True)
        checked_topology = _digest(current_d05_topology_root, "current_d05_topology_root")
        checked_inventory = _digest(current_k01_inventory_root, "current_k01_inventory_root")
    except K06Error as exc:
        return _reject(K06RejectCodeV1.WRONG_EXACT_TYPE, str(exc))
    certificate._validate()
    if current_phase is not K06_FINAL_PHASE_V1:
        return _reject(K06RejectCodeV1.WRONG_PHASE, "runtime is not at LEGACY_DISABLED")
    if checked_epoch != certificate.authority_epoch:
        return _reject(K06RejectCodeV1.STALE_EPOCH, "authority epoch differs from seal")
    if checked_topology != certificate.policy.d05_topology_root:
        return _reject(K06RejectCodeV1.TOPOLOGY_ROOT_MISMATCH, "topology root differs from seal")
    if checked_inventory != certificate.policy.k01_entrypoint_inventory_root:
        return _reject(K06RejectCodeV1.INVENTORY_ROOT_MISMATCH, "inventory root differs from seal")
    if current_feature_flag != certificate.feature_flag:
        return _reject(K06RejectCodeV1.FEATURE_FLAG_MISMATCH, "feature flag differs from seal")
    if certificate.feature_flag.enabled:
        return _reject(K06RejectCodeV1.FEATURE_FLAG_MISMATCH, "legacy feature is enabled")
    if writer is K06WriterV1.LEGACY:
        return _reject(K06RejectCodeV1.LEGACY_WRITER_DISABLED, "legacy writer is sealed")
    if checked_writer_id not in certificate.policy.target_writer_ids:
        return _reject(K06RejectCodeV1.UNKNOWN_WRITER, "writer ID is outside the sealed target set")
    if checked_profile != certificate.policy.target_writer_profile_root:
        return _reject(K06RejectCodeV1.WRITER_PROFILE_MISMATCH, "writer profile differs from seal")
    admission_root = _derive(
        FCIS_M6_K06_ADMISSION_ROOT_SCHEMA_V1,
        {
            "seal_root": certificate.seal_root,
            "feature_flag_root": feature_flag_root_v1(certificate.feature_flag),
            "phase": current_phase.value,
            "authority_epoch": checked_epoch,
            "writer": writer.value,
            "writer_id": checked_writer_id,
            "writer_profile_root": checked_profile,
        },
    )
    return K06WriterAcceptedV1(
        writer=K06WriterV1.TARGET,
        writer_id=checked_writer_id,
        writer_profile_root=checked_profile,
        authority_epoch=checked_epoch,
        seal_root=certificate.seal_root,
        feature_flag_root=feature_flag_root_v1(certificate.feature_flag),
        admission_root=admission_root,
    )


__all__ = [
    "FCIS_M6_K06_SCHEMA_V1",
    "K06Error",
    "K06FeatureFlagV1",
    "K06LegacySealCertificateV1",
    "K06LegacySealPolicyV1",
    "K06RejectCodeV1",
    "K06WriterAcceptedV1",
    "K06WriterDecisionV1",
    "K06WriterRejectV1",
    "K06WriterV1",
    "authorize_writer_v1",
    "feature_flag_root_v1",
    "is_verified_legacy_seal_v1",
    "seal_policy_root_v1",
]
