"""Typed deployment-boundary audit for the unmounted FCIS M6 slice.

K07 binds a deployment audit to the current K04 topology, K06 legacy seal, and
K01 entrypoint roots. It reports direct protected-table writers and credential
surface findings as typed gaps. The model deliberately refuses to convert a
source inventory into a clean production claim.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Final, TypeAlias

from src.state.canonical import canonical_json_bytes

FCIS_M6_K07_SCHEMA_V1: Final = "zenodex/fcis/m6/k07/deployment-audit/v1"
FCIS_M6_K07_ROOT_SCHEMA_V1: Final = "zenodex/fcis/m6/k07/audit-root/v1"
K07_MAX_PATHS_V1: Final = 128
K07_MAX_BINDINGS_V1: Final = 32
K07_MAX_FINDINGS_V1: Final = 256
K07_MAX_LINE_V1: Final = (1 << 32) - 1
_HEX: Final = frozenset("0123456789abcdef")
_K07_AUDIT_CONSTRUCTION_TOKEN_V1 = object()
_K07_CLEAN_CONSTRUCTION_TOKEN_V1 = object()


class K07Error(ValueError):
    """Raised when a K07 audit value is outside its closed language."""


class K07AuditStatusV1(str, Enum):
    """The only two outcomes of the deployment-boundary audit."""

    PASS = "PASS"
    GAP = "GAP"


class K07FindingKindV1(str, Enum):
    """Closed finding classes emitted by the source/deployment audit."""

    DIRECT_PROTECTED_WRITER = "direct_protected_writer"
    CREDENTIAL_POLICY_GAP = "credential_policy_gap"
    MISSING_SOURCE = "missing_source"
    MISSING_LAUNCH_BINDING = "missing_launch_binding"
    UNTRACKED_WORKER = "untracked_worker"
    MISSING_REQUIRED_MARKER = "missing_required_marker"


def _text(value: object, name: str, *, maximum_bytes: int = 512) -> str:
    if type(value) is not str or not value:
        raise K07Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise K07Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise K07Error(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise K07Error(f"{name} contains a control character")
    return value


def _path(value: object, name: str) -> str:
    checked = _text(value, name)
    if "\\" in checked or checked.startswith("/") or ".." in checked.split("/"):
        raise K07Error(f"{name} is not a safe repository-relative path")
    if any(part in {"", "."} for part in checked.split("/")):
        raise K07Error(f"{name} is not canonical")
    return checked


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if (
        len(checked) != 64
        or checked != checked.lower()
        or any(character not in _HEX for character in checked)
    ):
        raise K07Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _u32(value: object, name: str, *, positive: bool = False) -> int:
    minimum = 1 if positive else 0
    if type(value) is not int or value < minimum or value > K07_MAX_LINE_V1:
        raise K07Error(f"{name} is outside its closed u32 bound")
    return value


def _ordered_paths(value: object, name: str, *, maximum: int) -> tuple[str, ...]:
    if type(value) is not tuple or not value:
        raise K07Error(f"{name} must be a nonempty exact tuple")
    if len(value) > maximum:
        raise K07Error(f"{name} exceeds its closed collection bound")
    checked = tuple(_path(item, f"{name}[{index}]") for index, item in enumerate(value))
    if len(set(checked)) != len(checked):
        raise K07Error(f"{name} contains duplicates")
    if checked != tuple(sorted(checked, key=lambda item: item.encode("utf-8"))):
        raise K07Error(f"{name} is not canonically ordered")
    return checked


def _ordered_texts(value: object, name: str, *, maximum: int) -> tuple[str, ...]:
    if type(value) is not tuple or not value:
        raise K07Error(f"{name} must be a nonempty exact tuple")
    if len(value) > maximum:
        raise K07Error(f"{name} exceeds its closed collection bound")
    checked = tuple(_text(item, f"{name}[{index}]") for index, item in enumerate(value))
    if len(set(checked)) != len(checked):
        raise K07Error(f"{name} contains duplicates")
    if checked != tuple(sorted(checked, key=lambda item: item.encode("utf-8"))):
        raise K07Error(f"{name} is not canonically ordered")
    return checked


def _derive(domain: str, payload: dict[str, object]) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(payload)).hexdigest()


@dataclass(frozen=True, slots=True)
class K07LaunchBindingV1:
    """One explicitly declared process launch binding."""

    launcher_id: str
    source_path: str
    command: str
    publisher_id: str
    effect_capable: bool

    def __post_init__(self) -> None:
        _text(self.launcher_id, "launcher_id", maximum_bytes=128)
        _path(self.source_path, "source_path")
        _text(self.command, "command", maximum_bytes=512)
        _text(self.publisher_id, "publisher_id", maximum_bytes=128)
        if type(self.effect_capable) is not bool:
            raise K07Error("effect_capable has the wrong exact type")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "launcher_id": self.launcher_id,
            "source_path": self.source_path,
            "command": self.command,
            "publisher_id": self.publisher_id,
            "effect_capable": self.effect_capable,
        }


@dataclass(frozen=True, slots=True)
class K07FindingV1:
    """One source-bound deployment gap with an exact location and marker."""

    kind: K07FindingKindV1
    path: str
    line: int
    marker: str

    def __post_init__(self) -> None:
        if type(self.kind) is not K07FindingKindV1:
            raise K07Error("finding kind has the wrong exact type")
        _path(self.path, "finding.path")
        _u32(self.line, "finding.line", positive=True)
        _text(self.marker, "finding.marker", maximum_bytes=256)

    def sort_key(self) -> tuple[bytes, str, bytes, int]:
        return (
            self.path.encode("utf-8"),
            self.kind.value,
            self.marker.encode("utf-8"),
            self.line,
        )

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "kind": self.kind.value,
            "path": self.path,
            "line": self.line,
            "marker": self.marker,
        }


@dataclass(frozen=True, slots=True)
class K07DeploymentAuditV1:
    """Complete immutable result of one deployment-boundary audit."""

    k04_topology_root: str
    k06_seal_root: str
    k01_entrypoint_inventory_root: str
    audited_paths: tuple[str, ...]
    deployment_paths: tuple[str, ...]
    launch_bindings: tuple[K07LaunchBindingV1, ...]
    findings: tuple[K07FindingV1, ...]
    status: K07AuditStatusV1
    audit_root: str
    _construction_token: InitVar[object | None] = None

    def _validate(self) -> None:
        _digest(self.k04_topology_root, "k04_topology_root")
        _digest(self.k06_seal_root, "k06_seal_root")
        _digest(
            self.k01_entrypoint_inventory_root,
            "k01_entrypoint_inventory_root",
        )
        audited = _ordered_paths(self.audited_paths, "audited_paths", maximum=K07_MAX_PATHS_V1)
        deployment = _ordered_paths(
            self.deployment_paths,
            "deployment_paths",
            maximum=K07_MAX_PATHS_V1,
        )
        if not set(deployment).issubset(set(audited)):
            raise K07Error("deployment paths must be covered by audited paths")
        if type(self.launch_bindings) is not tuple:
            raise K07Error("launch_bindings must be an exact tuple")
        if len(self.launch_bindings) > K07_MAX_BINDINGS_V1:
            raise K07Error("launch_bindings exceeds its closed bound")
        for index, binding in enumerate(self.launch_bindings):
            if type(binding) is not K07LaunchBindingV1:
                raise K07Error(f"launch_bindings[{index}] has the wrong exact type")
            binding.__post_init__()
        binding_ids = tuple(binding.launcher_id for binding in self.launch_bindings)
        if len(set(binding_ids)) != len(binding_ids):
            raise K07Error("launch_bindings contains duplicate launcher IDs")
        if binding_ids != tuple(sorted(binding_ids, key=lambda item: item.encode("utf-8"))):
            raise K07Error("launch_bindings are not canonically ordered")
        if type(self.findings) is not tuple:
            raise K07Error("findings must be an exact tuple")
        if len(self.findings) > K07_MAX_FINDINGS_V1:
            raise K07Error("findings exceeds its closed bound")
        for index, finding in enumerate(self.findings):
            if type(finding) is not K07FindingV1:
                raise K07Error(f"findings[{index}] has the wrong exact type")
            finding.__post_init__()
        if self.findings != tuple(sorted(self.findings, key=K07FindingV1.sort_key)):
            raise K07Error("findings are not canonically ordered")
        if len({finding.sort_key() for finding in self.findings}) != len(self.findings):
            raise K07Error("findings contain duplicates")
        if type(self.status) is not K07AuditStatusV1:
            raise K07Error("status has the wrong exact type")
        expected_status = K07AuditStatusV1.GAP if self.findings else K07AuditStatusV1.PASS
        if self.status is not expected_status:
            raise K07Error("status does not match the finding set")
        expected_root = audit_root_v1_from_values(
            self.k04_topology_root,
            self.k06_seal_root,
            self.k01_entrypoint_inventory_root,
            audited,
            deployment,
            self.launch_bindings,
            self.findings,
            self.status,
        )
        if self.audit_root != expected_root:
            raise K07Error("audit root does not bind the complete audit")
        _digest(self.audit_root, "audit_root")

    def __post_init__(self, construction_token: object | None) -> None:
        self._validate()
        if construction_token is not _K07_AUDIT_CONSTRUCTION_TOKEN_V1:
            raise K07Error("only the checked builder may construct a deployment audit")

    def to_wire(self) -> dict[str, object]:
        self._validate()
        return {
            "schema": FCIS_M6_K07_SCHEMA_V1,
            "k04_topology_root": self.k04_topology_root,
            "k06_seal_root": self.k06_seal_root,
            "k01_entrypoint_inventory_root": self.k01_entrypoint_inventory_root,
            "audited_paths": list(self.audited_paths),
            "deployment_paths": list(self.deployment_paths),
            "launch_bindings": [binding.to_wire() for binding in self.launch_bindings],
            "findings": [finding.to_wire() for finding in self.findings],
            "status": self.status.value,
            "audit_root": self.audit_root,
        }


def audit_root_v1_from_values(
    k04_topology_root: str,
    k06_seal_root: str,
    k01_entrypoint_inventory_root: str,
    audited_paths: tuple[str, ...],
    deployment_paths: tuple[str, ...],
    launch_bindings: tuple[K07LaunchBindingV1, ...],
    findings: tuple[K07FindingV1, ...],
    status: K07AuditStatusV1,
) -> str:
    """Derive the root of the full audit result without a root field."""

    return _derive(
        FCIS_M6_K07_ROOT_SCHEMA_V1,
        {
            "schema": FCIS_M6_K07_SCHEMA_V1,
            "k04_topology_root": k04_topology_root,
            "k06_seal_root": k06_seal_root,
            "k01_entrypoint_inventory_root": k01_entrypoint_inventory_root,
            "audited_paths": list(audited_paths),
            "deployment_paths": list(deployment_paths),
            "launch_bindings": [binding.to_wire() for binding in launch_bindings],
            "findings": [finding.to_wire() for finding in findings],
            "status": status.value,
        },
    )


_K07_REGISTERED_AUDITS: dict[str, list[tuple[object, bytes]]] = {}


def _mint_deployment_audit_v1(
    *,
    k04_topology_root: str,
    k06_seal_root: str,
    k01_entrypoint_inventory_root: str,
    audited_paths: tuple[str, ...],
    deployment_paths: tuple[str, ...],
    launch_bindings: tuple[K07LaunchBindingV1, ...],
    findings: tuple[K07FindingV1, ...],
    status: K07AuditStatusV1,
) -> K07DeploymentAuditV1:
    """Mint one audit through the checked builder boundary."""

    audit_root = audit_root_v1_from_values(
        k04_topology_root,
        k06_seal_root,
        k01_entrypoint_inventory_root,
        audited_paths,
        deployment_paths,
        launch_bindings,
        findings,
        status,
    )
    audit = K07DeploymentAuditV1(
        k04_topology_root=k04_topology_root,
        k06_seal_root=k06_seal_root,
        k01_entrypoint_inventory_root=k01_entrypoint_inventory_root,
        audited_paths=audited_paths,
        deployment_paths=deployment_paths,
        launch_bindings=launch_bindings,
        findings=findings,
        status=status,
        audit_root=audit_root,
        _construction_token=_K07_AUDIT_CONSTRUCTION_TOKEN_V1,
    )
    snapshot = canonical_json_bytes(audit.to_wire())
    registered = _K07_REGISTERED_AUDITS.setdefault(audit_root, [])
    if any(entry[1] != snapshot for entry in registered):
        raise K07Error("audit root collision")
    registered.append((audit, snapshot))
    return audit


def is_verified_deployment_audit_v1(value: object) -> bool:
    """Require fresh validation and the exact verifier-owned audit object."""

    if type(value) is not K07DeploymentAuditV1:
        return False
    try:
        value._validate()
        registered = _K07_REGISTERED_AUDITS.get(value.audit_root, [])
        snapshot = canonical_json_bytes(value.to_wire())
        return any(entry[0] is value and entry[1] == snapshot for entry in registered)
    except (AttributeError, KeyError, TypeError, ValueError):
        return False


@dataclass(frozen=True, slots=True)
class K07AuditCleanV1:
    """Typed success only available for an empty-finding audit."""

    audit_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, construction_token: object | None) -> None:
        _digest(self.audit_root, "clean.audit_root")
        if construction_token is not _K07_CLEAN_CONSTRUCTION_TOKEN_V1:
            raise K07Error("only the audit gate may construct a clean decision")


@dataclass(frozen=True, slots=True)
class K07AuditBlockedV1:
    """Typed blocking result preserving the audit gap count."""

    audit_root: str
    finding_count: int

    def __post_init__(self) -> None:
        _digest(self.audit_root, "blocked.audit_root")
        _u32(self.finding_count, "blocked.finding_count", positive=True)


K07AuditDecisionV1: TypeAlias = K07AuditCleanV1 | K07AuditBlockedV1


def require_clean_deployment_audit_v1(value: object) -> K07AuditDecisionV1:
    """Refuse any deployment claim while the audit contains a finding."""

    if type(value) is not K07DeploymentAuditV1:
        raise K07Error("deployment audit has the wrong exact type")
    if not is_verified_deployment_audit_v1(value):
        raise K07Error("deployment audit is not verifier-owned")
    if value.status is K07AuditStatusV1.GAP:
        return K07AuditBlockedV1(value.audit_root, len(value.findings))
    return K07AuditCleanV1(
        value.audit_root,
        _construction_token=_K07_CLEAN_CONSTRUCTION_TOKEN_V1,
    )


__all__ = [
    "FCIS_M6_K07_SCHEMA_V1",
    "K07AuditBlockedV1",
    "K07AuditCleanV1",
    "K07AuditDecisionV1",
    "K07AuditStatusV1",
    "K07DeploymentAuditV1",
    "K07Error",
    "K07FindingKindV1",
    "K07FindingV1",
    "K07LaunchBindingV1",
    "audit_root_v1_from_values",
    "is_verified_deployment_audit_v1",
    "require_clean_deployment_audit_v1",
]
