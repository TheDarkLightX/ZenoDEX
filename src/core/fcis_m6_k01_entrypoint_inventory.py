"""Typed, source-bound K01 entrypoint inventory for FCIS M6.

K01 records the candidate surfaces that can accept commands, change
authoritative state, or create external effects.  The inventory is deliberately
honest about its boundary: it can bind a reviewed source set and its declared
entrypoints, while runtime reachability and deployment completeness remain
separate audit obligations.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from hashlib import sha256
from typing import Final

from src.state.canonical import canonical_json_bytes

FCIS_M6_K01_SCHEMA_V1: Final = "zenodex/fcis/m6/k01/value-moving-entrypoint-inventory/v1"
FCIS_M6_K01_CONFIG_SCHEMA_V1: Final = (
    "zenodex/fcis/m6/k01/value-moving-entrypoint-inventory-config/v1"
)
FCIS_M6_K01_ROOT_SCHEMA_V1: Final = "zenodex/fcis/m6/k01/entrypoint-inventory-root/v1"
MAX_K01_SOURCES_V1: Final = 256
MAX_K01_ENTRYPOINTS_V1: Final = 128
MAX_K01_NOTES_V1: Final = 32
MAX_SOURCE_BYTES_V1: Final = 64 * 1024 * 1024
_HEX: Final = frozenset("0123456789abcdef")
REQUIRED_PUBLISHER_IDS_V1: Final = frozenset(
    {
        "api_http_ingress",
        "background_outbox_delivery",
        "durable_recovery_worker",
        "durable_state_adapter",
        "entitlement_migration_worker",
        "governance_administrator",
        "legacy_fcis_runtime",
        "operator_cli",
        "proof_verifier",
    }
)


class FCISM6K01Error(ValueError):
    """Raised when a K01 inventory is outside its closed research language."""


class K01SurfaceKindV1(str, Enum):
    """Closed classes of command, authority, datastore, and effect surfaces."""

    API = "api"
    CLI = "cli"
    ADMINISTRATOR = "administrator"
    MIGRATION_WORKER = "migration_worker"
    RECOVERY_WORKER = "recovery_worker"
    PROOF_VERIFIER = "proof_verifier"
    LEGACY_RUNTIME = "legacy_runtime"
    BACKGROUND_OUTBOX_WORKER = "background_outbox_worker"
    DIRECT_DATASTORE_ADAPTER = "direct_datastore_adapter"
    ZUSD_EXTERNAL_SURFACE = "zusd_external_surface"
    PERPS_EXTERNAL_SURFACE = "perps_external_surface"
    AUTOTRADER_EXTERNAL_SURFACE = "autotrader_external_surface"


class K01LegacyStatusV1(str, Enum):
    """How the inventory classifies a surface relative to the M6 target."""

    RESEARCH_MODEL_ONLY = "research_model_only"
    UNVERIFIED_REPOSITORY_CANDIDATE = "unverified_repository_candidate"
    LEGACY_PATH = "legacy_path"
    NOT_VALUE_MOVING = "not_value_moving"
    OUTSIDE_M6_SCOPE = "outside_m6_scope"


class K01ReachabilityV1(str, Enum):
    """Evidence level for runtime reachability of an inventoried surface."""

    UNMOUNTED_RESEARCH_MODEL = "unmounted_research_model"
    UNVERIFIED_REPOSITORY_CANDIDATE = "unverified_repository_candidate"
    LEGACY_REACHABILITY_UNVERIFIED = "legacy_reachability_unverified"
    PROOF_INPUT_ONLY = "proof_input_only"
    OUTSIDE_M6_MOUNT_UNVERIFIED = "outside_m6_mount_unverified"


class K01CommitRequirementV1(str, Enum):
    """Required verified edge before a value-moving surface may publish."""

    AUTHENTICATED_COMMAND_TO_ANF_TO_UNIQUE_COMMIT_PORT = (
        "authenticated_command_to_anf_to_unique_commit_port"
    )
    CANONICAL_REOPEN_AND_FRESH_HEAD_AUTHORIZATION_TO_UNIQUE_COMMIT_PORT = (
        "canonical_reopen_and_fresh_head_authorization_to_unique_commit_port"
    )
    COMMITTED_OUTBOX_TO_VERIFIED_DESTINATION_AND_ACK_PORT = (
        "committed_outbox_to_verified_destination_and_ack_port"
    )
    ANF_VERIFIED_ATOMIC_PUBLICATION_PORT = "anf_verified_atomic_publication_port"
    MIGRATION_MANIFEST_AND_DUAL_CHECK_TO_UNIQUE_COMMIT_PORT = (
        "migration_manifest_and_dual_check_to_unique_commit_port"
    )
    LEGACY_WRITER_MUST_BE_REJECTED_AFTER_AUTHORITY_SWITCH = (
        "legacy_writer_must_be_rejected_after_authority_switch"
    )
    PROOF_VERIFIER_ONLY_NO_VALUE_WRITE = "proof_verifier_only_no_value_write"
    R13_WHOLE_SYSTEM_COMMIT_AND_BACKING_GATE_REQUIRED = (
        "r13_whole_system_commit_and_backing_gate_required"
    )
    OUTSIDE_M6_NO_COMMIT_PORT_CLAIM = "outside_m6_no_commit_port_claim"


class K01CoverageStatusV1(str, Enum):
    """Explicit status of the inventory's completeness boundary."""

    REVIEWED_SOURCE_SET_ONLY = "reviewed_source_set_only"


class K01NoteDispositionV1(str, Enum):
    """Disposition for a coverage or reachability note."""

    UNVERIFIED = "unverified"
    ABSENT_IN_THIS_SLICE = "absent_in_this_slice"
    OUTSIDE_M6 = "outside_m6"
    REQUIRED_NEXT_AUDIT = "required_next_audit"


def _text(value: object, name: str, *, max_bytes: int = 512) -> str:
    if type(value) is not str or not value:
        raise FCISM6K01Error(f"{name} must be a nonempty exact string")
    try:
        raw = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise FCISM6K01Error(f"{name} is not valid UTF-8") from exc
    if len(raw) > max_bytes:
        raise FCISM6K01Error(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise FCISM6K01Error(f"{name} contains a control character")
    return value


def _path(value: object, name: str) -> str:
    path = _text(value, name)
    if "\\" in path or path.startswith("/"):
        raise FCISM6K01Error(f"{name} must be a POSIX relative path")
    parts = path.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise FCISM6K01Error(f"{name} is not a canonical relative path")
    return path


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in _HEX for character in value)
    ):
        raise FCISM6K01Error(f"{name} must be 64 lowercase hexadecimal characters")
    return value


def _exact_int(value: object, name: str, *, maximum: int) -> int:
    if type(value) is not int or value < 0 or value > maximum:
        raise FCISM6K01Error(f"{name} is outside its closed integer bound")
    return value


def _exact_bool(value: object, name: str) -> bool:
    if type(value) is not bool:
        raise FCISM6K01Error(f"{name} must be an exact boolean")
    return value


def _paths(value: object, name: str, *, allow_empty: bool = False) -> tuple[str, ...]:
    if type(value) is not tuple:
        raise FCISM6K01Error(f"{name} must be an exact tuple")
    if not allow_empty and not value:
        raise FCISM6K01Error(f"{name} must be nonempty")
    checked = tuple(_path(item, f"{name}[{index}]") for index, item in enumerate(value))
    if len(set(checked)) != len(checked):
        raise FCISM6K01Error(f"{name} contains duplicate paths")
    if checked != tuple(sorted(checked, key=lambda item: item.encode("utf-8"))):
        raise FCISM6K01Error(f"{name} is not canonically ordered")
    return checked


def _root(domain: str, payload: object) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(payload)).hexdigest()


@dataclass(frozen=True, slots=True, order=True)
class K01SourceV1:
    """One exact source file bound into the K01 evidence set."""

    path: str
    purpose: str
    source_sha256: str
    source_bytes: int

    def __post_init__(self) -> None:
        _path(self.path, "source.path")
        _text(self.purpose, "source.purpose")
        _digest(self.source_sha256, "source.source_sha256")
        _exact_int(self.source_bytes, "source.source_bytes", maximum=MAX_SOURCE_BYTES_V1)

    def to_wire(self) -> dict[str, object]:
        return {
            "path": self.path,
            "purpose": self.purpose,
            "source_sha256": self.source_sha256,
            "source_bytes": self.source_bytes,
        }


@dataclass(frozen=True, slots=True, order=True)
class K01EntrypointV1:
    """One candidate value-moving or authority-relevant entrypoint."""

    publisher_id: str
    kind: K01SurfaceKindV1
    symbol_path: str
    caller: str
    input_type: str
    state_effect_touched: str
    required_anf_commit_port_call: K01CommitRequirementV1
    legacy_status: K01LegacyStatusV1
    runtime_reachability_evidence: K01ReachabilityV1
    value_moving: bool
    authority_sink: bool
    source_paths: tuple[str, ...]

    def __post_init__(self) -> None:
        _text(self.publisher_id, "entrypoint.publisher_id")
        if type(self.kind) is not K01SurfaceKindV1:
            raise FCISM6K01Error("entrypoint.kind has the wrong exact type")
        _text(self.symbol_path, "entrypoint.symbol_path")
        _text(self.caller, "entrypoint.caller")
        _text(self.input_type, "entrypoint.input_type")
        _text(self.state_effect_touched, "entrypoint.state_effect_touched")
        if type(self.required_anf_commit_port_call) is not K01CommitRequirementV1:
            raise FCISM6K01Error("entrypoint.required_anf_commit_port_call has the wrong type")
        if type(self.legacy_status) is not K01LegacyStatusV1:
            raise FCISM6K01Error("entrypoint.legacy_status has the wrong type")
        if type(self.runtime_reachability_evidence) is not K01ReachabilityV1:
            raise FCISM6K01Error("entrypoint.runtime_reachability_evidence has the wrong type")
        _exact_bool(self.value_moving, "entrypoint.value_moving")
        _exact_bool(self.authority_sink, "entrypoint.authority_sink")
        if self.authority_sink and not self.value_moving:
            raise FCISM6K01Error("an authority sink must be value-moving")
        _paths(self.source_paths, "entrypoint.source_paths")
        if self.value_moving and self.required_anf_commit_port_call is (
            K01CommitRequirementV1.PROOF_VERIFIER_ONLY_NO_VALUE_WRITE
        ):
            raise FCISM6K01Error("value-moving entrypoint cannot be proof-only")
        if self.legacy_status is K01LegacyStatusV1.LEGACY_PATH:
            if self.kind is not K01SurfaceKindV1.LEGACY_RUNTIME:
                raise FCISM6K01Error("only a legacy runtime may use legacy_path")
            if (
                self.runtime_reachability_evidence
                is not K01ReachabilityV1.LEGACY_REACHABILITY_UNVERIFIED
            ):
                raise FCISM6K01Error("legacy path reachability must remain explicitly unverified")
            if self.required_anf_commit_port_call is not (
                K01CommitRequirementV1.LEGACY_WRITER_MUST_BE_REJECTED_AFTER_AUTHORITY_SWITCH
            ):
                raise FCISM6K01Error("legacy path must require post-switch rejection")
        if self.kind is K01SurfaceKindV1.PROOF_VERIFIER:
            if self.value_moving or self.authority_sink:
                raise FCISM6K01Error("proof verifier is not a value-moving sink")
            if self.required_anf_commit_port_call is not (
                K01CommitRequirementV1.PROOF_VERIFIER_ONLY_NO_VALUE_WRITE
            ):
                raise FCISM6K01Error("proof verifier must be proof-only")
            if self.runtime_reachability_evidence is not K01ReachabilityV1.PROOF_INPUT_ONLY:
                raise FCISM6K01Error("proof verifier reachability must be proof_input_only")

    def to_wire(self) -> dict[str, object]:
        return {
            "publisher_id": self.publisher_id,
            "kind": self.kind.value,
            "symbol_path": self.symbol_path,
            "caller": self.caller,
            "input_type": self.input_type,
            "state_effect_touched": self.state_effect_touched,
            "required_anf_commit_port_call": self.required_anf_commit_port_call.value,
            "legacy_status": self.legacy_status.value,
            "runtime_reachability_evidence": self.runtime_reachability_evidence.value,
            "value_moving": self.value_moving,
            "authority_sink": self.authority_sink,
            "source_paths": list(self.source_paths),
        }


@dataclass(frozen=True, slots=True, order=True)
class K01CoverageNoteV1:
    """One explicit completeness or reachability boundary."""

    surface_id: str
    disposition: K01NoteDispositionV1
    reason: str
    paths: tuple[str, ...]

    def __post_init__(self) -> None:
        _text(self.surface_id, "coverage_note.surface_id")
        if type(self.disposition) is not K01NoteDispositionV1:
            raise FCISM6K01Error("coverage_note.disposition has the wrong type")
        _text(self.reason, "coverage_note.reason", max_bytes=2048)
        _paths(self.paths, "coverage_note.paths", allow_empty=True)

    def to_wire(self) -> dict[str, object]:
        return {
            "surface_id": self.surface_id,
            "disposition": self.disposition.value,
            "reason": self.reason,
            "paths": list(self.paths),
        }


@dataclass(frozen=True, slots=True, order=True)
class K01InventoryV1:
    """Complete typed projection of the reviewed K01 source set."""

    profile_id: str
    configuration_path: str
    configuration_sha256: str
    coverage_status: K01CoverageStatusV1
    deployment_source_paths: tuple[str, ...]
    sources: tuple[K01SourceV1, ...]
    entrypoints: tuple[K01EntrypointV1, ...]
    coverage_notes: tuple[K01CoverageNoteV1, ...]

    def __post_init__(self) -> None:
        _text(self.profile_id, "profile_id")
        _path(self.configuration_path, "configuration_path")
        _digest(self.configuration_sha256, "configuration_sha256")
        if type(self.coverage_status) is not K01CoverageStatusV1:
            raise FCISM6K01Error("coverage_status has the wrong type")
        _paths(self.deployment_source_paths, "deployment_source_paths")
        if type(self.sources) is not tuple or not self.sources:
            raise FCISM6K01Error("sources must be a nonempty tuple")
        if len(self.sources) > MAX_K01_SOURCES_V1:
            raise FCISM6K01Error("sources exceed the closed bound")
        if tuple(sorted(self.sources, key=lambda item: item.path.encode("utf-8"))) != self.sources:
            raise FCISM6K01Error("sources are not canonically ordered")
        source_paths = tuple(source.path for source in self.sources)
        if len(set(source_paths)) != len(source_paths):
            raise FCISM6K01Error("sources contain duplicate paths")
        source_set = set(source_paths)
        if self.configuration_path not in source_set:
            raise FCISM6K01Error("configuration path is not source-bound")
        if not set(self.deployment_source_paths).issubset(source_set):
            raise FCISM6K01Error("deployment source is absent from the source set")
        if type(self.entrypoints) is not tuple or not self.entrypoints:
            raise FCISM6K01Error("entrypoints must be a nonempty tuple")
        if len(self.entrypoints) > MAX_K01_ENTRYPOINTS_V1:
            raise FCISM6K01Error("entrypoints exceed the closed bound")
        if (
            tuple(sorted(self.entrypoints, key=lambda item: item.publisher_id.encode("utf-8")))
            != self.entrypoints
        ):
            raise FCISM6K01Error("entrypoints are not canonically ordered")
        publisher_ids = tuple(item.publisher_id for item in self.entrypoints)
        if len(set(publisher_ids)) != len(publisher_ids):
            raise FCISM6K01Error("entrypoints contain duplicate publisher IDs")
        missing = REQUIRED_PUBLISHER_IDS_V1.difference(publisher_ids)
        if missing:
            raise FCISM6K01Error(
                "required publisher IDs are missing: "
                + ",".join(sorted(missing, key=lambda item: item.encode("utf-8")))
            )
        for entrypoint in self.entrypoints:
            if not set(entrypoint.source_paths).issubset(source_set):
                raise FCISM6K01Error(
                    f"entrypoint {entrypoint.publisher_id!r} has an unbound source"
                )
        if type(self.coverage_notes) is not tuple or not self.coverage_notes:
            raise FCISM6K01Error("coverage_notes must be nonempty")
        if len(self.coverage_notes) > MAX_K01_NOTES_V1:
            raise FCISM6K01Error("coverage_notes exceed the closed bound")
        if (
            tuple(sorted(self.coverage_notes, key=lambda item: item.surface_id.encode("utf-8")))
            != self.coverage_notes
        ):
            raise FCISM6K01Error("coverage_notes are not canonically ordered")
        note_ids = tuple(item.surface_id for item in self.coverage_notes)
        if len(set(note_ids)) != len(note_ids):
            raise FCISM6K01Error("coverage_notes contain duplicate IDs")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_K01_SCHEMA_V1,
            "profile_id": self.profile_id,
            "configuration_path": self.configuration_path,
            "configuration_sha256": self.configuration_sha256,
            "coverage_status": self.coverage_status.value,
            "deployment_source_paths": list(self.deployment_source_paths),
            "sources": [source.to_wire() for source in self.sources],
            "entrypoints": [entrypoint.to_wire() for entrypoint in self.entrypoints],
            "coverage_notes": [note.to_wire() for note in self.coverage_notes],
        }


def entrypoint_inventory_root_v1(inventory: K01InventoryV1) -> str:
    """Derive the source-bound K01 inventory root."""

    return _root(FCIS_M6_K01_ROOT_SCHEMA_V1, inventory.to_wire())


def inventory_payload_v1(inventory: K01InventoryV1) -> dict[str, object]:
    """Return the canonical generated K01 evidence payload."""

    return {
        **inventory.to_wire(),
        "entrypoint_inventory_root": entrypoint_inventory_root_v1(inventory),
    }


__all__ = [
    "FCIS_M6_K01_CONFIG_SCHEMA_V1",
    "FCIS_M6_K01_ROOT_SCHEMA_V1",
    "FCIS_M6_K01_SCHEMA_V1",
    "FCISM6K01Error",
    "K01CommitRequirementV1",
    "K01CoverageNoteV1",
    "K01CoverageStatusV1",
    "K01EntrypointV1",
    "K01InventoryV1",
    "K01LegacyStatusV1",
    "K01NoteDispositionV1",
    "K01ReachabilityV1",
    "K01SourceV1",
    "K01SurfaceKindV1",
    "REQUIRED_PUBLISHER_IDS_V1",
    "entrypoint_inventory_root_v1",
    "inventory_payload_v1",
]
