"""Typed, source-derived TCG publisher inventory values.

The inventory is an external anchor for the research Tree-Chord-Gate model.
It intentionally accepts source hashes and reviewed deployment metadata as
inputs, while keeping filesystem reads and configuration decoding in the
imperative builder under ``tools/``.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from hashlib import sha256
from typing import Final

from src.state.canonical import canonical_json_bytes

FCIS_M6_TCG_INVENTORY_SCHEMA_V1: Final = "zenodex/fcis/m6/d05/tcg-publisher-inventory/v1"
FCIS_M6_TCG_TOPOLOGY_SCHEMA_V1: Final = "zenodex/fcis/m6/d05/anchored-topology/v1"
MAX_REVIEWED_SOURCES_V1: Final = 128
MAX_PUBLISHERS_V1: Final = 128
MAX_SOURCE_BYTES_V1: Final = 64 * 1024 * 1024
_HEX: Final = frozenset("0123456789abcdef")


class FCISM6TCGInventoryError(ValueError):
    """Raised when a D05 inventory is outside the closed research language."""


class PublisherKindV1(str, Enum):
    """Required publisher surfaces in the independently reviewed inventory."""

    API = "api"
    CLI = "cli"
    ADMINISTRATOR = "administrator"
    MIGRATION_WORKER = "migration_worker"
    RECOVERY_WORKER = "recovery_worker"
    PROOF_VERIFIER = "proof_verifier"
    LEGACY_RUNTIME = "legacy_runtime"
    BACKGROUND_OUTBOX_WORKER = "background_outbox_worker"
    DIRECT_DATASTORE_ADAPTER = "direct_datastore_adapter"


REQUIRED_PUBLISHER_KINDS_V1: Final = frozenset(PublisherKindV1)


def _exact_text(value: object, name: str, *, nonempty: bool = True) -> str:
    if type(value) is not str:
        raise FCISM6TCGInventoryError(f"{name} must be an exact str")
    if nonempty and not value:
        raise FCISM6TCGInventoryError(f"{name} must be nonempty")
    try:
        raw = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise FCISM6TCGInventoryError(f"{name} is not valid UTF-8") from exc
    if len(raw) > 512:
        raise FCISM6TCGInventoryError(f"{name} exceeds 512 UTF-8 bytes")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise FCISM6TCGInventoryError(f"{name} contains a control character")
    return value


def _relative_path(value: object, name: str) -> str:
    path = _exact_text(value, name)
    if "\\" in path or path.startswith("/"):
        raise FCISM6TCGInventoryError(f"{name} must be a POSIX relative path")
    parts = path.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise FCISM6TCGInventoryError(f"{name} is not a canonical relative path")
    return path


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in _HEX for character in value)
    ):
        raise FCISM6TCGInventoryError(f"{name} must be 64 lowercase hexadecimal characters")
    return value


def _exact_int(value: object, name: str, *, maximum: int) -> int:
    if type(value) is not int:
        raise FCISM6TCGInventoryError(f"{name} must be an exact int")
    if value < 0 or value > maximum:
        raise FCISM6TCGInventoryError(f"{name} is outside the closed range")
    return value


def _exact_bool(value: object, name: str) -> bool:
    if type(value) is not bool:
        raise FCISM6TCGInventoryError(f"{name} must be an exact bool")
    return value


def _canonical_text_tuple(value: object, name: str) -> tuple[str, ...]:
    if type(value) is not tuple:
        raise FCISM6TCGInventoryError(f"{name} must be an exact tuple")
    checked = tuple(_exact_text(item, f"{name}[{index}]") for index, item in enumerate(value))
    canonical = tuple(sorted(checked, key=lambda item: item.encode("utf-8")))
    if checked != canonical:
        raise FCISM6TCGInventoryError(f"{name} is not canonically ordered")
    if len(set(checked)) != len(checked):
        raise FCISM6TCGInventoryError(f"{name} contains duplicates")
    return checked


def _root(domain: str, payload: dict[str, object]) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(payload)).hexdigest()


@dataclass(frozen=True, slots=True, order=True)
class ReviewedSourceV1:
    """One exact file read from the independently reviewed source set."""

    path: str
    purpose: str
    source_sha256: str
    source_bytes: int

    def __post_init__(self) -> None:
        _relative_path(self.path, "source.path")
        _exact_text(self.purpose, "source.purpose")
        _digest(self.source_sha256, "source.source_sha256")
        _exact_int(
            self.source_bytes,
            "source.source_bytes",
            maximum=MAX_SOURCE_BYTES_V1,
        )

    def to_wire(self) -> dict[str, object]:
        return {
            "path": self.path,
            "purpose": self.purpose,
            "source_sha256": self.source_sha256,
            "source_bytes": self.source_bytes,
        }


@dataclass(frozen=True, slots=True, order=True)
class PublisherSpecV1:
    """One reviewed publisher or effect-capable authority surface."""

    publisher_id: str
    kind: PublisherKindV1
    entrypoint: str
    source_paths: tuple[str, ...]
    effect_capable: bool
    authority_sink: bool

    def __post_init__(self) -> None:
        _exact_text(self.publisher_id, "publisher.publisher_id")
        if type(self.kind) is not PublisherKindV1:
            raise FCISM6TCGInventoryError("publisher.kind has the wrong exact type")
        _exact_text(self.entrypoint, "publisher.entrypoint")
        if not self.source_paths:
            raise FCISM6TCGInventoryError("publisher.source_paths must be nonempty")
        for index, path in enumerate(self.source_paths):
            _relative_path(path, f"publisher.source_paths[{index}]")
        _canonical_text_tuple(self.source_paths, "publisher.source_paths")
        _exact_bool(self.effect_capable, "publisher.effect_capable")
        _exact_bool(self.authority_sink, "publisher.authority_sink")

    def to_wire(self) -> dict[str, object]:
        return {
            "publisher_id": self.publisher_id,
            "kind": self.kind.value,
            "entrypoint": self.entrypoint,
            "source_paths": list(self.source_paths),
            "effect_capable": self.effect_capable,
            "authority_sink": self.authority_sink,
        }


@dataclass(frozen=True, slots=True, order=True)
class TCGPublisherInventoryV1:
    """Complete typed projection of the independently reviewed inventory."""

    profile_id: str
    configuration_path: str
    configuration_sha256: str
    deployment_source_paths: tuple[str, ...]
    sources: tuple[ReviewedSourceV1, ...]
    publishers: tuple[PublisherSpecV1, ...]

    def __post_init__(self) -> None:
        _exact_text(self.profile_id, "profile_id")
        _relative_path(self.configuration_path, "configuration_path")
        _digest(self.configuration_sha256, "configuration_sha256")
        if not self.deployment_source_paths:
            raise FCISM6TCGInventoryError("deployment_source_paths must be nonempty")
        _canonical_text_tuple(
            self.deployment_source_paths,
            "deployment_source_paths",
        )
        if type(self.sources) is not tuple or not self.sources:
            raise FCISM6TCGInventoryError("sources must be a nonempty tuple")
        if len(self.sources) > MAX_REVIEWED_SOURCES_V1:
            raise FCISM6TCGInventoryError("sources exceed the closed bound")
        if tuple(sorted(self.sources, key=lambda item: item.path.encode("utf-8"))) != self.sources:
            raise FCISM6TCGInventoryError("sources are not canonically ordered")
        source_paths = tuple(source.path for source in self.sources)
        if len(set(source_paths)) != len(source_paths):
            raise FCISM6TCGInventoryError("sources contain duplicate paths")
        source_map = set(source_paths)
        if self.configuration_path not in source_map:
            raise FCISM6TCGInventoryError("configuration path is not anchored")
        if not set(self.deployment_source_paths).issubset(source_map):
            raise FCISM6TCGInventoryError("deployment source is missing from the source manifest")
        if type(self.publishers) is not tuple or not self.publishers:
            raise FCISM6TCGInventoryError("publishers must be a nonempty tuple")
        if len(self.publishers) > MAX_PUBLISHERS_V1:
            raise FCISM6TCGInventoryError("publishers exceed the closed bound")
        if (
            tuple(sorted(self.publishers, key=lambda item: item.publisher_id.encode("utf-8")))
            != self.publishers
        ):
            raise FCISM6TCGInventoryError("publishers are not canonically ordered")
        publisher_ids = tuple(item.publisher_id for item in self.publishers)
        if len(set(publisher_ids)) != len(publisher_ids):
            raise FCISM6TCGInventoryError("publishers contain duplicate IDs")
        kinds = {item.kind for item in self.publishers}
        missing = REQUIRED_PUBLISHER_KINDS_V1.difference(kinds)
        if missing:
            names = ",".join(sorted(item.value for item in missing))
            raise FCISM6TCGInventoryError(f"required publisher kinds are missing: {names}")
        if not any(item.effect_capable for item in self.publishers):
            raise FCISM6TCGInventoryError("inventory has no effect-capable publisher")
        if not any(item.authority_sink for item in self.publishers):
            raise FCISM6TCGInventoryError("inventory has no authority sink")
        for publisher in self.publishers:
            if not set(publisher.source_paths).issubset(source_map):
                raise FCISM6TCGInventoryError(
                    f"publisher {publisher.publisher_id!r} has an unanchored source"
                )

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_TCG_INVENTORY_SCHEMA_V1,
            "profile_id": self.profile_id,
            "configuration_path": self.configuration_path,
            "configuration_sha256": self.configuration_sha256,
            "deployment_source_paths": list(self.deployment_source_paths),
            "sources": [source.to_wire() for source in self.sources],
            "publishers": [publisher.to_wire() for publisher in self.publishers],
        }


def publisher_inventory_root_v1(inventory: TCGPublisherInventoryV1) -> str:
    """Hash the complete independent publisher inventory."""

    return _root(
        FCIS_M6_TCG_INVENTORY_SCHEMA_V1,
        inventory.to_wire(),
    )


def anchored_topology_root_v1(inventory: TCGPublisherInventoryV1) -> str:
    """Derive the topology anchor consumed by a later TCG verifier."""

    inventory_root = publisher_inventory_root_v1(inventory)
    return _root(
        FCIS_M6_TCG_TOPOLOGY_SCHEMA_V1,
        {
            "schema": FCIS_M6_TCG_TOPOLOGY_SCHEMA_V1,
            "profile_id": inventory.profile_id,
            "configuration_path": inventory.configuration_path,
            "configuration_sha256": inventory.configuration_sha256,
            "publisher_inventory_root": inventory_root,
            "publisher_ids": [publisher.publisher_id for publisher in inventory.publishers],
            "source_paths": [source.path for source in inventory.sources],
        },
    )


def inventory_payload_v1(inventory: TCGPublisherInventoryV1) -> dict[str, object]:
    """Return the canonical JSON-shaped generated D05 evidence payload."""

    return {
        **inventory.to_wire(),
        "publisher_inventory_root": publisher_inventory_root_v1(inventory),
        "topology_root": anchored_topology_root_v1(inventory),
    }


__all__ = [
    "FCIS_M6_TCG_INVENTORY_SCHEMA_V1",
    "FCIS_M6_TCG_TOPOLOGY_SCHEMA_V1",
    "FCISM6TCGInventoryError",
    "MAX_PUBLISHERS_V1",
    "MAX_REVIEWED_SOURCES_V1",
    "MAX_SOURCE_BYTES_V1",
    "PublisherKindV1",
    "PublisherSpecV1",
    "REQUIRED_PUBLISHER_KINDS_V1",
    "ReviewedSourceV1",
    "TCGPublisherInventoryV1",
    "anchored_topology_root_v1",
    "inventory_payload_v1",
    "publisher_inventory_root_v1",
]
