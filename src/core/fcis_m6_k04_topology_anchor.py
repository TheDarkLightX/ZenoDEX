"""Typed K04 topology anchor for the unmounted FCIS M6 source set."""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from typing import Final

from src.state.canonical import canonical_json_bytes

FCIS_M6_K04_SCHEMA_V1: Final = "zenodex/fcis/m6/k04/anchored-topology/v1"
FCIS_M6_K04_ROOT_SCHEMA_V1: Final = "zenodex/fcis/m6/k04/topology-anchor-root/v1"
MAX_K04_PUBLISHERS_V1: Final = 128
MAX_K04_SOURCES_V1: Final = 512
_HEX: Final = frozenset("0123456789abcdef")


class K04Error(ValueError):
    """Raised when a K04 topology anchor is outside its closed language."""


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or value != value.lower()
        or any(character not in _HEX for character in value)
    ):
        raise K04Error(f"{name} must be 64 lowercase hexadecimal characters")
    return value


def _text(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise K04Error(f"{name} must be a nonempty exact string")
    if len(value.encode("utf-8")) > 512:
        raise K04Error(f"{name} exceeds its byte bound")
    return value


def _ordered_strings(value: object, name: str, *, maximum: int) -> tuple[str, ...]:
    if type(value) is not tuple or not value:
        raise K04Error(f"{name} must be a nonempty exact tuple")
    if len(value) > maximum:
        raise K04Error(f"{name} exceeds its closed bound")
    checked = tuple(_text(item, f"{name}[{index}]") for index, item in enumerate(value))
    if checked != tuple(sorted(checked, key=lambda item: item.encode("utf-8"))):
        raise K04Error(f"{name} is not canonically ordered")
    if len(set(checked)) != len(checked):
        raise K04Error(f"{name} contains duplicates")
    return checked


def _root(payload: dict[str, object]) -> str:
    return sha256(
        FCIS_M6_K04_ROOT_SCHEMA_V1.encode("ascii") + b"\x00" + canonical_json_bytes(payload)
    ).hexdigest()


@dataclass(frozen=True, slots=True)
class K04TopologyAnchorV1:
    """One exact relation between D05, K01, and the unique K02 port."""

    d05_inventory_root: str
    d05_topology_root: str
    k01_entrypoint_inventory_root: str
    unique_port_id: str
    publisher_ids: tuple[str, ...]
    source_paths: tuple[str, ...]

    def __post_init__(self) -> None:
        _digest(self.d05_inventory_root, "d05_inventory_root")
        _digest(self.d05_topology_root, "d05_topology_root")
        _digest(self.k01_entrypoint_inventory_root, "k01_entrypoint_inventory_root")
        _text(self.unique_port_id, "unique_port_id")
        _ordered_strings(self.publisher_ids, "publisher_ids", maximum=MAX_K04_PUBLISHERS_V1)
        _ordered_strings(self.source_paths, "source_paths", maximum=MAX_K04_SOURCES_V1)

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_K04_SCHEMA_V1,
            "d05_inventory_root": self.d05_inventory_root,
            "d05_topology_root": self.d05_topology_root,
            "k01_entrypoint_inventory_root": self.k01_entrypoint_inventory_root,
            "unique_port_id": self.unique_port_id,
            "publisher_ids": list(self.publisher_ids),
            "source_paths": list(self.source_paths),
        }


def topology_anchor_root_v1(anchor: K04TopologyAnchorV1) -> str:
    """Derive the domain-separated K04 topology anchor root."""

    return _root(anchor.to_wire())


def topology_anchor_payload_v1(anchor: K04TopologyAnchorV1) -> dict[str, object]:
    """Return the canonical generated K04 anchor payload."""

    return {
        **anchor.to_wire(),
        "topology_anchor_root": topology_anchor_root_v1(anchor),
    }


__all__ = [
    "FCIS_M6_K04_ROOT_SCHEMA_V1",
    "FCIS_M6_K04_SCHEMA_V1",
    "K04Error",
    "K04TopologyAnchorV1",
    "topology_anchor_payload_v1",
    "topology_anchor_root_v1",
]
