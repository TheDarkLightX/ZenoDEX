"""Typed unmounted C03 entitlement state and migration values."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Final, final

from ..state.canonical import hex_to_bytes_fixed
from .fcis_entitlement_key_v1 import (
    EntitlementKeyV1,
    _require_bounded_text_v1,
)
from .fcis_m6_profile_ids import (
    AGQE_REPRESENTATION_PROFILE_ID_V1,
    SRGD_REPRESENTATION_PROFILE_ID_V1,
)

ENTITLEMENT_STATE_SCHEMA_ID_V1: Final[str] = "zenodex/fcis/entitlement/state/v1"
REPRESENTATION_MIGRATION_MANIFEST_SCHEMA_ID_V1: Final[str] = (
    "zenodex/fcis/entitlement/representation-migration/v1"
)
ENTITLEMENT_STATE_ENTRY_SCHEMA_ID_V1: Final[str] = (
    "zenodex/fcis/entitlement/state-entry/v1"
)

SUPPORTED_REPRESENTATION_IDS_V1: Final[tuple[str, str]] = (
    SRGD_REPRESENTATION_PROFILE_ID_V1,
    AGQE_REPRESENTATION_PROFILE_ID_V1,
)
ENTITLEMENT_STATE_FIELDS_V1: Final[tuple[str, str, str]] = (
    "key",
    "representation_id",
    "entries",
)
ENTITLEMENT_STATE_ENTRY_FIELDS_V1: Final[tuple[str, str]] = (
    "entry_id",
    "coordinates",
)
REPRESENTATION_MIGRATION_MANIFEST_FIELDS_V1: Final[
    tuple[str, str, str, str, str, str, str, str, str]
] = (
    "old_semantic_key",
    "new_semantic_key",
    "old_representation_id",
    "new_representation_id",
    "old_state_root",
    "new_state_root",
    "migration_map_id",
    "authority_epoch_root",
    "activation_sequence",
)

MAX_ENTITLEMENT_STATE_ENTRIES_V1: Final[int] = 50_000
MAX_ENTITLEMENT_COORDINATE_V1: Final[int] = 9_999
MAX_MIGRATION_SEQUENCE_V1: Final[int] = (1 << 256) - 1


def _require_state_root_v1(name: str, value: object) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be an exact string")
    hex_to_bytes_fixed(value, nbytes=32, name=name)
    return value


def _require_coordinate_v1(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    if not -MAX_ENTITLEMENT_COORDINATE_V1 <= value <= MAX_ENTITLEMENT_COORDINATE_V1:
        raise ValueError(f"{name} is outside the bounded coordinate domain")
    return value


@final
@dataclass(frozen=True, slots=True)
class EntitlementStateEntryV1:
    """One ordered residual-coordinate entry in an entitlement state."""

    entry_id: str
    coordinates: tuple[int, int, int]

    def __post_init__(self) -> None:
        _require_bounded_text_v1("entitlement entry ID", self.entry_id)
        if type(self.coordinates) is not tuple or len(self.coordinates) != 3:
            raise TypeError("entitlement coordinates must be an exact three-tuple")
        for index, coordinate in enumerate(self.coordinates):
            _require_coordinate_v1(f"entitlement coordinates[{index}]", coordinate)
        if sum(self.coordinates) != 0:
            raise ValueError("entitlement coordinates must conserve to zero")

    @property
    def protocol_order_key(self) -> bytes:
        return self.entry_id.encode("utf-8")


@final
@dataclass(frozen=True, slots=True)
class EntitlementStateV1:
    """Canonical state whose root is derived from its complete entry set."""

    key: EntitlementKeyV1
    representation_id: str
    entries: tuple[EntitlementStateEntryV1, ...]

    def __post_init__(self) -> None:
        if type(self.key) is not EntitlementKeyV1:
            raise TypeError("entitlement state key must be exact")
        self.key.__post_init__()
        _require_bounded_text_v1("entitlement representation ID", self.representation_id)
        if self.representation_id not in SUPPORTED_REPRESENTATION_IDS_V1:
            raise ValueError("unsupported entitlement representation")
        if type(self.entries) is not tuple:
            raise TypeError("entitlement state entries must be an exact tuple")
        if len(self.entries) > MAX_ENTITLEMENT_STATE_ENTRIES_V1:
            raise ValueError("entitlement state entry limit exceeded")
        previous: bytes | None = None
        for entry in self.entries:
            if type(entry) is not EntitlementStateEntryV1:
                raise TypeError("entitlement state entries must be exact")
            entry.__post_init__()
            current = entry.protocol_order_key
            if previous is not None and previous >= current:
                raise ValueError("entitlement state entries must be strictly ordered")
            previous = current

    @property
    def state_root(self) -> str:
        from .fcis_entitlement_migration_codec_v1 import (
            canonical_entitlement_state_root_v1,
        )

        return canonical_entitlement_state_root_v1(self)


@final
@dataclass(frozen=True, slots=True)
class RepresentationMigrationManifestV1:
    """Manifest whose roots and identity fields derive from verified states."""

    old_state: EntitlementStateV1
    new_state: EntitlementStateV1
    migration_map_id: str
    authority_epoch_root: str
    activation_sequence: int

    def __post_init__(self) -> None:
        if type(self.old_state) is not EntitlementStateV1:
            raise TypeError("old migration state must be exact")
        if type(self.new_state) is not EntitlementStateV1:
            raise TypeError("new migration state must be exact")
        self.old_state.__post_init__()
        self.new_state.__post_init__()
        if self.old_state.representation_id == self.new_state.representation_id:
            raise ValueError("migration must change representation")
        _require_bounded_text_v1("migration map ID", self.migration_map_id)
        _require_state_root_v1("authority epoch root", self.authority_epoch_root)
        if type(self.activation_sequence) is not int:
            raise TypeError("activation sequence must be an exact integer")
        if not 0 <= self.activation_sequence <= MAX_MIGRATION_SEQUENCE_V1:
            raise ValueError("activation sequence is outside the U256 domain")

    @property
    def old_semantic_key(self) -> EntitlementKeyV1:
        return self.old_state.key

    @property
    def new_semantic_key(self) -> EntitlementKeyV1:
        return self.new_state.key

    @property
    def old_representation_id(self) -> str:
        return self.old_state.representation_id

    @property
    def new_representation_id(self) -> str:
        return self.new_state.representation_id

    @property
    def old_state_root(self) -> str:
        return self.old_state.state_root

    @property
    def new_state_root(self) -> str:
        return self.new_state.state_root


__all__ = (
    "ENTITLEMENT_STATE_ENTRY_FIELDS_V1",
    "ENTITLEMENT_STATE_ENTRY_SCHEMA_ID_V1",
    "ENTITLEMENT_STATE_FIELDS_V1",
    "ENTITLEMENT_STATE_SCHEMA_ID_V1",
    "MAX_ENTITLEMENT_COORDINATE_V1",
    "MAX_ENTITLEMENT_STATE_ENTRIES_V1",
    "MAX_MIGRATION_SEQUENCE_V1",
    "REPRESENTATION_MIGRATION_MANIFEST_FIELDS_V1",
    "REPRESENTATION_MIGRATION_MANIFEST_SCHEMA_ID_V1",
    "SUPPORTED_REPRESENTATION_IDS_V1",
    "EntitlementStateEntryV1",
    "EntitlementStateV1",
    "RepresentationMigrationManifestV1",
)
