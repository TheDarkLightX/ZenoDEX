"""Closed composition-owned collections for committed authority values."""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from types import MappingProxyType
from typing import Generic, TypeVar, cast, final

K = TypeVar("K")
V = TypeVar("V")

_OWNED_MAP_CONSTRUCTION_TOKEN = object()
_OWNED_ENUM_CONSTRUCTION_TOKEN = object()
_MAPPING_PROXY_TYPE: type[object] = type(MappingProxyType({}))


@final
class OwnedEnumV1:
    """Immutable profile-relative enum identity with no source-member alias."""

    __slots__ = ("_schema_revision", "_enum_tag_ordinal", "_member_ordinal")

    _schema_revision: str
    _enum_tag_ordinal: int
    _member_ordinal: int

    def __init__(
        self,
        schema_revision: str,
        enum_tag_ordinal: int,
        member_ordinal: int,
        *,
        _construction_token: object = None,
    ) -> None:
        try:
            object.__getattribute__(self, "_schema_revision")
        except AttributeError:
            pass
        else:
            raise TypeError("OwnedEnumV1 is already initialized")

        if _construction_token is not _OWNED_ENUM_CONSTRUCTION_TOKEN:
            raise TypeError("OwnedEnumV1 requires closed admission")
        if (
            type(schema_revision) is not str
            or type(enum_tag_ordinal) is not int
            or type(member_ordinal) is not int
            or enum_tag_ordinal < 0
            or member_ordinal < 0
        ):
            raise TypeError("OwnedEnumV1 requires exact canonical metadata")

        object.__setattr__(self, "_schema_revision", schema_revision)
        object.__setattr__(self, "_enum_tag_ordinal", enum_tag_ordinal)
        object.__setattr__(self, "_member_ordinal", member_ordinal)

    @property
    def schema_revision(self) -> str:
        return self._schema_revision

    @property
    def enum_tag_ordinal(self) -> int:
        return self._enum_tag_ordinal

    @property
    def member_ordinal(self) -> int:
        return self._member_ordinal

    def __eq__(self, other: object) -> bool:
        if type(other) is not OwnedEnumV1:
            return False
        return (
            self._schema_revision == other._schema_revision
            and self._enum_tag_ordinal == other._enum_tag_ordinal
            and self._member_ordinal == other._member_ordinal
        )

    def __hash__(self) -> int:
        # Hash-table layout is non-normative. Integer-only hashing also avoids
        # Python's process-randomized string hash at this authority boundary.
        return (self._enum_tag_ordinal << 32) ^ self._member_ordinal

    def __repr__(self) -> str:
        return (
            "OwnedEnumV1("
            f"schema_revision={self._schema_revision!r},"
            f"enum_tag_ordinal={self._enum_tag_ordinal},"
            f"member_ordinal={self._member_ordinal})"
        )

    def __setattr__(self, _name: str, _value: object) -> None:
        raise TypeError("OwnedEnumV1 is immutable")


@final
class OwnedMapV1(Mapping[K, V], Generic[K, V]):
    """Canonical read-only map built only from fully admitted entries.

    The private lookup dictionary is fresh storage and never escapes. Protocol
    order comes from ``entries`` rather than the lookup implementation.
    """

    __slots__ = ("_schema_revision", "_schema_id", "_entries", "_index")

    _schema_revision: str
    _schema_id: str
    _entries: tuple[tuple[K, V], ...]
    _index: Mapping[K, V]

    def __init__(
        self,
        entries: tuple[tuple[K, V], ...],
        schema_revision: str,
        schema_id: str,
        *,
        _construction_token: object = None,
    ) -> None:
        try:
            object.__getattribute__(self, "_entries")
        except AttributeError:
            pass
        else:
            raise TypeError("OwnedMapV1 is already initialized")

        if _construction_token is not _OWNED_MAP_CONSTRUCTION_TOKEN:
            raise TypeError("OwnedMapV1 requires closed admission")
        if type(entries) is not tuple:
            raise TypeError("OwnedMapV1 entries must be an exact tuple")
        if type(schema_revision) is not str or type(schema_id) is not str:
            raise TypeError("OwnedMapV1 schema metadata must be exact strings")

        index: dict[K, V] = {}
        for entry in entries:
            if type(entry) is not tuple or len(entry) != 2:
                raise TypeError("OwnedMapV1 entries must be exact pairs")
            key, value = entry
            if key in index:
                raise ValueError("OwnedMapV1 duplicate admitted key")
            index[key] = value

        object.__setattr__(self, "_schema_revision", schema_revision)
        object.__setattr__(self, "_schema_id", schema_id)
        object.__setattr__(self, "_entries", entries)
        object.__setattr__(self, "_index", MappingProxyType(index))

    @property
    def schema_revision(self) -> str:
        return self._schema_revision

    @property
    def schema_id(self) -> str:
        return self._schema_id

    @property
    def entries(self) -> tuple[tuple[K, V], ...]:
        return self._entries

    def __getitem__(self, key: K) -> V:
        return self._index[key]

    def __iter__(self) -> Iterator[K]:
        return (entry[0] for entry in self._entries)

    def __len__(self) -> int:
        return len(self._entries)

    def __eq__(self, other: object) -> bool:
        if type(other) is not OwnedMapV1:
            return False
        return (
            self._schema_revision == other._schema_revision
            and self._schema_id == other._schema_id
            and self._entries == other._entries
        )

    def __setattr__(self, _name: str, _value: object) -> None:
        raise TypeError("OwnedMapV1 is immutable")


def owned_map_structure_is_exact_v1(value: object) -> bool:
    """Return whether one owned map still has its closed admitted structure.

    The lookup index is non-authoritative acceleration state. Every index item
    must be the identical key/value pair retained by the canonical entries so
    hostile in-process mutation cannot change lookup behavior without changing
    the canonical projection. This check retains no reconstructed collection.
    """

    if type(value) is not OwnedMapV1:
        return False
    try:
        schema_revision = object.__getattribute__(value, "_schema_revision")
        schema_id = object.__getattribute__(value, "_schema_id")
        entries = object.__getattribute__(value, "_entries")
        index = object.__getattribute__(value, "_index")
    except AttributeError:
        return False
    if type(schema_revision) is not str or type(schema_id) is not str:
        return False
    if type(entries) is not tuple or type(index) is not _MAPPING_PROXY_TYPE:
        return False
    exact_index = cast(Mapping[object, object], index)
    if len(entries) != len(exact_index):
        return False
    for entry, indexed_entry in zip(entries, exact_index.items(), strict=True):
        if type(entry) is not tuple or len(entry) != 2:
            return False
        key, item = entry
        if type(indexed_entry) is not tuple or len(indexed_entry) != 2:
            return False
        indexed_key, indexed_item = indexed_entry
        if indexed_key is not key or indexed_item is not item:
            return False
    return True


def _owned_map_from_admitted(
    entries: tuple[tuple[K, V], ...],
    schema_revision: str,
    schema_id: str,
) -> OwnedMapV1[K, V]:
    """Trusted construction edge used only by the closed interpreter."""

    return OwnedMapV1(
        entries,
        schema_revision,
        schema_id,
        _construction_token=_OWNED_MAP_CONSTRUCTION_TOKEN,
    )


def _owned_map_from_canonical_transition_v1(
    entries: tuple[tuple[K, V], ...],
    schema_revision: str,
    schema_id: str,
) -> OwnedMapV1[K, V]:
    """Trusted freeze edge for one fully validated canonical transition.

    The FCIS authority checker permits this capability only in
    ``state_transitions.py``. The transition must establish exact types,
    canonical order, uniqueness, and domain invariants before calling it.
    """

    return OwnedMapV1(
        entries,
        schema_revision,
        schema_id,
        _construction_token=_OWNED_MAP_CONSTRUCTION_TOKEN,
    )


def _owned_enum_from_admitted(
    schema_revision: str,
    enum_tag_ordinal: int,
    member_ordinal: int,
) -> OwnedEnumV1:
    """Trusted enum-copy edge used only by the closed interpreter."""

    return OwnedEnumV1(
        schema_revision,
        enum_tag_ordinal,
        member_ordinal,
        _construction_token=_OWNED_ENUM_CONSTRUCTION_TOKEN,
    )


def _owned_enum_from_canonical_transition_v1(
    schema_revision: str,
    enum_tag_ordinal: int,
    member_ordinal: int,
) -> OwnedEnumV1:
    """Trusted enum construction edge for one closed state transition.

    The FCIS authority checker permits this capability only in the closed pool
    creation transition. Callers must choose tag and member ordinals from the
    source-owned profile, never from authority input without exact validation.
    """

    return OwnedEnumV1(
        schema_revision,
        enum_tag_ordinal,
        member_ordinal,
        _construction_token=_OWNED_ENUM_CONSTRUCTION_TOKEN,
    )
