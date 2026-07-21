"""Owned immutable collection helpers for authority-bearing state.

The functional core may accept ordinary ``dict`` and ``list`` builders at a
decode or transaction-scratch boundary. Once admitted into committed state or
an accepted effect plan, these helpers detach the value from caller-owned
aliases and expose only read operations.

The immutable values use composition. Subclassing ``dict`` or ``list`` is not
safe here because a caller can invoke a mutable built-in descriptor directly,
for example ``dict.__setitem__(value, key, item)``, bypassing an overridden
method. Validators that require a mutable concrete type must run before this
boundary or consume an explicit detached copy.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator, Mapping, Sequence
from copy import deepcopy
from dataclasses import fields as dataclass_fields
from dataclasses import is_dataclass
from types import MappingProxyType
from typing import Any, NoReturn, overload


class FrozenDict(Mapping[Any, Any]):
    """An owned mapping snapshot with no mutable built-in base class."""

    __slots__ = ("_data",)
    _data: Mapping[Any, Any]

    def __init__(
        self,
        source: Mapping[Any, Any] | Iterable[tuple[Any, Any]] = (),
    ) -> None:
        # MappingProxyType is safe only because it wraps this fresh private copy.
        # The caller never receives the mutable backing dictionary.
        snapshot = dict(source)
        object.__setattr__(self, "_data", MappingProxyType(snapshot))

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("immutable mapping snapshot")

    @staticmethod
    def _immutable(*_args: object, **_kwargs: object) -> NoReturn:
        raise TypeError("immutable mapping snapshot")

    __setitem__ = _immutable
    __delitem__ = _immutable
    clear = _immutable
    pop = _immutable
    popitem = _immutable
    setdefault = _immutable
    update = _immutable
    __ior__ = _immutable

    def __getitem__(self, key: Any) -> Any:
        return self._data[key]

    def __iter__(self) -> Iterator[Any]:
        return iter(self._data)

    def __len__(self) -> int:
        return len(self._data)

    def copy(self) -> dict[Any, Any]:
        """Return an explicitly mutable detached copy."""

        return dict(self._data)

    def __copy__(self) -> FrozenDict:
        return self

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenDict:
        return self

    def __repr__(self) -> str:
        return f"FrozenDict({dict(self._data)!r})"


class FrozenList(Sequence[Any]):
    """An owned sequence snapshot with no mutable built-in base class."""

    __slots__ = ("_items",)
    _items: tuple[Any, ...]

    def __init__(self, source: Iterable[Any] = ()) -> None:
        object.__setattr__(self, "_items", tuple(source))

    @staticmethod
    def _immutable(*_args: object, **_kwargs: object) -> NoReturn:
        raise TypeError("immutable list snapshot")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("immutable list snapshot")

    __setitem__ = _immutable
    __delitem__ = _immutable
    __iadd__ = _immutable
    __imul__ = _immutable
    append = _immutable
    clear = _immutable
    extend = _immutable
    insert = _immutable
    pop = _immutable
    remove = _immutable
    reverse = _immutable
    sort = _immutable

    @overload
    def __getitem__(self, index: int) -> Any: ...

    @overload
    def __getitem__(self, index: slice) -> FrozenList: ...

    def __getitem__(self, index: int | slice) -> Any:
        item = self._items[index]
        if isinstance(index, slice):
            return FrozenList(item)
        return item

    def __iter__(self) -> Iterator[Any]:
        return iter(self._items)

    def __len__(self) -> int:
        return len(self._items)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, FrozenList):
            return self._items == other._items
        if isinstance(other, list):
            return list(self._items) == other
        return False

    def copy(self) -> list[Any]:
        """Return an explicitly mutable detached copy."""

        return list(self._items)

    def __copy__(self) -> FrozenList:
        return self

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenList:
        return self

    def __repr__(self) -> str:
        return f"FrozenList({list(self._items)!r})"


def deep_freeze(value: Any) -> Any:
    """Return a detached, recursively immutable snapshot of an acyclic value.

    Consensus and signature payloads are already required to be acyclic and
    canonically serializable.  Rejecting mutation after this copy removes the
    time-of-check/time-of-use gap without changing the accepted scalar domain.
    Dataclass instances retain their exact runtime type; only their nested
    fields are replaced with owned immutable snapshots.
    """

    if isinstance(value, (FrozenDict, FrozenList)):
        return value
    if isinstance(value, dict):
        return FrozenDict((deep_freeze(key), deep_freeze(item)) for key, item in value.items())
    if isinstance(value, list):
        return FrozenList(deep_freeze(item) for item in value)
    if isinstance(value, tuple):
        return tuple(deep_freeze(item) for item in value)
    if isinstance(value, (set, frozenset)):
        return frozenset(deep_freeze(item) for item in value)
    if is_dataclass(value) and not isinstance(value, type):
        cloned = deepcopy(value)
        for field in dataclass_fields(cloned):
            object.__setattr__(
                cloned,
                field.name,
                deep_freeze(getattr(cloned, field.name)),
            )
        return cloned
    return deepcopy(value)
