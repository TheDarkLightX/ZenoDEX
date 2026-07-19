"""Owned immutable collection helpers for authority-bearing state.

The functional core still accepts ordinary ``dict`` and ``list`` builders at its
input boundary.  Once a value is admitted into committed state or an accepted
effect plan, these helpers detach it from caller-owned aliases and reject every
public mutation operation.

``FrozenDict`` and ``FrozenList`` intentionally retain their nominal built-in
interfaces.  Legacy validators that use ``isinstance(value, dict)`` or
``isinstance(value, list)`` therefore keep working while authority-bearing
values become immutable.
"""

from __future__ import annotations

from copy import deepcopy
from dataclasses import fields as dataclass_fields
from dataclasses import is_dataclass
from typing import Any, NoReturn


class FrozenDict(dict[Any, Any]):
    """A ``dict`` snapshot whose mutation surface always fails closed."""

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

    def copy(self) -> dict[Any, Any]:
        """Return an explicitly mutable detached copy."""

        return dict(self)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenDict:
        return self


class FrozenList(list[Any]):
    """A ``list`` snapshot whose mutation surface always fails closed."""

    @staticmethod
    def _immutable(*_args: object, **_kwargs: object) -> NoReturn:
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

    def copy(self) -> list[Any]:
        """Return an explicitly mutable detached copy."""

        return list(self)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenList:
        return self


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
        return FrozenDict(
            (deep_freeze(key), deep_freeze(item))
            for key, item in value.items()
        )
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
