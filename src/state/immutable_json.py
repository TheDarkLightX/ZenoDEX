"""Recursively immutable JSON-shaped values for authority boundaries.

A frozen outer dataclass does not own nested ``dict`` and ``list`` builders.
The concrete values use composition over owned snapshots. They have no mutable
``dict`` or ``list`` base class whose descriptors can bypass an overridden
mutator. They are intended for values that have been authenticated, hashed,
accepted, or otherwise assigned protocol meaning.

``copy.copy`` preserves the immutable authority value. ``copy.deepcopy`` creates
a detached mutable JSON builder. This lets adversarial tests and transport code
tamper with an untrusted copy without restoring mutability to the accepted value.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any, TypeVar

from .immutable_collections import (
    FrozenDict as _OwnedFrozenDict,
)
from .immutable_collections import (
    FrozenList as _OwnedFrozenList,
)
from .immutable_collections import (
    deep_thaw_json,
)


class FrozenList(_OwnedFrozenList):
    """An owned JSON-array snapshot with no mutable built-in base class."""

    __slots__ = ()

    def __deepcopy__(self, _memo: dict[int, object]) -> list[Any]:
        return thaw_json_value(self)


class FrozenDict(_OwnedFrozenDict):
    """An owned JSON-object snapshot with no mutable built-in base class."""

    __slots__ = ()

    def __deepcopy__(self, _memo: dict[int, object]) -> dict[str, Any]:
        return thaw_json_value(self)


_JSON_ATOM = (type(None), bool, int, str)


def freeze_json_value(value: Any, *, name: str = "value") -> Any:
    """Copy a JSON-shaped value into a recursively immutable normal form.

    Mutable input containers are never retained. ``tuple`` is accepted as a
    builder convenience and normalized to ``FrozenList`` because canonical JSON
    gives lists and tuples the same array representation. Floats, bytes, sets,
    non-string object keys, and arbitrary live objects are rejected.
    """

    if type(value) in _JSON_ATOM:
        return value
    if isinstance(value, float):
        raise TypeError(f"{name} cannot contain floats")
    if type(value) in (dict, FrozenDict, _OwnedFrozenDict):
        frozen: list[tuple[str, Any]] = []
        for key, child in value.items():
            if type(key) is not str:
                raise TypeError(f"{name} object keys must be strings")
            frozen.append((key, freeze_json_value(child, name=f"{name}.{key}")))
        return FrozenDict(frozen)
    if type(value) in (list, tuple, FrozenList, _OwnedFrozenList):
        return FrozenList(
            freeze_json_value(child, name=f"{name}[{index}]")
            for index, child in enumerate(value)
        )
    raise TypeError(f"{name} contains unsupported type: {type(value).__name__}")


def thaw_json_value(value: Any) -> Any:
    """Copy a JSON-shaped value into detached mutable ``dict``/``list`` builders."""

    thawed = deep_thaw_json(value)
    if type(thawed) in _JSON_ATOM or type(thawed) in (dict, list):
        return thawed
    raise TypeError(f"cannot thaw unsupported type: {type(value).__name__}")


TMapping = TypeVar("TMapping", bound=Mapping[str, Any])


def freeze_json_mapping(value: TMapping, *, name: str = "value") -> FrozenDict:
    """Freeze one exact JSON object into an owned immutable value."""

    if type(value) not in (dict, FrozenDict, _OwnedFrozenDict):
        raise TypeError(f"{name} must be an exact owned mapping")
    frozen = freeze_json_value(value, name=name)
    if type(frozen) is not FrozenDict:  # pragma: no cover - construction invariant
        raise AssertionError("freeze_json_mapping did not return FrozenDict")
    return frozen


def snapshot_json_mapping(value: TMapping, *, name: str = "value") -> dict[str, Any]:
    """Return one detached builtin projection of an exact owned JSON object."""

    snapshot = thaw_json_value(freeze_json_mapping(value, name=name))
    if type(snapshot) is not dict:  # pragma: no cover - construction invariant
        raise AssertionError("snapshot_json_mapping did not return dict")
    return snapshot


__all__ = [
    "FrozenDict",
    "FrozenList",
    "freeze_json_mapping",
    "freeze_json_value",
    "snapshot_json_mapping",
    "thaw_json_value",
]
