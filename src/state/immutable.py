"""Small immutable containers for canonical state and effect boundaries.

Mutable ``dict`` and ``list`` instances remain useful as local builders.  The
types in this module are the sealing boundary: they own their contents and
reject every normal mutation API after construction.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator, Mapping
from dataclasses import is_dataclass
from inspect import signature
from types import MappingProxyType
from typing import Any, NoReturn, TypeVar, cast

_T = TypeVar("_T", bound=type[Any])


class SealedValue:
    """Marker storage for slotted, frozen authoritative dataclasses.

    Python's ``frozen=True`` blocks assignment syntax but an already-created
    instance can otherwise be changed by calling its generated ``__init__``
    again.  Authoritative values inherit this slot and use
    :func:`seal_dataclass_init` to make initialization one-shot.

    This protects ordinary Python APIs.  Code that deliberately invokes
    ``object.__setattr__`` or raw slot descriptors is outside that contract in
    the same way as native-memory mutation is outside a Rust safe-code claim.
    """

    __slots__ = ("__zenodex_init_complete",)

    def __copy__(self) -> "SealedValue":
        return self

    def __deepcopy__(self, memo: dict[int, Any]) -> "SealedValue":
        memo[id(self)] = self
        return self

    def __reduce_ex__(self, protocol: int) -> NoReturn:
        raise TypeError(
            "authoritative values are not pickle data; use the canonical protocol encoder"
        )


def _is_initialized(value: SealedValue) -> bool:
    try:
        return bool(object.__getattribute__(value, "_SealedValue__zenodex_init_complete"))
    except AttributeError:
        return False


def seal_dataclass_init(cls: _T) -> _T:
    """Make a frozen, slotted dataclass's initialization one-shot.

    Apply this *outside* ``@dataclass(frozen=True, slots=True)``.  The marker
    lives outside the dataclass field set, so canonical ``asdict`` projections
    are unchanged.  Pickle is rejected: authoritative persistence must use the
    versioned canonical protocol encoder, not Python object reconstruction.
    """

    if not is_dataclass(cls):
        raise TypeError("seal_dataclass_init requires an already-created dataclass")
    if not issubclass(cls, SealedValue):
        raise TypeError("sealed dataclass must inherit SealedValue")
    if "__slots__" not in cls.__dict__:
        raise TypeError("sealed dataclass must use slots=True")

    original_init = cls.__init__
    def guarded_init(self: SealedValue, *args: Any, **kwargs: Any) -> None:
        if _is_initialized(self):
            raise TypeError(f"{cls.__name__} is already initialized")
        # Seal before user-defined post-init code runs, so callbacks cannot
        # recursively re-enter the generated initializer.
        object.__setattr__(self, "_SealedValue__zenodex_init_complete", True)
        original_init(self, *args, **kwargs)

    guarded_init.__name__ = "__init__"
    guarded_init.__qualname__ = f"{cls.__qualname__}.__init__"
    guarded_init.__doc__ = original_init.__doc__
    guarded_init.__module__ = original_init.__module__
    guarded_init.__annotations__ = dict(getattr(original_init, "__annotations__", {}))
    guarded_init.__signature__ = signature(original_init)  # type: ignore[attr-defined]

    def reject_pickle_state(self: SealedValue, state: object = None) -> NoReturn:
        raise TypeError(
            "authoritative values are not pickle data; use the canonical protocol encoder"
        )

    cls.__init__ = guarded_init  # type: ignore[method-assign]
    cls.__getstate__ = reject_pickle_state  # type: ignore[attr-defined]
    cls.__setstate__ = reject_pickle_state  # type: ignore[attr-defined]
    cls.__zenodex_init_guarded__ = True  # type: ignore[attr-defined]
    return cast(_T, cls)


def _immutable_error() -> NoReturn:
    raise TypeError("immutable value cannot be mutated")


class FrozenDict(Mapping[Any, Any]):
    """An owned immutable map shell with no ``dict`` mutation escape.

    Composite state constructors remain responsible for validating/sealing
    leaf values.  Canonical JSON values should be built through
    :func:`deep_freeze`, which recursively seals the complete tree.
    """

    __slots__ = ("__data",)

    def __init_subclass__(cls, **kwargs: Any) -> NoReturn:
        raise TypeError("FrozenDict cannot be subclassed")

    def __init__(
        self,
        values: Mapping[Any, Any] | Iterable[tuple[Any, Any]] = (),
    ) -> None:
        try:
            object.__getattribute__(self, "_FrozenDict__data")
        except AttributeError:
            pass
        else:
            raise TypeError("FrozenDict is already initialized")
        owned = dict(values)
        object.__setattr__(self, "_FrozenDict__data", MappingProxyType(owned))

    def __getitem__(self, key: Any) -> Any:
        return self.__data[key]

    def __iter__(self) -> Iterator[Any]:
        return iter(self.__data)

    def __len__(self) -> int:
        return len(self.__data)

    def __repr__(self) -> str:
        return f"FrozenDict({dict(self.__data)!r})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Mapping) and dict(self.items()) == dict(other.items())

    def __setattr__(self, name: str, value: Any) -> NoReturn:
        _immutable_error()

    def __copy__(self) -> "FrozenDict":
        return self

    def __deepcopy__(self, memo: dict[int, Any]) -> "FrozenDict":
        memo[id(self)] = self
        return self

    def __setitem__(self, key: Any, value: Any) -> NoReturn:
        _immutable_error()

    def __delitem__(self, key: Any) -> NoReturn:
        _immutable_error()

    def clear(self) -> NoReturn:
        _immutable_error()

    def pop(self, key: Any, default: Any = None) -> NoReturn:
        _immutable_error()

    def popitem(self) -> NoReturn:
        _immutable_error()

    def setdefault(self, key: Any, default: Any = None) -> NoReturn:
        _immutable_error()

    def update(self, *args: Any, **kwargs: Any) -> NoReturn:
        _immutable_error()

    def __ior__(self, other: object) -> NoReturn:
        _immutable_error()


class FrozenSequence(tuple[Any, ...]):
    """Immutable sequence shell with compatibility equality for old lists."""

    def __init_subclass__(cls, **kwargs: Any) -> NoReturn:
        raise TypeError("FrozenSequence cannot be subclassed")

    def __new__(cls, values: object = ()) -> "FrozenSequence":
        return super().__new__(cls, values)  # type: ignore[arg-type]

    def __eq__(self, other: object) -> bool:
        if isinstance(other, (list, tuple)):
            return tuple(self) == tuple(other)
        return False

    def __ne__(self, other: object) -> bool:
        return not self.__eq__(other)

    __hash__ = tuple.__hash__

    def __copy__(self) -> "FrozenSequence":
        return self

    def __deepcopy__(self, memo: dict[int, Any]) -> "FrozenSequence":
        memo[id(self)] = self
        return self


def deep_freeze(value: Any, *, name: str = "value") -> Any:
    """Own and recursively freeze a JSON-like value.

    DEX intents and settlement events are canonical JSON data.  Rejecting
    arbitrary Python objects here prevents executable/mutable objects from
    crossing a signed or effect-plan boundary.
    """

    return _deep_freeze_json(value, name=name, active=set())


def _deep_freeze_json(value: Any, *, name: str, active: set[int]) -> Any:
    if isinstance(value, Mapping):
        identity = id(value)
        if identity in active:
            raise TypeError(f"{name} contains a container cycle")
        active.add(identity)
        try:
            owned: dict[str, Any] = {}
            for key, inner in value.items():
                if type(key) is not str:
                    raise TypeError(f"{name} keys must be exact strings")
                owned[key] = _deep_freeze_json(
                    inner,
                    name=f"{name}[{key!r}]",
                    active=active,
                )
            return FrozenDict(owned)
        finally:
            active.remove(identity)
    if isinstance(value, (list, tuple)):
        identity = id(value)
        if identity in active:
            raise TypeError(f"{name} contains a container cycle")
        active.add(identity)
        try:
            return FrozenSequence(
                _deep_freeze_json(
                    inner,
                    name=f"{name}[{index}]",
                    active=active,
                )
                for index, inner in enumerate(value)
            )
        finally:
            active.remove(identity)
    if value is None or type(value) in (bool, int, str):
        return value
    raise TypeError(
        f"{name} contains non-canonical or executable value: {type(value).__name__}"
    )


def freeze_mapping(value: Mapping[Any, Any], *, name: str = "mapping") -> FrozenDict:
    frozen = deep_freeze(value, name=name)
    if not isinstance(frozen, FrozenDict):
        raise TypeError(f"{name} must be a mapping")
    return frozen
