"""Private graph ownership support for the V2 asset-origin packet."""

from __future__ import annotations

from collections.abc import Callable
from typing import Any


class _OwnedDataclassSnapshotPropertyV2(property):
    """Dataclass field descriptor with private storage and snapshot reads.

    Dataclass-generated construction and ``replace`` continue to use the
    public field name.  Storage stays private, and every public read receives
    a fresh exact snapshot supplied by the owning packet type.
    """

    def __init__(
        self,
        private_name: str,
        expected_type: type[Any],
        snapshot: Callable[[Any], Any],
        error_message: str,
        *,
        allow_none: bool = False,
    ) -> None:
        super().__init__()
        self._private_name = private_name
        self._expected_type = expected_type
        self._snapshot = snapshot
        self._error_message = error_message
        self._allow_none = allow_none

    def __get__(
        self,
        instance: object | None,
        owner: type[object] | None = None,
    ) -> Any:
        if instance is None:
            raise AttributeError
        value = object.__getattribute__(instance, self._private_name)
        if value is None:
            return None
        return self._snapshot(value)

    def __set__(self, instance: object, value: object) -> None:
        if value is None:
            if not self._allow_none:
                raise TypeError(self._error_message)
            object.__setattr__(instance, self._private_name, None)
            return
        if type(value) is not self._expected_type:
            raise TypeError(self._error_message)
        object.__setattr__(instance, self._private_name, self._snapshot(value))


__all__ = ["_OwnedDataclassSnapshotPropertyV2"]
