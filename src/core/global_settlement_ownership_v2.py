"""Private graph-ownership descriptors for GlobalSettlementABI V2 values."""

from __future__ import annotations

from typing import Any

from .global_settlement_primitives_v2 import (
    _require_sorted_unique_tokens_v2,
    _require_tuple_v2,
    _snapshot_dataclass_tuple_v2,
)


class _DataclassTupleSnapshotPropertyV2(property):
    """Dataclass-compatible property owning and returning exact typed snapshots."""

    def __init__(
        self,
        private_name: str,
        expected_type: type[Any],
        field_name: str,
        *,
        empty_default: bool = False,
        item_ceiling: int | None = None,
    ) -> None:
        super().__init__()
        self._private_name = private_name
        self._expected_type = expected_type
        self._field_name = field_name
        self._empty_default = empty_default
        self._item_ceiling = item_ceiling

    def __get__(
        self,
        instance: object | None,
        owner: type[object] | None = None,
    ) -> Any:
        if instance is None:
            if self._empty_default:
                return ()
            raise AttributeError
        return _snapshot_dataclass_tuple_v2(
            object.__getattribute__(instance, self._private_name),
            self._expected_type,
            self._field_name,
        )

    def __set__(self, instance: object, value: object) -> None:
        items = _require_tuple_v2(value, name=self._field_name)
        if self._item_ceiling is not None and len(items) > self._item_ceiling:
            raise ValueError(
                f"{self._field_name} exceeds its {self._item_ceiling}-item ceiling"
            )
        object.__setattr__(
            instance,
            self._private_name,
            _snapshot_dataclass_tuple_v2(
                items,
                self._expected_type,
                self._field_name,
            ),
        )


class _SortedTokenTupleSnapshotPropertyV2(property):
    """Dataclass-compatible property owning a sorted tuple of exact tokens."""

    def __init__(self, private_name: str, field_name: str, item_ceiling: int) -> None:
        super().__init__()
        self._private_name = private_name
        self._field_name = field_name
        self._item_ceiling = item_ceiling

    def __get__(
        self,
        instance: object | None,
        owner: type[object] | None = None,
    ) -> Any:
        if instance is None:
            raise AttributeError
        return tuple(object.__getattribute__(instance, self._private_name))

    def __set__(self, instance: object, value: object) -> None:
        items = _require_tuple_v2(value, name=self._field_name)
        if len(items) > self._item_ceiling:
            raise ValueError(
                f"{self._field_name} exceeds its {self._item_ceiling}-item ceiling"
            )
        object.__setattr__(
            instance,
            self._private_name,
            tuple(_require_sorted_unique_tokens_v2(items, name=self._field_name)),
        )


__all__: list[str] = []
