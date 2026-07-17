from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any


def _require_text(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


def _require_flag(value: Any, *, name: str) -> bool:
    if isinstance(value, bool):
        return bool(value)
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be a bool or 0/1 int")
    if value not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return bool(value)


@dataclass(frozen=True)
class ConfidentialRequestKey:
    extension_id: str
    provider_id: str
    request_id: str

    def __post_init__(self) -> None:
        object.__setattr__(
            self, "extension_id", _require_text(self.extension_id, name="extension_id")
        )
        object.__setattr__(self, "provider_id", _require_text(self.provider_id, name="provider_id"))
        object.__setattr__(self, "request_id", _require_text(self.request_id, name="request_id"))


@dataclass(frozen=True)
class ConfidentialRequestUseTransition:
    request_used_before: bool
    consume_request: bool
    request_unused_ok: bool
    transition_ok: bool
    consume_applied: bool
    request_used_after: bool


def evaluate_confidential_request_use_transition(
    *,
    request_used_before: Any,
    consume_request: Any,
) -> ConfidentialRequestUseTransition:
    used_before = _require_flag(request_used_before, name="request_used_before")
    consume = _require_flag(consume_request, name="consume_request")
    request_unused_ok = not used_before
    transition_ok = bool((not consume) or request_unused_ok)
    consume_applied = bool(consume and request_unused_ok)
    request_used_after = bool(used_before or consume_applied)
    return ConfidentialRequestUseTransition(
        request_used_before=used_before,
        consume_request=consume,
        request_unused_ok=request_unused_ok,
        transition_ok=transition_ok,
        consume_applied=consume_applied,
        request_used_after=request_used_after,
    )


ConfidentialRequestEntry = tuple[ConfidentialRequestKey, bool]
ConfidentialRequestEntries = (
    Mapping[ConfidentialRequestKey, bool] | Iterable[ConfidentialRequestEntry]
)


def _canonical_used_entries(
    entries: ConfidentialRequestEntries,
) -> tuple[ConfidentialRequestEntry, ...]:
    raw_entries = entries.items() if isinstance(entries, Mapping) else entries
    seen_keys: set[ConfidentialRequestKey] = set()
    used_keys: set[ConfidentialRequestKey] = set()
    for index, raw_entry in enumerate(raw_entries):
        if not isinstance(raw_entry, tuple) or len(raw_entry) != 2:
            raise TypeError(f"entries[{index}] must be a (ConfidentialRequestKey, bool) tuple")
        key, raw_used = raw_entry
        if not isinstance(key, ConfidentialRequestKey):
            raise TypeError(f"entries[{index}] key must be a ConfidentialRequestKey")
        if key in seen_keys:
            raise ValueError(f"entries[{index}] duplicates a confidential request key")
        seen_keys.add(key)
        used = _require_flag(raw_used, name=f"entries[{index}].used")
        if used:
            used_keys.add(key)
    return tuple(
        (key, True)
        for key in sorted(
            used_keys,
            key=lambda item: (item.extension_id, item.provider_id, item.request_id),
        )
    )


@dataclass(frozen=True, slots=True, init=False)
class ConfidentialRequestTable:
    """Canonical immutable snapshot of consumed confidential request keys."""

    entries: tuple[ConfidentialRequestEntry, ...]

    def __init__(self, entries: ConfidentialRequestEntries = ()) -> None:
        object.__setattr__(self, "entries", _canonical_used_entries(entries))

    def is_used(self, key: ConfidentialRequestKey) -> bool:
        if not isinstance(key, ConfidentialRequestKey):
            raise TypeError("key must be a ConfidentialRequestKey")
        return any(entry_key == key for entry_key, _used in self.entries)

    def consume(self, key: ConfidentialRequestKey) -> ConfidentialRequestTable:
        """Return a new snapshot with ``key`` consumed; reject replay atomically."""

        if not isinstance(key, ConfidentialRequestKey):
            raise TypeError("key must be a ConfidentialRequestKey")
        if self.is_used(key):
            raise ValueError("request already used")
        return ConfidentialRequestTable((*self.entries, (key, True)))

    def get_all(self) -> Mapping[ConfidentialRequestKey, bool]:
        return MappingProxyType(dict(self.entries))


def copy_confidential_request_table(
    request_table: ConfidentialRequestTable,
) -> ConfidentialRequestTable:
    if not isinstance(request_table, ConfidentialRequestTable):
        raise TypeError("request_table must be a ConfidentialRequestTable")
    return ConfidentialRequestTable(request_table.entries)
