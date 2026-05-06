from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Mapping


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
        object.__setattr__(self, "extension_id", _require_text(self.extension_id, name="extension_id"))
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


@dataclass
class ConfidentialRequestTable:
    _used: Dict[ConfidentialRequestKey, bool] = field(default_factory=dict)

    def is_used(self, key: ConfidentialRequestKey) -> bool:
        if not isinstance(key, ConfidentialRequestKey):
            raise TypeError("key must be a ConfidentialRequestKey")
        return bool(self._used.get(key, False))

    def mark_used(self, key: ConfidentialRequestKey) -> None:
        if not isinstance(key, ConfidentialRequestKey):
            raise TypeError("key must be a ConfidentialRequestKey")
        self._used[key] = True

    def get_all(self) -> Mapping[ConfidentialRequestKey, bool]:
        return dict(self._used)


def copy_confidential_request_table(request_table: ConfidentialRequestTable) -> ConfidentialRequestTable:
    if not isinstance(request_table, ConfidentialRequestTable):
        raise TypeError("request_table must be a ConfidentialRequestTable")
    copied = ConfidentialRequestTable()
    for key, used in request_table.get_all().items():
        if bool(used):
            copied.mark_used(key)
    return copied
