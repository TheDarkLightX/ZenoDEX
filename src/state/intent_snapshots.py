"""Immutable owned snapshots for authenticated and admitted intents."""

from __future__ import annotations

from collections.abc import Sequence
from copy import deepcopy
from typing import Any, NoReturn

from .immutable_collections import deep_freeze
from .intents import Intent


def _immutable_intent(*_args: object, **_kwargs: object) -> NoReturn:
    raise TypeError("authenticated intent snapshot is immutable")


class FrozenIntent(Intent):
    """Read-compatible ``Intent`` whose complete signed meaning is sealed."""

    def __post_init__(self) -> None:
        object.__setattr__(self, "_snapshot_sealed", False)
        Intent.__post_init__(self)
        fields = self.fields or {}
        if not isinstance(fields, dict):
            raise TypeError("intent.fields must be a dict")
        object.__setattr__(self, "fields", deep_freeze(fields))
        object.__setattr__(self, "_snapshot_sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if self.__dict__.get("_snapshot_sealed", False):
            raise TypeError("authenticated intent snapshot is immutable")
        object.__setattr__(self, name, value)

    def set_field(self, key: str, value: Any) -> None:
        _immutable_intent(key, value)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenIntent:
        return self


def freeze_intent(intent: Intent) -> Intent:
    """Detach one intent from caller-owned attributes and nested field aliases."""

    if not isinstance(intent, Intent):
        raise TypeError("intent must be an Intent")
    if isinstance(intent, FrozenIntent):
        return intent
    fields = intent.fields or {}
    if not isinstance(fields, dict):
        raise TypeError("intent.fields must be a dict")
    return FrozenIntent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        salt=intent.salt,
        fields=deepcopy(fields),
    )


def freeze_intent_batch(intents: Sequence[Intent]) -> list[Intent]:
    """Snapshot a batch once, then use that exact value for all core checks."""

    return [freeze_intent(intent) for intent in intents]
