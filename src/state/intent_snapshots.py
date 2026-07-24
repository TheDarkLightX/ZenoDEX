"""Exact owned intent values and one-way FCIS snapshot facades."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, cast, final

from .canonical import canonical_json_bytes
from .intents import (
    CreatePoolIntent,
    Intent,
    RouteIntent,
    SwapIntent,
    ValidatedIntent,
)
from .owned_collections import OwnedEnumV1, OwnedMapV1
from .owned_json import (
    JsonProjectionV1,
    OwnedJsonValueV1,
    _admit_graph_value,
    _project_owned_json_unchecked,
)


@final
@dataclass(frozen=True, slots=True)
class OwnedIntentV1:
    """Composition-owned parsed command with no mutable ``Intent`` base."""

    module: str
    version: str
    kind: OwnedEnumV1
    intent_id: str
    sender_pubkey: str
    deadline: int
    salt: str | None
    fields: OwnedMapV1[str, OwnedJsonValueV1]


IntentSourceV1: TypeAlias = (
    Intent | SwapIntent | RouteIntent | CreatePoolIntent | ValidatedIntent | OwnedIntentV1
)


def _record_field(
    values: tuple[tuple[str, object], ...],
    index: int,
    expected_name: str,
) -> object:
    if type(values) is not tuple or index >= len(values):
        raise ValueError("intent record field registry drift")
    field = values[index]
    if type(field) is not tuple or len(field) != 2 or field[0] != expected_name:
        raise ValueError("intent record field registry drift")
    return field[1]


def _construct_intent_record(
    values: tuple[tuple[str, object], ...],
) -> OwnedIntentV1:
    owned = OwnedIntentV1(
        cast(str, _record_field(values, 0, "module")),
        cast(str, _record_field(values, 1, "version")),
        cast(OwnedEnumV1, _record_field(values, 2, "kind")),
        cast(str, _record_field(values, 3, "intent_id")),
        cast(str, _record_field(values, 4, "sender_pubkey")),
        cast(int, _record_field(values, 5, "deadline")),
        cast(str | None, _record_field(values, 6, "salt")),
        cast(
            OwnedMapV1[str, OwnedJsonValueV1],
            _record_field(values, 7, "fields"),
        ),
    )
    from .intent_schema import validate_owned_intent_invariants_v1

    validate_owned_intent_invariants_v1(owned)
    return owned


def _project_owned_intent(value: OwnedIntentV1) -> dict[str, JsonProjectionV1]:
    from .intent_schema import intent_kind_text_v1

    projection: dict[str, JsonProjectionV1] = {
        "module": value.module,
        "version": value.version,
        "kind": intent_kind_text_v1(value.kind),
        "intent_id": value.intent_id,
        "sender_pubkey": value.sender_pubkey,
        "deadline": value.deadline,
        "fields": _project_owned_json_unchecked(value.fields),
    }
    if value.salt is not None:
        projection["salt"] = value.salt
    return projection


def snapshot_intent(source: IntentSourceV1) -> OwnedIntentV1:
    """Own one exact known intent source through the kind-indexed schema."""

    from .intent_schema import INTENT_ADMISSION_SCHEMA_ID_V1

    admitted = _admit_graph_value(INTENT_ADMISSION_SCHEMA_ID_V1, source)
    if type(admitted) is not OwnedIntentV1:
        raise RuntimeError("closed intent admission returned an impossible result")
    return admitted


def admit_intent_batch(
    source: list[IntentSourceV1] | tuple[IntentSourceV1, ...],
) -> tuple[OwnedIntentV1, ...]:
    """Own a bounded intent sequence while preserving declared protocol order."""

    from .intent_schema import INTENT_BATCH_ADMISSION_SCHEMA_ID_V1

    admitted = _admit_graph_value(INTENT_BATCH_ADMISSION_SCHEMA_ID_V1, source)
    if type(admitted) is not tuple or any(type(item) is not OwnedIntentV1 for item in admitted):
        raise RuntimeError("closed intent-batch admission returned an impossible result")
    return cast(tuple[OwnedIntentV1, ...], admitted)


def canonical_owned_intent_bytes_v1(value: OwnedIntentV1) -> bytes:
    """Encode the exact signing projection after full owned revalidation."""

    owned = snapshot_intent(value)
    return canonical_json_bytes(_project_owned_intent(owned))
