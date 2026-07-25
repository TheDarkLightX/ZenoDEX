"""Bounded composition-owned JSON values for FCIS authority graphs.

Decoded mutable containers enter only through the closed state admission
profile. Public projection accepts already-owned values, revalidates them, and
returns a fresh non-authoritative builtin tree for legacy shell adapters.
"""

from __future__ import annotations

from typing import NoReturn, TypeAlias, cast

from .owned_collections import OwnedMapV1
from .snapshot_combinators import (
    AdmissionLimitsV1,
    AdmitCode,
    AdmitOk,
    AdmitReject,
    BoundedJsonValue,
    ExactString,
    MapOf,
    SchemaRegistrationV1,
    StringRuleV1,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)
from .state_snapshots import StateAdmissionError

MAX_OWNED_JSON_DEPTH_V1 = 64
MAX_OWNED_JSON_NODES_V1 = 200_000
MAX_OWNED_JSON_BYTES_V1 = 4_000_000
MAX_OWNED_JSON_CONTAINER_ITEMS_V1 = 200_000
MAX_OWNED_JSON_INTEGER_BITS_V1 = 256
MAX_OWNED_JSON_STRING_CHARACTERS_V1 = 4_096
MAX_OWNED_JSON_STRING_UTF8_BYTES_V1 = 16_384

OWNED_JSON_VALUE_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/authority/json-value/v1"
OWNED_JSON_OBJECT_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/authority/json-object/v1"
OWNED_JSON_VALUE_MAP_SCHEMA_ID_V1 = "zenodex/fcis/authority/json-value-map/v1"
OWNED_JSON_OBJECT_MAP_SCHEMA_ID_V1 = "zenodex/fcis/authority/json-object-map/v1"

JsonSourceValueV1: TypeAlias = (
    None
    | bool
    | int
    | str
    | list["JsonSourceValueV1"]
    | tuple["JsonSourceValueV1", ...]
    | dict[str, "JsonSourceValueV1"]
    | OwnedMapV1[str, "JsonSourceValueV1"]
)
OwnedJsonValueV1: TypeAlias = (
    None | bool | int | str | tuple["OwnedJsonValueV1", ...] | OwnedMapV1[str, "OwnedJsonValueV1"]
)
OwnedJsonObjectV1: TypeAlias = OwnedMapV1[str, OwnedJsonValueV1]
JsonProjectionV1: TypeAlias = (
    None | bool | int | str | list["JsonProjectionV1"] | dict[str, "JsonProjectionV1"]
)

JSON_VALUE_SCHEMA_V1 = BoundedJsonValue(
    OWNED_JSON_VALUE_MAP_SCHEMA_ID_V1,
    MAX_OWNED_JSON_CONTAINER_ITEMS_V1,
    MAX_OWNED_JSON_INTEGER_BITS_V1,
    MAX_OWNED_JSON_STRING_CHARACTERS_V1,
    MAX_OWNED_JSON_STRING_UTF8_BYTES_V1,
)
JSON_KEY_SCHEMA_V1 = ExactString(
    StringRuleV1.EXACT_TEXT,
    MAX_OWNED_JSON_STRING_UTF8_BYTES_V1,
    max_characters=MAX_OWNED_JSON_STRING_CHARACTERS_V1,
)
JSON_OBJECT_SCHEMA_V1 = MapOf(
    JSON_KEY_SCHEMA_V1,
    JSON_VALUE_SCHEMA_V1,
    MAX_OWNED_JSON_CONTAINER_ITEMS_V1,
    OWNED_JSON_OBJECT_MAP_SCHEMA_ID_V1,
)
JSON_SCHEMA_REGISTRATIONS_V1 = (
    SchemaRegistrationV1(OWNED_JSON_VALUE_ADMISSION_SCHEMA_ID_V1, JSON_VALUE_SCHEMA_V1),
    SchemaRegistrationV1(OWNED_JSON_OBJECT_ADMISSION_SCHEMA_ID_V1, JSON_OBJECT_SCHEMA_V1),
)

_AUTHORITY_GRAPH_ADMISSION_LIMITS_RESULT_V1 = build_admission_limits_v1(
    AdmissionLimitsV1(
        max_depth=MAX_OWNED_JSON_DEPTH_V1,
        max_nodes=MAX_OWNED_JSON_NODES_V1,
        max_canonical_bytes=MAX_OWNED_JSON_BYTES_V1,
        max_collection_items=MAX_OWNED_JSON_CONTAINER_ITEMS_V1,
    )
)
if type(_AUTHORITY_GRAPH_ADMISSION_LIMITS_RESULT_V1) is not ValidatedAdmissionLimitsV1:
    raise RuntimeError("FCIS authority-graph admission limits are invalid")
AUTHORITY_GRAPH_ADMISSION_LIMITS_V1 = _AUTHORITY_GRAPH_ADMISSION_LIMITS_RESULT_V1


def _raise_graph_reject(reject: AdmitReject) -> NoReturn:
    raise StateAdmissionError(reject.code, reject.path)


def _admit_graph_value(schema_id: str, source: object) -> object:
    from .state_admission_profile import admit
    from .state_snapshot_values import FCIS_STATE_SCHEMA_REVISION_V1

    result = admit(
        FCIS_STATE_SCHEMA_REVISION_V1,
        schema_id,
        AUTHORITY_GRAPH_ADMISSION_LIMITS_V1,
        source,
    )
    if type(result) is AdmitReject:
        _raise_graph_reject(result)
    if type(result) is not AdmitOk:
        raise RuntimeError("closed authority admission returned an impossible result")
    return result.value


def _project_owned_json_unchecked(value: OwnedJsonValueV1) -> JsonProjectionV1:
    if value is None or type(value) in (bool, int, str):
        return cast(None | bool | int | str, value)
    if type(value) is tuple:
        sequence = cast(tuple[OwnedJsonValueV1, ...], value)
        return [_project_owned_json_unchecked(item) for item in sequence]
    if type(value) is OwnedMapV1:
        owned_map = cast(OwnedMapV1[str, OwnedJsonValueV1], value)
        return {key: _project_owned_json_unchecked(item) for key, item in owned_map.entries}
    raise TypeError("owned JSON projection received an unsupported exact type")


def snapshot_owned_json(value: JsonSourceValueV1) -> OwnedJsonValueV1:
    """Admit one bounded JSON value through the sole production profile."""

    admitted = _admit_graph_value(OWNED_JSON_VALUE_ADMISSION_SCHEMA_ID_V1, value)
    return cast(OwnedJsonValueV1, admitted)


def snapshot_owned_json_object(
    value: dict[str, JsonSourceValueV1] | OwnedJsonObjectV1,
) -> OwnedJsonObjectV1:
    """Admit one exact JSON object; scalar and sequence roots reject."""

    admitted = _admit_graph_value(OWNED_JSON_OBJECT_ADMISSION_SCHEMA_ID_V1, value)
    if type(admitted) is not OwnedMapV1:
        raise RuntimeError("closed JSON-object admission returned an impossible result")
    return cast(OwnedJsonObjectV1, admitted)


def project_owned_json(value: OwnedJsonValueV1) -> JsonProjectionV1:
    """Return a fresh builtin projection after full owned-value revalidation."""

    if type(value) in (dict, list):
        _raise_graph_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    schema_id = OWNED_JSON_VALUE_ADMISSION_SCHEMA_ID_V1
    if type(value) is OwnedMapV1:
        owned_map = cast(OwnedMapV1[str, OwnedJsonValueV1], value)
        if owned_map.schema_id == OWNED_JSON_OBJECT_MAP_SCHEMA_ID_V1:
            schema_id = OWNED_JSON_OBJECT_ADMISSION_SCHEMA_ID_V1
        elif owned_map.schema_id != OWNED_JSON_VALUE_MAP_SCHEMA_ID_V1:
            _raise_graph_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = cast(OwnedJsonValueV1, _admit_graph_value(schema_id, value))
    return _project_owned_json_unchecked(admitted)
