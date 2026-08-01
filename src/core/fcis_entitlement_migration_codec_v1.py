"""Canonical state and root-bound migration codecs for unmounted C03."""
from __future__ import annotations

import json
from dataclasses import dataclass
from enum import Enum
from typing import Final, cast, final

from ..state.canonical import (
    bounded_json_utf8_size,
    canonical_json_bytes,
    sha256_hex,
)
from ..state.snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
)
from .fcis_entitlement_key_codec_v1 import _entitlement_key_projection_v1
from .fcis_entitlement_key_v1 import (
    ENTITLEMENT_KEY_FIELDS_V1,
    EntitlementKeyV1,
)
from .fcis_entitlement_migration_values_v1 import (
    ENTITLEMENT_STATE_ENTRY_FIELDS_V1,
    ENTITLEMENT_STATE_FIELDS_V1,
    ENTITLEMENT_STATE_SCHEMA_ID_V1,
    REPRESENTATION_MIGRATION_MANIFEST_FIELDS_V1,
    REPRESENTATION_MIGRATION_MANIFEST_SCHEMA_ID_V1,
    EntitlementStateEntryV1,
    EntitlementStateV1,
    RepresentationMigrationManifestV1,
)


class C03CodecCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_UTF8 = "invalid_utf8"
    INVALID_JSON = "invalid_json"
    UNKNOWN_SCHEMA = "unknown_schema"
    UNKNOWN_FIELD = "unknown_field"
    MISSING_FIELD = "missing_field"
    INVALID_VALUE = "invalid_value"
    NONCANONICAL_ENCODING = "noncanonical_encoding"
    VERIFIED_STATE_REQUIRED = "verified_state_required"
    STATE_ROOT_MISMATCH = "state_root_mismatch"


@final
@dataclass(frozen=True, slots=True)
class C03CodecRejectV1:
    code: C03CodecCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not C03CodecCodeV1:
            raise TypeError("C03 reject code must be exact")
        if type(self.path) is not tuple or any(
            type(part) is not str for part in self.path
        ):
            raise TypeError("C03 reject path must be an exact tuple of strings")


C03StateDecodeResultV1 = EntitlementStateV1 | C03CodecRejectV1
C03ManifestDecodeResultV1 = RepresentationMigrationManifestV1 | C03CodecRejectV1

_MAX_PAYLOAD_BYTES_V1: Final[int] = MAX_CANONICAL_BYTES_V1


class _Pairs(tuple[tuple[str, object], ...]):
    pass


class _DuplicateFieldError(ValueError):
    def __init__(self, path: tuple[str, ...]) -> None:
        super().__init__("duplicate JSON field")
        self.path = path


def _reject(
    code: C03CodecCodeV1,
    *path: str,
) -> C03CodecRejectV1:
    return C03CodecRejectV1(code, path)


def _reject_float(_value: str) -> object:
    raise ValueError("floats are not admitted")


def _pairs_hook(pairs: list[tuple[str, object]]) -> _Pairs:
    return _Pairs(pairs)


def _materialize_pairs(value: object, path: tuple[str, ...] = ()) -> object:
    if type(value) is _Pairs:
        result: dict[str, object] = {}
        for key, child in value:
            if key in result:
                raise _DuplicateFieldError(path + (key,))
            result[key] = _materialize_pairs(child, path + (key,))
        return result
    if type(value) is list:
        return [
            _materialize_pairs(child, path + (str(index),))
            for index, child in enumerate(cast(list[object], value))
        ]
    return value


def _decode_envelope(
    payload: object,
    *,
    schema_id: str,
    value_fields: tuple[str, ...],
) -> dict[str, object] | C03CodecRejectV1:
    if type(payload) is not bytes:
        return _reject(C03CodecCodeV1.WRONG_EXACT_TYPE)
    if len(payload) > _MAX_PAYLOAD_BYTES_V1:
        return _reject(C03CodecCodeV1.INVALID_VALUE, "payload")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError:
        return _reject(C03CodecCodeV1.INVALID_UTF8)
    try:
        parsed_pairs = json.loads(
            text,
            object_pairs_hook=_pairs_hook,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
        parsed = _materialize_pairs(parsed_pairs)
    except _DuplicateFieldError as exc:
        return _reject(C03CodecCodeV1.INVALID_VALUE, *exc.path)
    except (TypeError, ValueError, json.JSONDecodeError, RecursionError):
        return _reject(C03CodecCodeV1.INVALID_JSON)
    if type(parsed) is not dict:
        return _reject(C03CodecCodeV1.WRONG_EXACT_TYPE, "envelope")
    envelope = cast(dict[str, object], parsed)
    actual_envelope_fields = set(envelope)
    if actual_envelope_fields != {"schema", "value"}:
        unknown = sorted(actual_envelope_fields - {"schema", "value"})
        if unknown:
            return _reject(C03CodecCodeV1.UNKNOWN_FIELD, "envelope", unknown[0])
        missing = sorted({"schema", "value"} - actual_envelope_fields)
        return _reject(C03CodecCodeV1.MISSING_FIELD, "envelope", missing[0])
    if envelope["schema"] != schema_id:
        return _reject(C03CodecCodeV1.UNKNOWN_SCHEMA, "schema")
    raw_value = envelope["value"]
    if type(raw_value) is not dict:
        return _reject(C03CodecCodeV1.WRONG_EXACT_TYPE, "value")
    value = cast(dict[str, object], raw_value)
    actual_fields = set(value)
    expected_fields = set(value_fields)
    unknown = sorted(actual_fields - expected_fields)
    if unknown:
        return _reject(C03CodecCodeV1.UNKNOWN_FIELD, "value", unknown[0])
    missing = sorted(expected_fields - actual_fields)
    if missing:
        return _reject(C03CodecCodeV1.MISSING_FIELD, "value", missing[0])
    try:
        bounded_json_utf8_size(
            envelope,
            max_bytes=MAX_CANONICAL_BYTES_V1,
            max_depth=MAX_ADMISSION_DEPTH_V1,
            max_items=MAX_ADMISSION_NODES_V1,
        )
        canonical = canonical_json_bytes(envelope)
    except (TypeError, ValueError, UnicodeEncodeError):
        return _reject(C03CodecCodeV1.INVALID_VALUE, "value")
    if canonical != payload:
        return _reject(C03CodecCodeV1.NONCANONICAL_ENCODING)
    return value


def _key_from_value(
    raw: object,
    *,
    path: tuple[str, ...],
) -> EntitlementKeyV1 | C03CodecRejectV1:
    if type(raw) is not dict:
        return _reject(C03CodecCodeV1.WRONG_EXACT_TYPE, *path)
    value = cast(dict[str, object], raw)
    expected = set(ENTITLEMENT_KEY_FIELDS_V1)
    unknown = sorted(set(value) - expected)
    if unknown:
        return _reject(C03CodecCodeV1.UNKNOWN_FIELD, *path, unknown[0])
    missing = sorted(expected - set(value))
    if missing:
        return _reject(C03CodecCodeV1.MISSING_FIELD, *path, missing[0])
    try:
        return EntitlementKeyV1(
            value["fee_distribution_domain_id"],
            value["asset"],
            value["semantic_profile_id"],
            value["fixed_role_order_id"],
        )
    except (TypeError, ValueError):
        return _reject(C03CodecCodeV1.INVALID_VALUE, *path)


def _state_from_value(
    raw: object,
    *,
    path: tuple[str, ...] = ("value",),
) -> EntitlementStateV1 | C03CodecRejectV1:
    if type(raw) is not dict:
        return _reject(C03CodecCodeV1.WRONG_EXACT_TYPE, *path)
    value = cast(dict[str, object], raw)
    expected = set(ENTITLEMENT_STATE_FIELDS_V1)
    unknown = sorted(set(value) - expected)
    if unknown:
        return _reject(C03CodecCodeV1.UNKNOWN_FIELD, *path, unknown[0])
    missing = sorted(expected - set(value))
    if missing:
        return _reject(C03CodecCodeV1.MISSING_FIELD, *path, missing[0])
    key = _key_from_value(value["key"], path=path + ("key",))
    if type(key) is C03CodecRejectV1:
        return key
    representation = value["representation_id"]
    if type(representation) is not str:
        return _reject(C03CodecCodeV1.WRONG_EXACT_TYPE, *path, "representation_id")
    raw_entries = value["entries"]
    if type(raw_entries) is not list:
        return _reject(C03CodecCodeV1.WRONG_EXACT_TYPE, *path, "entries")
    entries: list[EntitlementStateEntryV1] = []
    for index, raw_entry in enumerate(raw_entries):
        entry_path = path + ("entries", str(index))
        if type(raw_entry) is not dict:
            return _reject(C03CodecCodeV1.WRONG_EXACT_TYPE, *entry_path)
        entry_value = cast(dict[str, object], raw_entry)
        expected_entry = set(ENTITLEMENT_STATE_ENTRY_FIELDS_V1)
        unknown = sorted(set(entry_value) - expected_entry)
        if unknown:
            return _reject(C03CodecCodeV1.UNKNOWN_FIELD, *entry_path, unknown[0])
        missing = sorted(expected_entry - set(entry_value))
        if missing:
            return _reject(C03CodecCodeV1.MISSING_FIELD, *entry_path, missing[0])
        coordinates = entry_value["coordinates"]
        if type(coordinates) is not list or len(coordinates) != 3:
            return _reject(C03CodecCodeV1.WRONG_EXACT_TYPE, *entry_path, "coordinates")
        try:
            entries.append(
                EntitlementStateEntryV1(
                    cast(str, entry_value["entry_id"]),
                    cast(tuple[int, int, int], tuple(coordinates)),
                )
            )
        except (TypeError, ValueError):
            return _reject(C03CodecCodeV1.INVALID_VALUE, *entry_path)
    try:
        return EntitlementStateV1(
            cast(EntitlementKeyV1, key),
            representation,
            tuple(entries),
        )
    except (TypeError, ValueError):
        return _reject(C03CodecCodeV1.INVALID_VALUE, *path)


def _key_projection_v1(key: EntitlementKeyV1) -> dict[str, str]:
    return cast(dict[str, str], _entitlement_key_projection_v1(key))


def _entry_projection_v1(entry: EntitlementStateEntryV1) -> dict[str, object]:
    entry.__post_init__()
    return {
        "entry_id": entry.entry_id,
        "coordinates": entry.coordinates,
    }


def _state_projection_v1(state: EntitlementStateV1) -> dict[str, object]:
    state.__post_init__()
    return {
        "key": _key_projection_v1(state.key),
        "representation_id": state.representation_id,
        "entries": tuple(_entry_projection_v1(entry) for entry in state.entries),
    }


def _manifest_projection_v1(
    manifest: RepresentationMigrationManifestV1,
) -> dict[str, object]:
    manifest.__post_init__()
    return {
        "old_semantic_key": _key_projection_v1(manifest.old_semantic_key),
        "new_semantic_key": _key_projection_v1(manifest.new_semantic_key),
        "old_representation_id": manifest.old_representation_id,
        "new_representation_id": manifest.new_representation_id,
        "old_state_root": manifest.old_state_root,
        "new_state_root": manifest.new_state_root,
        "migration_map_id": manifest.migration_map_id,
        "authority_epoch_root": manifest.authority_epoch_root,
        "activation_sequence": manifest.activation_sequence,
    }


def encode_entitlement_state_v1(state: object) -> bytes:
    if type(state) is not EntitlementStateV1:
        raise TypeError("state codec requires an exact EntitlementStateV1")
    envelope = {
        "schema": ENTITLEMENT_STATE_SCHEMA_ID_V1,
        "value": _state_projection_v1(state),
    }
    bounded_json_utf8_size(
        envelope,
        max_bytes=MAX_CANONICAL_BYTES_V1,
        max_depth=MAX_ADMISSION_DEPTH_V1,
        max_items=MAX_ADMISSION_NODES_V1,
    )
    return cast(bytes, canonical_json_bytes(envelope))


def canonical_entitlement_state_root_v1(state: object) -> str:
    return cast(str, sha256_hex(encode_entitlement_state_v1(state)))


def encode_representation_migration_manifest_v1(manifest: object) -> bytes:
    if type(manifest) is not RepresentationMigrationManifestV1:
        raise TypeError("manifest codec requires an exact manifest")
    envelope = {
        "schema": REPRESENTATION_MIGRATION_MANIFEST_SCHEMA_ID_V1,
        "value": _manifest_projection_v1(manifest),
    }
    bounded_json_utf8_size(
        envelope,
        max_bytes=MAX_CANONICAL_BYTES_V1,
        max_depth=MAX_ADMISSION_DEPTH_V1,
        max_items=MAX_ADMISSION_NODES_V1,
    )
    return cast(bytes, canonical_json_bytes(envelope))


def canonical_sha256_migration_manifest_v1(manifest: object) -> str:
    return cast(str, sha256_hex(encode_representation_migration_manifest_v1(manifest)))


def decode_entitlement_state_v1(payload: object) -> C03StateDecodeResultV1:
    envelope = _decode_envelope(
        payload,
        schema_id=ENTITLEMENT_STATE_SCHEMA_ID_V1,
        value_fields=ENTITLEMENT_STATE_FIELDS_V1,
    )
    if type(envelope) is C03CodecRejectV1:
        return envelope
    return _state_from_value(envelope)


def decode_representation_migration_manifest_v1(
    payload: object,
    *,
    expected_old_state: object,
    expected_new_state: object,
) -> C03ManifestDecodeResultV1:
    if type(expected_old_state) is not EntitlementStateV1:
        return _reject(C03CodecCodeV1.VERIFIED_STATE_REQUIRED, "expected_old_state")
    if type(expected_new_state) is not EntitlementStateV1:
        return _reject(C03CodecCodeV1.VERIFIED_STATE_REQUIRED, "expected_new_state")
    old_state = expected_old_state
    new_state = expected_new_state
    envelope = _decode_envelope(
        payload,
        schema_id=REPRESENTATION_MIGRATION_MANIFEST_SCHEMA_ID_V1,
        value_fields=REPRESENTATION_MIGRATION_MANIFEST_FIELDS_V1,
    )
    if type(envelope) is C03CodecRejectV1:
        return envelope
    old_key = _key_from_value(
        envelope["old_semantic_key"],
        path=("value", "old_semantic_key"),
    )
    new_key = _key_from_value(
        envelope["new_semantic_key"],
        path=("value", "new_semantic_key"),
    )
    if type(old_key) is C03CodecRejectV1:
        return old_key
    if type(new_key) is C03CodecRejectV1:
        return new_key
    raw_old_representation = envelope["old_representation_id"]
    raw_new_representation = envelope["new_representation_id"]
    raw_old_root = envelope["old_state_root"]
    raw_new_root = envelope["new_state_root"]
    raw_map_id = envelope["migration_map_id"]
    raw_epoch_root = envelope["authority_epoch_root"]
    raw_sequence = envelope["activation_sequence"]
    if raw_old_representation != old_state.representation_id:
        return _reject(C03CodecCodeV1.INVALID_VALUE, "value", "old_representation_id")
    if raw_new_representation != new_state.representation_id:
        return _reject(C03CodecCodeV1.INVALID_VALUE, "value", "new_representation_id")
    if old_key != old_state.key:
        return _reject(C03CodecCodeV1.INVALID_VALUE, "value", "old_semantic_key")
    if new_key != new_state.key:
        return _reject(C03CodecCodeV1.INVALID_VALUE, "value", "new_semantic_key")
    if raw_old_root != old_state.state_root or raw_new_root != new_state.state_root:
        return _reject(C03CodecCodeV1.STATE_ROOT_MISMATCH, "value", "state_root")
    try:
        return RepresentationMigrationManifestV1(
            old_state,
            new_state,
            cast(str, raw_map_id),
            cast(str, raw_epoch_root),
            cast(int, raw_sequence),
        )
    except (TypeError, ValueError):
        return _reject(C03CodecCodeV1.INVALID_VALUE, "value")


__all__ = (
    "C03CodecCodeV1",
    "C03CodecRejectV1",
    "C03ManifestDecodeResultV1",
    "C03StateDecodeResultV1",
    "canonical_entitlement_state_root_v1",
    "canonical_sha256_migration_manifest_v1",
    "decode_entitlement_state_v1",
    "decode_representation_migration_manifest_v1",
    "encode_entitlement_state_v1",
    "encode_representation_migration_manifest_v1",
)
