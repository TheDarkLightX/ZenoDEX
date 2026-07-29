"""Strict closed admission for the unmounted FCIS B1B-1 carrier bytes."""

from __future__ import annotations

import json
from dataclasses import fields
from typing import cast

from ..state.canonical import canonical_json_bytes
from .fcis_b1b_authority_schema import (
    FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2,
    FCIS_B1B_AUTHORITY_SOURCE_TYPES_BY_SCHEMA_V2,
)
from .fcis_b1b_authority_values import (
    DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2,
    FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
    MAX_B1B_CANONICAL_BYTES_V2,
    MAX_B1B_JSON_COLLECTION_ITEMS_V2,
    MAX_B1B_JSON_DEPTH_V2,
    MAX_B1B_JSON_NODES_V2,
    V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
    B1BAuthorityAdmissionCodeV2,
    B1BAuthorityAdmissionRejectV2,
    B1BAuthorityAdmissionResultV2,
    B1BAuthoritySourceV2,
    DeploymentBootstrapAnchorClaimSourceV2,
    DeploymentBootstrapAnchorClaimV2,
    FCISAuthorityHeaderSourceV2,
    FCISAuthorityHeaderV2,
    V1ToV2MigrationManifestSourceV2,
    V1ToV2MigrationManifestV2,
)


class _Pairs(tuple[tuple[str, object], ...]):
    pass


class _DuplicateFieldError(ValueError):
    def __init__(self, path: tuple[str, ...]) -> None:
        super().__init__("duplicate JSON field")
        self.path = path


class _JsonResourceScannerV2:
    """Bound work before the host JSON parser sees attacker-controlled input."""

    def __init__(self, text: str) -> None:
        self._text = text
        self._depth = 0
        self._nodes = 0
        self._collection_commas: list[int] = []
        self._in_string = False
        self._escaped = False
        self._in_primitive = False

    def scan(self) -> B1BAuthorityAdmissionRejectV2 | None:
        for character in self._text:
            if self._in_string:
                self._scan_string_character(character)
                continue
            if self._in_primitive and character not in " \t\r\n,]}:":
                continue
            self._in_primitive = False
            reject = self._scan_token(character)
            if reject is not None:
                return reject
        return None

    def _scan_string_character(self, character: str) -> None:
        if self._escaped:
            self._escaped = False
        elif character == "\\":
            self._escaped = True
        elif character == '"':
            self._in_string = False

    def _scan_token(self, character: str) -> B1BAuthorityAdmissionRejectV2 | None:
        if character == '"':
            self._in_string = True
            return self._add_node()
        if character in "[{":
            if self._depth >= MAX_B1B_JSON_DEPTH_V2:
                return _reject(B1BAuthorityAdmissionCodeV2.JSON_DEPTH_LIMIT)
            node_reject = self._add_node()
            if node_reject is not None:
                return node_reject
            self._depth += 1
            self._collection_commas.append(0)
            return None
        if character in "]}":
            if self._depth:
                self._depth -= 1
                self._collection_commas.pop()
            return None
        if character == "," and self._collection_commas:
            next_commas = self._collection_commas[-1] + 1
            if next_commas >= MAX_B1B_JSON_COLLECTION_ITEMS_V2:
                return _reject(B1BAuthorityAdmissionCodeV2.JSON_COLLECTION_LIMIT)
            self._collection_commas[-1] = next_commas
            return None
        if character in "-0123456789tfn":
            self._in_primitive = True
            return self._add_node()
        return None

    def _add_node(self) -> B1BAuthorityAdmissionRejectV2 | None:
        self._nodes += 1
        if self._nodes > MAX_B1B_JSON_NODES_V2:
            return _reject(B1BAuthorityAdmissionCodeV2.JSON_NODE_LIMIT)
        return None


def validate_fcis_b1b_json_resource_bounds_v2(
    payload: object,
) -> B1BAuthorityAdmissionRejectV2 | None:
    """Reject attacker-controlled JSON before parser recursion or allocation grows."""

    if type(payload) is not bytes:
        return _reject(B1BAuthorityAdmissionCodeV2.WRONG_EXACT_TYPE)
    exact_payload = payload
    if len(exact_payload) > MAX_B1B_CANONICAL_BYTES_V2:
        return _reject(B1BAuthorityAdmissionCodeV2.BYTE_LIMIT)
    try:
        text = exact_payload.decode("utf-8")
    except UnicodeDecodeError:
        return _reject(B1BAuthorityAdmissionCodeV2.INVALID_UTF8)
    return _JsonResourceScannerV2(text).scan()


def _reject(code: B1BAuthorityAdmissionCodeV2, *path: str) -> B1BAuthorityAdmissionRejectV2:
    return B1BAuthorityAdmissionRejectV2(code, path)


def _reject_float(_text: str) -> object:
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


def _construct_from_source_v2(schema_id: str, source: object) -> B1BAuthorityAdmissionResultV2:
    expected_source = FCIS_B1B_AUTHORITY_SOURCE_TYPES_BY_SCHEMA_V2.get(schema_id)
    if expected_source is None:
        return _reject(B1BAuthorityAdmissionCodeV2.UNKNOWN_SCHEMA, "schema")
    if type(source) is not expected_source:
        return _reject(B1BAuthorityAdmissionCodeV2.WRONG_EXACT_TYPE, "value")
    try:
        if schema_id == FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2:
            header_source = cast(FCISAuthorityHeaderSourceV2, source)
            return FCISAuthorityHeaderV2(
                cast(str, header_source.chain_deployment_id),
                cast(int, header_source.sequence),
                cast(str, header_source.fee_distribution_configuration_root),
            )
        if schema_id == DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2:
            anchor_source = cast(DeploymentBootstrapAnchorClaimSourceV2, source)
            return DeploymentBootstrapAnchorClaimV2(
                cast(str, anchor_source.chain_deployment_id),
                cast(str, anchor_source.expected_migration_manifest_root),
            )
        if schema_id == V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2:
            manifest_source = cast(V1ToV2MigrationManifestSourceV2, source)
            return V1ToV2MigrationManifestV2(
                cast(str, manifest_source.chain_deployment_id),
                cast(str, manifest_source.expected_v1_pre_root),
                cast(str, manifest_source.fee_distribution_domain_id),
                cast(str, manifest_source.expected_initial_configuration_root),
                cast(int, manifest_source.initial_sequence),
                cast(int, manifest_source.initial_configuration_version),
                cast(int, manifest_source.initial_activation_sequence),
                cast(int, manifest_source.source_snapshot_version),
                cast(int, manifest_source.target_snapshot_version),
            )
    except (TypeError, ValueError):
        return _reject(B1BAuthorityAdmissionCodeV2.INVALID_VALUE, "value")
    return _reject(B1BAuthorityAdmissionCodeV2.UNKNOWN_SCHEMA, "schema")


def admit_fcis_b1b_authority_source_v2(
    schema_id: str,
    source: object,
) -> B1BAuthorityAdmissionResultV2:
    if type(schema_id) is not str:
        return _reject(B1BAuthorityAdmissionCodeV2.WRONG_EXACT_TYPE, "schema")
    return _construct_from_source_v2(schema_id, source)


def _source_from_mapping_v2(schema_id: str, value: dict[str, object]) -> object:
    if schema_id == FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2:
        return FCISAuthorityHeaderSourceV2(
            value["chain_deployment_id"],
            value["sequence"],
            value["fee_distribution_configuration_root"],
        )
    if schema_id == DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2:
        return DeploymentBootstrapAnchorClaimSourceV2(
            value["chain_deployment_id"],
            value["expected_migration_manifest_root"],
        )
    if schema_id == V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2:
        return V1ToV2MigrationManifestSourceV2(
            value["chain_deployment_id"],
            value["expected_v1_pre_root"],
            value["fee_distribution_domain_id"],
            value["expected_initial_configuration_root"],
            value["initial_sequence"],
            value["initial_configuration_version"],
            value["initial_activation_sequence"],
            value["source_snapshot_version"],
            value["target_snapshot_version"],
        )
    raise ValueError("unknown B1B authority carrier schema")


def decode_fcis_b1b_authority_v2(payload: object) -> B1BAuthorityAdmissionResultV2:
    """Decode one uniquely encoded canonical carrier and consume all bytes."""

    resource_reject = validate_fcis_b1b_json_resource_bounds_v2(payload)
    if resource_reject is not None:
        return resource_reject
    exact_payload = cast(bytes, payload)
    text = exact_payload.decode("utf-8")
    try:
        parsed_pairs = json.loads(
            text,
            object_pairs_hook=_pairs_hook,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
        parsed = _materialize_pairs(parsed_pairs)
    except _DuplicateFieldError as exc:
        return B1BAuthorityAdmissionRejectV2(
            B1BAuthorityAdmissionCodeV2.DUPLICATE_FIELD,
            exc.path,
        )
    except (TypeError, ValueError, json.JSONDecodeError, RecursionError):
        return _reject(B1BAuthorityAdmissionCodeV2.INVALID_JSON)
    if type(parsed) is not dict:
        return _reject(B1BAuthorityAdmissionCodeV2.WRONG_EXACT_TYPE)
    envelope = cast(dict[str, object], parsed)
    envelope_fields = set(envelope)
    unknown_envelope = sorted(envelope_fields - {"schema", "value"})
    if unknown_envelope:
        return _reject(B1BAuthorityAdmissionCodeV2.UNKNOWN_FIELD, unknown_envelope[0])
    missing_envelope = sorted({"schema", "value"} - envelope_fields)
    if missing_envelope:
        return _reject(B1BAuthorityAdmissionCodeV2.MISSING_FIELD, missing_envelope[0])
    schema_id = envelope["schema"]
    if type(schema_id) is not str:
        return _reject(B1BAuthorityAdmissionCodeV2.WRONG_EXACT_TYPE, "schema")
    if schema_id not in FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2:
        return _reject(B1BAuthorityAdmissionCodeV2.UNKNOWN_SCHEMA, "schema")
    raw_value = envelope["value"]
    if type(raw_value) is not dict:
        return _reject(B1BAuthorityAdmissionCodeV2.WRONG_EXACT_TYPE, "value")
    value = cast(dict[str, object], raw_value)
    expected_fields = set(FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2[schema_id])
    actual_fields = set(value)
    unknown = sorted(actual_fields - expected_fields)
    if unknown:
        return _reject(B1BAuthorityAdmissionCodeV2.UNKNOWN_FIELD, "value", unknown[0])
    missing = sorted(expected_fields - actual_fields)
    if missing:
        return _reject(B1BAuthorityAdmissionCodeV2.MISSING_FIELD, "value", missing[0])
    try:
        canonical = canonical_json_bytes(envelope)
    except (TypeError, ValueError, UnicodeEncodeError):
        return _reject(B1BAuthorityAdmissionCodeV2.INVALID_VALUE, "value")
    if canonical != exact_payload:
        return _reject(B1BAuthorityAdmissionCodeV2.NONCANONICAL_ENCODING)
    source = _source_from_mapping_v2(schema_id, value)
    exact_source = cast(B1BAuthoritySourceV2, source)
    if tuple(field.name for field in fields(exact_source)) != (
        FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2[schema_id]
    ):
        return _reject(B1BAuthorityAdmissionCodeV2.UNKNOWN_FIELD, "value")
    return _construct_from_source_v2(schema_id, source)


__all__ = (
    "admit_fcis_b1b_authority_source_v2",
    "decode_fcis_b1b_authority_v2",
    "validate_fcis_b1b_json_resource_bounds_v2",
)
