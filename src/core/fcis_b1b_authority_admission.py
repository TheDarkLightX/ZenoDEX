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
    V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
    B1BAuthorityAdmissionCodeV2,
    B1BAuthorityAdmissionRejectV2,
    B1BAuthorityAdmissionResultV2,
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


def _reject(code: B1BAuthorityAdmissionCodeV2, *path: str) -> B1BAuthorityAdmissionRejectV2:
    return B1BAuthorityAdmissionRejectV2(code, path)


def _reject_float(_text: str) -> object:
    raise ValueError("floats are not admitted")


def _pairs_hook(pairs: list[tuple[str, object]]) -> _Pairs:
    return _Pairs(pairs)


def _materialize_pairs(value: object, path: tuple[str, ...] = ()) -> object:
    if type(value) is _Pairs:
        result: dict[str, object] = {}
        for key, child in cast(_Pairs, value):
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
            exact = cast(FCISAuthorityHeaderSourceV2, source)
            return FCISAuthorityHeaderV2(
                exact.chain_deployment_id,
                exact.sequence,
                exact.fee_distribution_configuration_root,
            )
        if schema_id == DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2:
            exact = cast(DeploymentBootstrapAnchorClaimSourceV2, source)
            return DeploymentBootstrapAnchorClaimV2(
                exact.chain_deployment_id,
                exact.expected_migration_manifest_root,
            )
        if schema_id == V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2:
            exact = cast(V1ToV2MigrationManifestSourceV2, source)
            return V1ToV2MigrationManifestV2(
                exact.chain_deployment_id,
                exact.expected_v1_pre_root,
                exact.fee_distribution_domain_id,
                exact.expected_initial_configuration_root,
                exact.initial_sequence,
                exact.initial_configuration_version,
                exact.initial_activation_sequence,
                exact.source_snapshot_version,
                exact.target_snapshot_version,
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

    if type(payload) is not bytes:
        return _reject(B1BAuthorityAdmissionCodeV2.WRONG_EXACT_TYPE)
    exact_payload = cast(bytes, payload)
    if len(exact_payload) > MAX_B1B_CANONICAL_BYTES_V2:
        return _reject(B1BAuthorityAdmissionCodeV2.BYTE_LIMIT)
    try:
        text = exact_payload.decode("utf-8")
    except UnicodeDecodeError:
        return _reject(B1BAuthorityAdmissionCodeV2.INVALID_UTF8)
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
    except (TypeError, ValueError, json.JSONDecodeError):
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
    if tuple(field.name for field in fields(source)) != (
        FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2[schema_id]
    ):
        return _reject(B1BAuthorityAdmissionCodeV2.UNKNOWN_FIELD, "value")
    return _construct_from_source_v2(schema_id, source)


__all__ = (
    "admit_fcis_b1b_authority_source_v2",
    "decode_fcis_b1b_authority_v2",
)
