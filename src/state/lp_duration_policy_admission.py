"""Closed four-argument admission profile for the LP duration-risk context."""

from __future__ import annotations

from enum import Enum
from typing import cast

from . import snapshot_combinators
from .canonical import bounded_json_utf8_size, canonical_json_bytes
from .lp_duration_policy_schema import (
    LP_DURATION_POLICY_RECORD_REGISTRATIONS_V1,
    LP_DURATION_POLICY_SCHEMA_ID_V1,
    LP_DURATION_POLICY_SCHEMA_REGISTRATIONS_V1,
    LP_DURATION_POLICY_SCHEMA_REVISION_V1,
    LPDurationPolicyEnumTagV1,
    LPDurationPolicyRecordTagV1,
)
from .lp_duration_policy_values import LPDurationRiskPolicyV1
from .snapshot_combinators import (
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    build_admission_registry_v1,
)

FCIS_REQUIRED_REGISTRY_IDS = ("zenodex/fcis/context/lp-duration-policy-value/v1",)
FCIS_REGISTERED_REGISTRY_IDS = ("zenodex/fcis/context/lp-duration-policy-value/v1",)

_LP_DURATION_POLICY_ADMISSION_REGISTRY_V1 = build_admission_registry_v1(
    schema_revision=LP_DURATION_POLICY_SCHEMA_REVISION_V1,
    enum_tag_type=LPDurationPolicyEnumTagV1,
    record_tag_type=LPDurationPolicyRecordTagV1,
    enum_registrations=(),
    record_registrations=LP_DURATION_POLICY_RECORD_REGISTRATIONS_V1,
    schema_registrations=LP_DURATION_POLICY_SCHEMA_REGISTRATIONS_V1,
)
if _LP_DURATION_POLICY_ADMISSION_REGISTRY_V1.schema_ids != FCIS_REGISTERED_REGISTRY_IDS:
    raise RuntimeError("LP duration-policy admission registry manifest drift")


def _record_field(
    values: tuple[tuple[str, object], ...],
    index: int,
    expected_name: str,
) -> object:
    if type(values) is not tuple or index >= len(values):
        raise ValueError("LP duration-policy field registry drift")
    field = values[index]
    if type(field) is not tuple or len(field) != 2 or field[0] != expected_name:
        raise ValueError("LP duration-policy field registry drift")
    return field[1]


def _construct_context_record(
    record_tag: Enum,
    values: tuple[tuple[str, object], ...],
) -> object:
    if record_tag is not LPDurationPolicyRecordTagV1.LP_DURATION_POLICY or len(values) != 6:
        raise ValueError("unsupported LP duration-policy record")
    return LPDurationRiskPolicyV1(
        base_age_seconds=cast(int, _record_field(values, 0, "base_age_seconds")),
        max_age_seconds=cast(int, _record_field(values, 1, "max_age_seconds")),
        churn_window_seconds=cast(
            int,
            _record_field(values, 2, "churn_window_seconds"),
        ),
        decay_seconds=cast(int, _record_field(values, 3, "decay_seconds")),
        multiplier=cast(int, _record_field(values, 4, "multiplier")),
        max_churn_tier=cast(int, _record_field(values, 5, "max_churn_tier")),
    )


def _canonical_context_encoder(schema_id: str, value: object) -> bytes:
    if schema_id != LP_DURATION_POLICY_SCHEMA_ID_V1:
        raise ValueError("unknown LP duration-policy schema")
    if value is None:
        projection: object = None
    elif type(value) is LPDurationRiskPolicyV1:
        exact = cast(LPDurationRiskPolicyV1, value)
        projection = {
            "base_age_seconds": exact.base_age_seconds,
            "max_age_seconds": exact.max_age_seconds,
            "churn_window_seconds": exact.churn_window_seconds,
            "decay_seconds": exact.decay_seconds,
            "multiplier": exact.multiplier,
            "max_churn_tier": exact.max_churn_tier,
        }
    else:
        raise TypeError("LP duration-policy schema and output disagree")
    bounded_json_utf8_size(
        projection,
        max_bytes=snapshot_combinators.MAX_CANONICAL_BYTES_V1,
        max_depth=snapshot_combinators.MAX_ADMISSION_DEPTH_V1,
        max_items=snapshot_combinators.MAX_COLLECTION_ITEMS_V1,
    )
    return canonical_json_bytes(projection)


def admit(
    schema_revision: str,
    schema_id: str,
    validated_limits: ValidatedAdmissionLimitsV1,
    source: object,
) -> AdmitOk[object] | AdmitReject:
    """Admit through the sole source-owned LP duration-policy profile."""

    return snapshot_combinators._admit_with_registry_v1(
        _LP_DURATION_POLICY_ADMISSION_REGISTRY_V1,
        schema_revision,
        schema_id,
        validated_limits,
        source,
        _construct_context_record,
        _canonical_context_encoder,
    )


__all__ = ("admit",)
