"""Closed four-argument admission profile for FCIS execution context."""

from __future__ import annotations

from enum import Enum
from typing import cast

from . import snapshot_combinators
from .fcis_execution_context_codec import encode_fcis_execution_context_v1
from .fcis_execution_context_schema import (
    FCIS_EXECUTION_CONTEXT_ENUM_REGISTRATIONS_V1,
    FCIS_EXECUTION_CONTEXT_RECORD_REGISTRATIONS_V1,
    FCIS_EXECUTION_CONTEXT_SCHEMA_REGISTRATIONS_V1,
)
from .fcis_execution_context_values import (
    FCIS_EXECUTION_CONTEXT_SCHEMA_REVISION_V1,
    FCISExecutionContextEnumTagV1,
    FCISExecutionContextRecordTagV1,
    FCISFeeSplitPolicyV1,
    FCISSettlementExecutionContextV1,
    FCISStepExecutionContextV1,
)
from .lp_duration_policy_values import LPDurationRiskPolicyV1
from .owned_collections import OwnedEnumV1
from .snapshot_combinators import (
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    build_admission_registry_v1,
)

FCIS_REQUIRED_REGISTRY_IDS = (
    "zenodex/fcis/context/settlement-value/v1",
    "zenodex/fcis/context/step-value/v1",
)
FCIS_REGISTERED_REGISTRY_IDS = (
    "zenodex/fcis/context/settlement-value/v1",
    "zenodex/fcis/context/step-value/v1",
)

_FCIS_EXECUTION_CONTEXT_ADMISSION_REGISTRY_V1 = build_admission_registry_v1(
    schema_revision=FCIS_EXECUTION_CONTEXT_SCHEMA_REVISION_V1,
    enum_tag_type=FCISExecutionContextEnumTagV1,
    record_tag_type=FCISExecutionContextRecordTagV1,
    enum_registrations=FCIS_EXECUTION_CONTEXT_ENUM_REGISTRATIONS_V1,
    record_registrations=FCIS_EXECUTION_CONTEXT_RECORD_REGISTRATIONS_V1,
    schema_registrations=FCIS_EXECUTION_CONTEXT_SCHEMA_REGISTRATIONS_V1,
)
if _FCIS_EXECUTION_CONTEXT_ADMISSION_REGISTRY_V1.schema_ids != FCIS_REGISTERED_REGISTRY_IDS:
    raise RuntimeError("FCIS execution-context admission registry manifest drift")


def _record_field(
    values: tuple[tuple[str, object], ...],
    index: int,
    expected_name: str,
) -> object:
    if type(values) is not tuple or index >= len(values):
        raise ValueError("FCIS execution-context field registry drift")
    field = values[index]
    if type(field) is not tuple or len(field) != 2 or field[0] != expected_name:
        raise ValueError("FCIS execution-context field registry drift")
    return field[1]


def _construct_settlement_v1(
    values: tuple[tuple[str, object], ...],
) -> FCISSettlementExecutionContextV1:
    if len(values) != 7:
        raise ValueError("unsupported FCIS settlement-context record")
    return FCISSettlementExecutionContextV1(
        now=cast(int, _record_field(values, 0, "now")),
        min_lp_position_age_seconds=cast(
            int,
            _record_field(values, 1, "min_lp_position_age_seconds"),
        ),
        mode=cast(OwnedEnumV1, _record_field(values, 2, "mode")),
        allow_cow_netting=cast(bool, _record_field(values, 3, "allow_cow_netting")),
        allow_snapshot_bound_quote_bindings=cast(
            bool,
            _record_field(values, 4, "allow_snapshot_bound_quote_bindings"),
        ),
        protocol_fee_share_bps=cast(
            int,
            _record_field(values, 5, "protocol_fee_share_bps"),
        ),
        protocol_fee_recipient_pubkey=cast(
            str | None,
            _record_field(values, 6, "protocol_fee_recipient_pubkey"),
        ),
    )


def _construct_fee_split_v1(
    values: tuple[tuple[str, object], ...],
) -> FCISFeeSplitPolicyV1:
    if len(values) != 3:
        raise ValueError("unsupported FCIS fee-split record")
    return FCISFeeSplitPolicyV1(
        buyback_bps=cast(int, _record_field(values, 0, "buyback_bps")),
        treasury_bps=cast(int, _record_field(values, 1, "treasury_bps")),
        rewards_bps=cast(int, _record_field(values, 2, "rewards_bps")),
    )


def _construct_lp_duration_v1(
    values: tuple[tuple[str, object], ...],
) -> LPDurationRiskPolicyV1:
    if len(values) != 6:
        raise ValueError("unsupported FCIS LP duration-policy record")
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


def _construct_step_v1(
    values: tuple[tuple[str, object], ...],
) -> FCISStepExecutionContextV1:
    if len(values) != 6:
        raise ValueError("unsupported FCIS step-context record")
    return FCISStepExecutionContextV1(
        settlement=cast(
            FCISSettlementExecutionContextV1,
            _record_field(values, 0, "settlement"),
        ),
        require_all_nonces=cast(
            bool,
            _record_field(values, 1, "require_all_nonces"),
        ),
        reject_settlements_with_rejected_intents=cast(
            bool,
            _record_field(values, 2, "reject_settlements_with_rejected_intents"),
        ),
        fee_split_policy=cast(
            FCISFeeSplitPolicyV1 | None,
            _record_field(values, 3, "fee_split_policy"),
        ),
        lp_duration_policy=cast(
            LPDurationRiskPolicyV1 | None,
            _record_field(values, 4, "lp_duration_policy"),
        ),
        snapshot_version=cast(int, _record_field(values, 5, "snapshot_version")),
    )


def _construct_context_record(
    record_tag: Enum,
    values: tuple[tuple[str, object], ...],
) -> object:
    if record_tag is FCISExecutionContextRecordTagV1.SETTLEMENT:
        return _construct_settlement_v1(values)
    if record_tag is FCISExecutionContextRecordTagV1.FEE_SPLIT:
        return _construct_fee_split_v1(values)
    if record_tag is FCISExecutionContextRecordTagV1.LP_DURATION_POLICY:
        return _construct_lp_duration_v1(values)
    if record_tag is FCISExecutionContextRecordTagV1.STEP:
        return _construct_step_v1(values)
    raise ValueError("unsupported FCIS execution-context record")


def _canonical_context_encoder(schema_id: str, value: object) -> bytes:
    """Keep executable encoder authority private to this closed profile."""

    return encode_fcis_execution_context_v1(schema_id, value)


def admit(
    schema_revision: str,
    schema_id: str,
    validated_limits: ValidatedAdmissionLimitsV1,
    source: object,
) -> AdmitOk[object] | AdmitReject:
    """Admit through the sole source-owned FCIS execution-context profile."""

    return snapshot_combinators._admit_with_registry_v1(
        _FCIS_EXECUTION_CONTEXT_ADMISSION_REGISTRY_V1,
        schema_revision,
        schema_id,
        validated_limits,
        source,
        _construct_context_record,
        _canonical_context_encoder,
    )


__all__ = ("admit",)
