"""Caller-safe bindings for the closed FCIS execution-context profile."""

from __future__ import annotations

from typing import cast

from .fcis_execution_context_admission import admit as _admit_context_profile
from .fcis_execution_context_values import (
    FCIS_EXECUTION_CONTEXT_SCHEMA_REVISION_V1,
    FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1,
    FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
    FCISSettlementExecutionContextV1,
    FCISStepExecutionContextV1,
)
from .snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
    MAX_COLLECTION_ITEMS_V1,
    AdmissionLimitsV1,
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)

_FCIS_EXECUTION_CONTEXT_ADMISSION_LIMITS_V1 = build_admission_limits_v1(
    AdmissionLimitsV1(
        max_depth=MAX_ADMISSION_DEPTH_V1,
        max_nodes=MAX_ADMISSION_NODES_V1,
        max_canonical_bytes=MAX_CANONICAL_BYTES_V1,
        max_collection_items=MAX_COLLECTION_ITEMS_V1,
    )
)
if type(_FCIS_EXECUTION_CONTEXT_ADMISSION_LIMITS_V1) is not ValidatedAdmissionLimitsV1:
    raise RuntimeError("FCIS execution-context admission limits are invalid")


def admit_fcis_settlement_execution_context_v1(
    source: object,
) -> AdmitOk[FCISSettlementExecutionContextV1] | AdmitReject:
    """Admit or re-admit one exact settlement context with no partial value."""

    result = _admit_context_profile(
        FCIS_EXECUTION_CONTEXT_SCHEMA_REVISION_V1,
        FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1,
        _FCIS_EXECUTION_CONTEXT_ADMISSION_LIMITS_V1,
        source,
    )
    return cast(AdmitOk[FCISSettlementExecutionContextV1] | AdmitReject, result)


def admit_fcis_step_execution_context_v1(
    source: object,
) -> AdmitOk[FCISStepExecutionContextV1] | AdmitReject:
    """Admit every policy input for one step through one closed schema."""

    result = _admit_context_profile(
        FCIS_EXECUTION_CONTEXT_SCHEMA_REVISION_V1,
        FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
        _FCIS_EXECUTION_CONTEXT_ADMISSION_LIMITS_V1,
        source,
    )
    return cast(AdmitOk[FCISStepExecutionContextV1] | AdmitReject, result)


__all__ = (
    "admit_fcis_settlement_execution_context_v1",
    "admit_fcis_step_execution_context_v1",
)
