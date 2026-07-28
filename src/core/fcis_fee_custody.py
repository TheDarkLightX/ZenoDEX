"""Caller-safe facade for the closed FCIS fee-custody V2 profile."""

from __future__ import annotations

from typing import cast

from ..state.snapshot_combinators import (
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
from .fcis_fee_custody_admission import admit as _admit_fee_custody_v2
from .fcis_fee_custody_values import (
    ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_ID_V2,
    FEE_ACCUMULATOR_SCHEMA_ID_V2,
    FEE_CUSTODY_SCHEMA_REVISION_V2,
    FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
    PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2,
    AssetFeeDistributionV2,
    CommittedFeeAccumulatorStateV2,
    FeeDistributionPolicyV2,
    ProtocolFeeCreditV2,
)

_FEE_CUSTODY_LIMITS_V2 = build_admission_limits_v1(
    AdmissionLimitsV1(
        max_depth=MAX_ADMISSION_DEPTH_V1,
        max_nodes=MAX_ADMISSION_NODES_V1,
        max_canonical_bytes=MAX_CANONICAL_BYTES_V1,
        max_collection_items=MAX_COLLECTION_ITEMS_V1,
    )
)
if type(_FEE_CUSTODY_LIMITS_V2) is not ValidatedAdmissionLimitsV1:
    raise RuntimeError("fee-custody admission limits are invalid")


def admit_protocol_fee_credit_batch_v2(
    source: object,
) -> AdmitOk[tuple[ProtocolFeeCreditV2, ...]] | AdmitReject:
    result = _admit_fee_custody_v2(
        FEE_CUSTODY_SCHEMA_REVISION_V2,
        PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2,
        _FEE_CUSTODY_LIMITS_V2,
        source,
    )
    return cast(AdmitOk[tuple[ProtocolFeeCreditV2, ...]] | AdmitReject, result)


def admit_fee_distribution_policy_v2(
    source: object,
) -> AdmitOk[FeeDistributionPolicyV2] | AdmitReject:
    result = _admit_fee_custody_v2(
        FEE_CUSTODY_SCHEMA_REVISION_V2,
        FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
        _FEE_CUSTODY_LIMITS_V2,
        source,
    )
    return cast(AdmitOk[FeeDistributionPolicyV2] | AdmitReject, result)


def admit_fee_accumulator_v2(
    source: object,
) -> AdmitOk[CommittedFeeAccumulatorStateV2] | AdmitReject:
    result = _admit_fee_custody_v2(
        FEE_CUSTODY_SCHEMA_REVISION_V2,
        FEE_ACCUMULATOR_SCHEMA_ID_V2,
        _FEE_CUSTODY_LIMITS_V2,
        source,
    )
    return cast(AdmitOk[CommittedFeeAccumulatorStateV2] | AdmitReject, result)


def admit_asset_fee_distribution_batch_v2(
    source: object,
) -> AdmitOk[tuple[AssetFeeDistributionV2, ...]] | AdmitReject:
    result = _admit_fee_custody_v2(
        FEE_CUSTODY_SCHEMA_REVISION_V2,
        ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_ID_V2,
        _FEE_CUSTODY_LIMITS_V2,
        source,
    )
    return cast(AdmitOk[tuple[AssetFeeDistributionV2, ...]] | AdmitReject, result)


__all__ = (
    "admit_asset_fee_distribution_batch_v2",
    "admit_fee_accumulator_v2",
    "admit_fee_distribution_policy_v2",
    "admit_protocol_fee_credit_batch_v2",
)
