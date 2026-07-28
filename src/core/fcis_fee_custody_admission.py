"""Closed deterministic admission profile for FCIS fee-custody V2 values."""

from __future__ import annotations

from enum import Enum
from typing import cast

from ..state import snapshot_combinators
from ..state.snapshot_combinators import (
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    build_admission_registry_v1,
)
from .fcis_fee_custody_codec import encode_fcis_fee_custody_v2
from .fcis_fee_custody_schema import (
    FCIS_FEE_CUSTODY_RECORD_REGISTRATIONS_V2,
    FCIS_FEE_CUSTODY_SCHEMA_REGISTRATIONS_V2,
)
from .fcis_fee_custody_values import (
    FEE_CUSTODY_SCHEMA_REVISION_V2,
    AssetFeeDistributionV2,
    CommittedFeeAccumulatorStateV2,
    FCISFeeCustodyEnumTagV2,
    FCISFeeCustodyRecordTagV2,
    FeeDistributionPolicyV2,
    FeeDustEntryV2,
    ProtocolFeeCreditV2,
)

FCIS_REQUIRED_REGISTRY_IDS = (
    "zenodex/fcis/fee-custody/protocol-credit/v2",
    "zenodex/fcis/fee-custody/protocol-credit-batch/v2",
    "zenodex/fcis/fee-custody/distribution-policy/v2",
    "zenodex/fcis/fee-custody/accumulator/v2",
    "zenodex/fcis/fee-custody/asset-distribution/v2",
    "zenodex/fcis/fee-custody/asset-distribution-batch/v2",
)
FCIS_REGISTERED_REGISTRY_IDS = (
    "zenodex/fcis/fee-custody/protocol-credit/v2",
    "zenodex/fcis/fee-custody/protocol-credit-batch/v2",
    "zenodex/fcis/fee-custody/distribution-policy/v2",
    "zenodex/fcis/fee-custody/accumulator/v2",
    "zenodex/fcis/fee-custody/asset-distribution/v2",
    "zenodex/fcis/fee-custody/asset-distribution-batch/v2",
)


def _record_field(
    values: tuple[tuple[str, object], ...],
    index: int,
    expected_name: str,
) -> object:
    if type(values) is not tuple or index >= len(values):
        raise ValueError("fee-custody field registry drift")
    field = values[index]
    if type(field) is not tuple or len(field) != 2 or field[0] != expected_name:
        raise ValueError("fee-custody field registry drift")
    return field[1]


def _construct_credit_v2(values: tuple[tuple[str, object], ...]) -> ProtocolFeeCreditV2:
    if len(values) != 3:
        raise ValueError("unsupported protocol fee credit record")
    return ProtocolFeeCreditV2(
        cast(str, _record_field(values, 0, "source_custody_pubkey")),
        cast(str, _record_field(values, 1, "asset")),
        cast(int, _record_field(values, 2, "amount")),
    )


def _construct_policy_v2(
    values: tuple[tuple[str, object], ...],
) -> FeeDistributionPolicyV2:
    if len(values) != 6:
        raise ValueError("unsupported fee distribution policy record")
    return FeeDistributionPolicyV2(
        cast(int, _record_field(values, 0, "buyback_bps")),
        cast(int, _record_field(values, 1, "treasury_bps")),
        cast(int, _record_field(values, 2, "rewards_bps")),
        cast(str, _record_field(values, 3, "buyback_custody_pubkey")),
        cast(str, _record_field(values, 4, "treasury_custody_pubkey")),
        cast(str, _record_field(values, 5, "rewards_custody_pubkey")),
    )


def _construct_dust_v2(values: tuple[tuple[str, object], ...]) -> FeeDustEntryV2:
    if len(values) != 3:
        raise ValueError("unsupported fee dust record")
    return FeeDustEntryV2(
        cast(str, _record_field(values, 0, "source_custody_pubkey")),
        cast(str, _record_field(values, 1, "asset")),
        cast(int, _record_field(values, 2, "amount")),
    )


def _construct_accumulator_v2(
    values: tuple[tuple[str, object], ...],
) -> CommittedFeeAccumulatorStateV2:
    if len(values) != 1:
        raise ValueError("unsupported fee accumulator record")
    return CommittedFeeAccumulatorStateV2(
        cast(tuple[FeeDustEntryV2, ...], _record_field(values, 0, "entries"))
    )


def _construct_distribution_v2(
    values: tuple[tuple[str, object], ...],
) -> AssetFeeDistributionV2:
    if len(values) != 9:
        raise ValueError("unsupported asset fee distribution record")
    return AssetFeeDistributionV2(
        cast(str, _record_field(values, 0, "source_custody_pubkey")),
        cast(str, _record_field(values, 1, "asset")),
        cast(str, _record_field(values, 2, "buyback_custody_pubkey")),
        cast(str, _record_field(values, 3, "treasury_custody_pubkey")),
        cast(str, _record_field(values, 4, "rewards_custody_pubkey")),
        cast(int, _record_field(values, 5, "buyback_amount")),
        cast(int, _record_field(values, 6, "treasury_amount")),
        cast(int, _record_field(values, 7, "rewards_amount")),
        cast(int, _record_field(values, 8, "dust_carried")),
    )


def _construct_fee_custody_record_v2(
    record_tag: Enum,
    values: tuple[tuple[str, object], ...],
) -> object:
    if record_tag is FCISFeeCustodyRecordTagV2.PROTOCOL_FEE_CREDIT:
        return _construct_credit_v2(values)
    if record_tag is FCISFeeCustodyRecordTagV2.DISTRIBUTION_POLICY:
        return _construct_policy_v2(values)
    if record_tag is FCISFeeCustodyRecordTagV2.DUST_ENTRY:
        return _construct_dust_v2(values)
    if record_tag is FCISFeeCustodyRecordTagV2.ACCUMULATOR:
        return _construct_accumulator_v2(values)
    if record_tag is FCISFeeCustodyRecordTagV2.ASSET_DISTRIBUTION:
        return _construct_distribution_v2(values)
    raise ValueError("unsupported fee-custody record")


_FCIS_FEE_CUSTODY_ADMISSION_REGISTRY_V2 = build_admission_registry_v1(
    schema_revision=FEE_CUSTODY_SCHEMA_REVISION_V2,
    enum_tag_type=FCISFeeCustodyEnumTagV2,
    record_tag_type=FCISFeeCustodyRecordTagV2,
    enum_registrations=(),
    record_registrations=FCIS_FEE_CUSTODY_RECORD_REGISTRATIONS_V2,
    schema_registrations=FCIS_FEE_CUSTODY_SCHEMA_REGISTRATIONS_V2,
)
if _FCIS_FEE_CUSTODY_ADMISSION_REGISTRY_V2.schema_ids != FCIS_REGISTERED_REGISTRY_IDS:
    raise RuntimeError("fee-custody admission registry manifest drift")


def _canonical_fee_custody_encoder_v2(schema_id: str, value: object) -> bytes:
    return encode_fcis_fee_custody_v2(schema_id, value)


def admit(
    schema_revision: str,
    schema_id: str,
    validated_limits: ValidatedAdmissionLimitsV1,
    source: object,
) -> AdmitOk[object] | AdmitReject:
    """Admit through the sole source-owned fee-custody V2 profile."""

    return snapshot_combinators._admit_with_registry_v1(
        _FCIS_FEE_CUSTODY_ADMISSION_REGISTRY_V2,
        schema_revision,
        schema_id,
        validated_limits,
        source,
        _construct_fee_custody_record_v2,
        _canonical_fee_custody_encoder_v2,
    )


__all__ = ("admit",)
