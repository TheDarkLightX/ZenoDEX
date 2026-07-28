"""Closed admission profile for unmounted SRGD-v1 candidate values."""

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
from .fcis_fee_apportionment_codec import encode_fcis_fee_apportionment_v2
from .fcis_fee_apportionment_schema import (
    FCIS_FEE_APPORTIONMENT_RECORD_REGISTRATIONS_V2,
    FCIS_FEE_APPORTIONMENT_SCHEMA_REGISTRATIONS_V2,
)
from .fcis_fee_apportionment_values import (
    FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
    CommittedFeeApportionmentStateV2,
    FCISFeeApportionmentEnumTagV2,
    FCISFeeApportionmentRecordTagV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
    FeeDeficitEntryV2,
    FeeDistributionPolicyV2,
)

FCIS_REQUIRED_REGISTRY_IDS = (
    "zenodex/fcis/fee-apportionment/key/v2",
    "zenodex/fcis/fee-apportionment/amount-candidate/v2",
    "zenodex/fcis/fee-apportionment/amount-candidate-batch/v2",
    "zenodex/fcis/fee-apportionment/deficit-entry/v2",
    "zenodex/fcis/fee-apportionment/committed-state/v2",
    "zenodex/fcis/fee-distribution/policy/v2",
)
FCIS_REGISTERED_REGISTRY_IDS = (
    "zenodex/fcis/fee-apportionment/key/v2",
    "zenodex/fcis/fee-apportionment/amount-candidate/v2",
    "zenodex/fcis/fee-apportionment/amount-candidate-batch/v2",
    "zenodex/fcis/fee-apportionment/deficit-entry/v2",
    "zenodex/fcis/fee-apportionment/committed-state/v2",
    "zenodex/fcis/fee-distribution/policy/v2",
)


def _record_field(
    values: tuple[tuple[str, object], ...],
    index: int,
    expected_name: str,
) -> object:
    if type(values) is not tuple or index >= len(values):
        raise ValueError("fee-apportionment field registry drift")
    field = values[index]
    if type(field) is not tuple or len(field) != 2 or field[0] != expected_name:
        raise ValueError("fee-apportionment field registry drift")
    return field[1]


def _construct_key_v2(
    values: tuple[tuple[str, object], ...],
) -> FeeApportionmentKeyV2:
    if len(values) != 2:
        raise ValueError("unsupported fee-apportionment key record")
    return FeeApportionmentKeyV2(
        cast(str, _record_field(values, 0, "fee_distribution_domain_id")),
        cast(str, _record_field(values, 1, "asset")),
    )


def _construct_candidate_v2(
    values: tuple[tuple[str, object], ...],
) -> FeeAmountCandidateV2:
    if len(values) != 2:
        raise ValueError("unsupported fee amount candidate record")
    return FeeAmountCandidateV2(
        cast(FeeApportionmentKeyV2, _record_field(values, 0, "key")),
        cast(int, _record_field(values, 1, "amount")),
    )


def _construct_deficit_entry_v2(
    values: tuple[tuple[str, object], ...],
) -> FeeDeficitEntryV2:
    if len(values) != 3:
        raise ValueError("unsupported fee deficit entry record")
    return FeeDeficitEntryV2(
        cast(FeeApportionmentKeyV2, _record_field(values, 0, "key")),
        cast(int, _record_field(values, 1, "deficit_buyback")),
        cast(int, _record_field(values, 2, "deficit_treasury")),
    )


def _construct_state_v2(
    values: tuple[tuple[str, object], ...],
) -> CommittedFeeApportionmentStateV2:
    if len(values) != 2:
        raise ValueError("unsupported committed fee-apportionment state record")
    return CommittedFeeApportionmentStateV2(
        cast(str, _record_field(values, 0, "algorithm_version")),
        cast(
            tuple[FeeDeficitEntryV2, ...],
            _record_field(values, 1, "entries"),
        ),
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
        cast(str, _record_field(values, 3, "buyback_destination")),
        cast(str, _record_field(values, 4, "treasury_destination")),
        cast(str, _record_field(values, 5, "rewards_destination")),
    )


def _construct_fee_apportionment_record_v2(
    record_tag: Enum,
    values: tuple[tuple[str, object], ...],
) -> object:
    if record_tag is FCISFeeApportionmentRecordTagV2.KEY:
        return _construct_key_v2(values)
    if record_tag is FCISFeeApportionmentRecordTagV2.AMOUNT_CANDIDATE:
        return _construct_candidate_v2(values)
    if record_tag is FCISFeeApportionmentRecordTagV2.DEFICIT_ENTRY:
        return _construct_deficit_entry_v2(values)
    if record_tag is FCISFeeApportionmentRecordTagV2.COMMITTED_STATE:
        return _construct_state_v2(values)
    if record_tag is FCISFeeApportionmentRecordTagV2.DISTRIBUTION_POLICY:
        return _construct_policy_v2(values)
    raise ValueError("unsupported fee-apportionment record")


_FCIS_FEE_APPORTIONMENT_ADMISSION_REGISTRY_V2 = build_admission_registry_v1(
    schema_revision=FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
    enum_tag_type=FCISFeeApportionmentEnumTagV2,
    record_tag_type=FCISFeeApportionmentRecordTagV2,
    enum_registrations=(),
    record_registrations=FCIS_FEE_APPORTIONMENT_RECORD_REGISTRATIONS_V2,
    schema_registrations=FCIS_FEE_APPORTIONMENT_SCHEMA_REGISTRATIONS_V2,
)
if _FCIS_FEE_APPORTIONMENT_ADMISSION_REGISTRY_V2.schema_ids != FCIS_REGISTERED_REGISTRY_IDS:
    raise RuntimeError("fee-apportionment admission registry manifest drift")


def _canonical_fee_apportionment_encoder_v2(
    schema_id: str,
    value: object,
) -> bytes:
    return encode_fcis_fee_apportionment_v2(schema_id, value)


def admit(
    schema_revision: str,
    schema_id: str,
    validated_limits: ValidatedAdmissionLimitsV1,
    source: object,
) -> AdmitOk[object] | AdmitReject:
    """Admit through the sole source-owned SRGD-v1 candidate profile."""

    return snapshot_combinators._admit_with_registry_v1(
        _FCIS_FEE_APPORTIONMENT_ADMISSION_REGISTRY_V2,
        schema_revision,
        schema_id,
        validated_limits,
        source,
        _construct_fee_apportionment_record_v2,
        _canonical_fee_apportionment_encoder_v2,
    )


__all__ = ("admit",)
