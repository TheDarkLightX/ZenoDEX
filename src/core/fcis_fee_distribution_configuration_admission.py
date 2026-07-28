"""Closed admission profile for fee-distribution configuration claims."""

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
from .fcis_fee_apportionment_values import (
    FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
    FeeDistributionPolicyV2,
)
from .fcis_fee_distribution_configuration_codec import (
    encode_fee_distribution_configuration_v2,
)
from .fcis_fee_distribution_configuration_schema import (
    FCIS_FEE_DISTRIBUTION_CONFIGURATION_RECORD_REGISTRATIONS_V2,
    FCIS_FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REGISTRATIONS_V2,
)
from .fcis_fee_distribution_configuration_values import (
    FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2,
    FCISFeeDistributionConfigurationEnumTagV2,
    FCISFeeDistributionConfigurationRecordTagV2,
    FeeDistributionConfigurationBodyV2,
    FeeDistributionConfigurationClaimV2,
)

FCIS_REQUIRED_REGISTRY_IDS = (
    "zenodex/fcis/fee-distribution/policy/v2",
    "zenodex/fcis/fee-distribution/configuration-body/v2",
    "zenodex/fcis/fee-distribution/configuration-claim/v2",
)
FCIS_REGISTERED_REGISTRY_IDS = (
    "zenodex/fcis/fee-distribution/policy/v2",
    "zenodex/fcis/fee-distribution/configuration-body/v2",
    "zenodex/fcis/fee-distribution/configuration-claim/v2",
)


def _record_field(
    values: tuple[tuple[str, object], ...],
    index: int,
    expected_name: str,
) -> object:
    if type(values) is not tuple or index >= len(values):
        raise ValueError("fee configuration field registry drift")
    field = values[index]
    if type(field) is not tuple or len(field) != 2 or field[0] != expected_name:
        raise ValueError("fee configuration field registry drift")
    return field[1]


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


def _construct_body_v2(
    values: tuple[tuple[str, object], ...],
) -> FeeDistributionConfigurationBodyV2:
    if len(values) != 8:
        raise ValueError("unsupported fee configuration body record")
    return FeeDistributionConfigurationBodyV2(
        cast(str, _record_field(values, 0, "chain_deployment_id")),
        cast(int, _record_field(values, 1, "configuration_version")),
        cast(str, _record_field(values, 2, "fee_distribution_domain_id")),
        cast(str, _record_field(values, 3, "policy_root")),
        cast(FeeDistributionPolicyV2, _record_field(values, 4, "policy")),
        cast(int, _record_field(values, 5, "activation_sequence")),
        cast(str, _record_field(values, 6, "algorithm_version")),
        cast(str, _record_field(values, 7, "accepted_language_version")),
    )


def _construct_claim_v2(
    values: tuple[tuple[str, object], ...],
) -> FeeDistributionConfigurationClaimV2:
    if len(values) != 2:
        raise ValueError("unsupported fee configuration claim record")
    return FeeDistributionConfigurationClaimV2(
        cast(FeeDistributionConfigurationBodyV2, _record_field(values, 0, "body")),
        cast(str, _record_field(values, 1, "configuration_root")),
    )


def _construct_fee_configuration_record_v2(
    record_tag: Enum,
    values: tuple[tuple[str, object], ...],
) -> object:
    if record_tag is FCISFeeDistributionConfigurationRecordTagV2.DISTRIBUTION_POLICY:
        return _construct_policy_v2(values)
    if record_tag is FCISFeeDistributionConfigurationRecordTagV2.CONFIGURATION_BODY:
        return _construct_body_v2(values)
    if record_tag is FCISFeeDistributionConfigurationRecordTagV2.CONFIGURATION_CLAIM:
        return _construct_claim_v2(values)
    raise ValueError("unsupported fee distribution configuration record")


_FCIS_FEE_DISTRIBUTION_CONFIGURATION_ADMISSION_REGISTRY_V2 = build_admission_registry_v1(
    schema_revision=FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2,
    enum_tag_type=FCISFeeDistributionConfigurationEnumTagV2,
    record_tag_type=FCISFeeDistributionConfigurationRecordTagV2,
    enum_registrations=(),
    record_registrations=FCIS_FEE_DISTRIBUTION_CONFIGURATION_RECORD_REGISTRATIONS_V2,
    schema_registrations=FCIS_FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REGISTRATIONS_V2,
)
if (
    _FCIS_FEE_DISTRIBUTION_CONFIGURATION_ADMISSION_REGISTRY_V2.schema_ids
    != FCIS_REGISTERED_REGISTRY_IDS
):
    raise RuntimeError("fee distribution configuration registry manifest drift")


def _canonical_fee_configuration_encoder_v2(
    schema_id: str,
    value: object,
) -> bytes:
    if schema_id == FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2:
        return cast(bytes, encode_fcis_fee_apportionment_v2(schema_id, value))
    if schema_id in (
        FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2,
        FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
    ):
        return encode_fee_distribution_configuration_v2(schema_id, value)
    raise ValueError("unknown fee distribution configuration schema")


def admit(
    schema_revision: str,
    schema_id: str,
    validated_limits: ValidatedAdmissionLimitsV1,
    source: object,
) -> AdmitOk[object] | AdmitReject:
    """Admit through the sole source-owned configuration-claim profile."""

    return snapshot_combinators._admit_with_registry_v1(
        _FCIS_FEE_DISTRIBUTION_CONFIGURATION_ADMISSION_REGISTRY_V2,
        schema_revision,
        schema_id,
        validated_limits,
        source,
        _construct_fee_configuration_record_v2,
        _canonical_fee_configuration_encoder_v2,
    )


__all__ = ("admit",)
