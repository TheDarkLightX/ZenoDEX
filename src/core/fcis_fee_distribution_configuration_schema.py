"""Closed schemas for unmounted fee-distribution configuration claims."""

from __future__ import annotations

from ..state.snapshot_combinators import (
    DeclaredFieldV1,
    ExactInt,
    ExactString,
    RecordOf,
    RecordRegistrationV1,
    SchemaRegistrationV1,
    SchemaV1,
    StringRuleV1,
)
from ..state.state_snapshot_values import (
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
)
from .fcis_fee_apportionment_values import (
    BPS_DENOMINATOR_V2,
    FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
    MAX_FEE_AMOUNT_V2,
    FeeDistributionPolicySourceV2,
    FeeDistributionPolicyV2,
)
from .fcis_fee_distribution_configuration_values import (
    FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
    FCISFeeDistributionConfigurationRecordTagV2,
    FeeDistributionConfigurationBodySourceV2,
    FeeDistributionConfigurationBodyV2,
    FeeDistributionConfigurationClaimSourceV2,
    FeeDistributionConfigurationClaimV2,
)


def _field(name: str, schema: SchemaV1) -> DeclaredFieldV1:
    return DeclaredFieldV1(name, schema)


FEE_CONFIGURATION_TEXT_V2 = ExactString(
    StringRuleV1.NON_EMPTY,
    max_utf8_bytes=MAX_STATE_STRING_UTF8_BYTES_V1,
    max_characters=MAX_STATE_STRING_CHARACTERS_V1,
)
FEE_CONFIGURATION_U256_V2 = ExactInt(0, MAX_FEE_AMOUNT_V2)
FEE_CONFIGURATION_POSITIVE_U256_V2 = ExactInt(1, MAX_FEE_AMOUNT_V2)
FEE_CONFIGURATION_BPS_V2 = ExactInt(0, BPS_DENOMINATOR_V2)

FEE_DISTRIBUTION_POLICY_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeDistributionConfigurationRecordTagV2.DISTRIBUTION_POLICY,
    (
        _field("buyback_bps", FEE_CONFIGURATION_BPS_V2),
        _field("treasury_bps", FEE_CONFIGURATION_BPS_V2),
        _field("rewards_bps", FEE_CONFIGURATION_BPS_V2),
        _field("buyback_destination", FEE_CONFIGURATION_TEXT_V2),
        _field("treasury_destination", FEE_CONFIGURATION_TEXT_V2),
        _field("rewards_destination", FEE_CONFIGURATION_TEXT_V2),
    ),
)

FEE_DISTRIBUTION_CONFIGURATION_BODY_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeDistributionConfigurationRecordTagV2.CONFIGURATION_BODY,
    (
        _field("chain_deployment_id", FEE_CONFIGURATION_TEXT_V2),
        _field("configuration_version", FEE_CONFIGURATION_POSITIVE_U256_V2),
        _field("fee_distribution_domain_id", FEE_CONFIGURATION_TEXT_V2),
        _field("policy_root", FEE_CONFIGURATION_TEXT_V2),
        _field("policy", FEE_DISTRIBUTION_POLICY_RECORD_SCHEMA_V2),
        _field("activation_sequence", FEE_CONFIGURATION_U256_V2),
        _field("algorithm_version", FEE_CONFIGURATION_TEXT_V2),
        _field("accepted_language_version", FEE_CONFIGURATION_TEXT_V2),
    ),
)
FEE_DISTRIBUTION_CONFIGURATION_CLAIM_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeDistributionConfigurationRecordTagV2.CONFIGURATION_CLAIM,
    (
        _field("body", FEE_DISTRIBUTION_CONFIGURATION_BODY_RECORD_SCHEMA_V2),
        _field("configuration_root", FEE_CONFIGURATION_TEXT_V2),
    ),
)

FCIS_FEE_DISTRIBUTION_CONFIGURATION_RECORD_REGISTRATIONS_V2 = (
    RecordRegistrationV1(
        FCISFeeDistributionConfigurationRecordTagV2.DISTRIBUTION_POLICY,
        FeeDistributionPolicySourceV2,
        FeeDistributionPolicyV2,
    ),
    RecordRegistrationV1(
        FCISFeeDistributionConfigurationRecordTagV2.CONFIGURATION_BODY,
        FeeDistributionConfigurationBodySourceV2,
        FeeDistributionConfigurationBodyV2,
    ),
    RecordRegistrationV1(
        FCISFeeDistributionConfigurationRecordTagV2.CONFIGURATION_CLAIM,
        FeeDistributionConfigurationClaimSourceV2,
        FeeDistributionConfigurationClaimV2,
    ),
)

FCIS_FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REGISTRATIONS_V2 = (
    SchemaRegistrationV1(
        FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
        FEE_DISTRIBUTION_POLICY_RECORD_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2,
        FEE_DISTRIBUTION_CONFIGURATION_BODY_RECORD_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
        FEE_DISTRIBUTION_CONFIGURATION_CLAIM_RECORD_SCHEMA_V2,
    ),
)

__all__ = (
    "FCIS_FEE_DISTRIBUTION_CONFIGURATION_RECORD_REGISTRATIONS_V2",
    "FCIS_FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REGISTRATIONS_V2",
    "FEE_DISTRIBUTION_CONFIGURATION_BODY_RECORD_SCHEMA_V2",
    "FEE_DISTRIBUTION_CONFIGURATION_CLAIM_RECORD_SCHEMA_V2",
)
