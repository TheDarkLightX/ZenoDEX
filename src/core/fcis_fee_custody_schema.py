"""Closed declarative schemas for FCIS per-custody fee values."""

from __future__ import annotations

from ..state.snapshot_combinators import (
    DeclaredFieldV1,
    ExactInt,
    ExactString,
    RecordOf,
    RecordRegistrationV1,
    SchemaRegistrationV1,
    SchemaV1,
    SequenceOf,
    SequenceSourceKind,
    StringRuleV1,
)
from ..state.state_snapshot_values import (
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
)
from .fcis_fee_custody_values import (
    ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_ID_V2,
    ASSET_FEE_DISTRIBUTION_SCHEMA_ID_V2,
    BPS_DENOMINATOR_V2,
    FEE_ACCUMULATOR_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
    MAX_FEE_AMOUNT_V2,
    MAX_FEE_CREDITS_V2,
    MAX_FEE_CUSTODY_KEYS_V2,
    PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2,
    PROTOCOL_FEE_CREDIT_SCHEMA_ID_V2,
    AssetFeeDistributionSourceV2,
    AssetFeeDistributionV2,
    CommittedFeeAccumulatorStateV2,
    FCISFeeCustodyRecordTagV2,
    FeeAccumulatorSourceV2,
    FeeDistributionPolicySourceV2,
    FeeDistributionPolicyV2,
    FeeDustEntrySourceV2,
    FeeDustEntryV2,
    ProtocolFeeCreditSourceV2,
    ProtocolFeeCreditV2,
)


def _field(name: str, schema: SchemaV1) -> DeclaredFieldV1:
    return DeclaredFieldV1(name, schema)


FEE_CUSTODY_TEXT_V2 = ExactString(
    StringRuleV1.NON_EMPTY,
    max_utf8_bytes=MAX_STATE_STRING_UTF8_BYTES_V1,
    max_characters=MAX_STATE_STRING_CHARACTERS_V1,
)
FEE_CUSTODY_AMOUNT_V2 = ExactInt(0, MAX_FEE_AMOUNT_V2)
POSITIVE_FEE_CUSTODY_AMOUNT_V2 = ExactInt(1, MAX_FEE_AMOUNT_V2)
FEE_CUSTODY_BPS_V2 = ExactInt(0, BPS_DENOMINATOR_V2)

PROTOCOL_FEE_CREDIT_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeCustodyRecordTagV2.PROTOCOL_FEE_CREDIT,
    (
        _field("source_custody_pubkey", FEE_CUSTODY_TEXT_V2),
        _field("asset", FEE_CUSTODY_TEXT_V2),
        _field("amount", POSITIVE_FEE_CUSTODY_AMOUNT_V2),
    ),
)
PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_V2 = SequenceOf(
    (SequenceSourceKind.EXACT_TUPLE,),
    PROTOCOL_FEE_CREDIT_RECORD_SCHEMA_V2,
    0,
    MAX_FEE_CREDITS_V2,
)
FEE_DISTRIBUTION_POLICY_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeCustodyRecordTagV2.DISTRIBUTION_POLICY,
    (
        _field("buyback_bps", FEE_CUSTODY_BPS_V2),
        _field("treasury_bps", FEE_CUSTODY_BPS_V2),
        _field("rewards_bps", FEE_CUSTODY_BPS_V2),
        _field("buyback_custody_pubkey", FEE_CUSTODY_TEXT_V2),
        _field("treasury_custody_pubkey", FEE_CUSTODY_TEXT_V2),
        _field("rewards_custody_pubkey", FEE_CUSTODY_TEXT_V2),
    ),
)
FEE_DUST_ENTRY_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeCustodyRecordTagV2.DUST_ENTRY,
    (
        _field("source_custody_pubkey", FEE_CUSTODY_TEXT_V2),
        _field("asset", FEE_CUSTODY_TEXT_V2),
        _field("amount", POSITIVE_FEE_CUSTODY_AMOUNT_V2),
    ),
)
FEE_ACCUMULATOR_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeCustodyRecordTagV2.ACCUMULATOR,
    (
        _field(
            "entries",
            SequenceOf(
                (SequenceSourceKind.EXACT_TUPLE,),
                FEE_DUST_ENTRY_RECORD_SCHEMA_V2,
                0,
                MAX_FEE_CUSTODY_KEYS_V2,
            ),
        ),
    ),
)
ASSET_FEE_DISTRIBUTION_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeCustodyRecordTagV2.ASSET_DISTRIBUTION,
    (
        _field("source_custody_pubkey", FEE_CUSTODY_TEXT_V2),
        _field("asset", FEE_CUSTODY_TEXT_V2),
        _field("buyback_custody_pubkey", FEE_CUSTODY_TEXT_V2),
        _field("treasury_custody_pubkey", FEE_CUSTODY_TEXT_V2),
        _field("rewards_custody_pubkey", FEE_CUSTODY_TEXT_V2),
        _field("buyback_amount", FEE_CUSTODY_AMOUNT_V2),
        _field("treasury_amount", FEE_CUSTODY_AMOUNT_V2),
        _field("rewards_amount", FEE_CUSTODY_AMOUNT_V2),
        _field("dust_carried", FEE_CUSTODY_AMOUNT_V2),
    ),
)
ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_V2 = SequenceOf(
    (SequenceSourceKind.EXACT_TUPLE,),
    ASSET_FEE_DISTRIBUTION_RECORD_SCHEMA_V2,
    0,
    MAX_FEE_CUSTODY_KEYS_V2,
)

FCIS_FEE_CUSTODY_RECORD_REGISTRATIONS_V2 = (
    RecordRegistrationV1(
        FCISFeeCustodyRecordTagV2.PROTOCOL_FEE_CREDIT,
        ProtocolFeeCreditSourceV2,
        ProtocolFeeCreditV2,
    ),
    RecordRegistrationV1(
        FCISFeeCustodyRecordTagV2.DISTRIBUTION_POLICY,
        FeeDistributionPolicySourceV2,
        FeeDistributionPolicyV2,
    ),
    RecordRegistrationV1(
        FCISFeeCustodyRecordTagV2.DUST_ENTRY,
        FeeDustEntrySourceV2,
        FeeDustEntryV2,
    ),
    RecordRegistrationV1(
        FCISFeeCustodyRecordTagV2.ACCUMULATOR,
        FeeAccumulatorSourceV2,
        CommittedFeeAccumulatorStateV2,
    ),
    RecordRegistrationV1(
        FCISFeeCustodyRecordTagV2.ASSET_DISTRIBUTION,
        AssetFeeDistributionSourceV2,
        AssetFeeDistributionV2,
    ),
)

FCIS_FEE_CUSTODY_SCHEMA_REGISTRATIONS_V2 = (
    SchemaRegistrationV1(
        PROTOCOL_FEE_CREDIT_SCHEMA_ID_V2,
        PROTOCOL_FEE_CREDIT_RECORD_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2,
        PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
        FEE_DISTRIBUTION_POLICY_RECORD_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        FEE_ACCUMULATOR_SCHEMA_ID_V2,
        FEE_ACCUMULATOR_RECORD_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        ASSET_FEE_DISTRIBUTION_SCHEMA_ID_V2,
        ASSET_FEE_DISTRIBUTION_RECORD_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_ID_V2,
        ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_V2,
    ),
)

__all__ = (
    "ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_V2",
    "ASSET_FEE_DISTRIBUTION_RECORD_SCHEMA_V2",
    "FCIS_FEE_CUSTODY_RECORD_REGISTRATIONS_V2",
    "FCIS_FEE_CUSTODY_SCHEMA_REGISTRATIONS_V2",
    "FEE_ACCUMULATOR_RECORD_SCHEMA_V2",
    "FEE_DISTRIBUTION_POLICY_RECORD_SCHEMA_V2",
    "PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_V2",
    "PROTOCOL_FEE_CREDIT_RECORD_SCHEMA_V2",
)
