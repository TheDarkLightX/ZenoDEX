"""Closed declarative schemas for unmounted SRGD-v1 candidate values."""

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
from .fcis_fee_apportionment_values import (
    BPS_DENOMINATOR_V2,
    COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
    FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2,
    FEE_AMOUNT_CANDIDATE_SCHEMA_ID_V2,
    FEE_APPORTIONMENT_KEY_SCHEMA_ID_V2,
    FEE_DEFICIT_ENTRY_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
    MAX_FEE_AMOUNT_CANDIDATES_V2,
    MAX_FEE_AMOUNT_V2,
    MAX_FEE_APPORTIONMENT_KEYS_V2,
    CommittedFeeApportionmentStateSourceV2,
    CommittedFeeApportionmentStateV2,
    FCISFeeApportionmentRecordTagV2,
    FeeAmountCandidateSourceV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeySourceV2,
    FeeApportionmentKeyV2,
    FeeDeficitEntrySourceV2,
    FeeDeficitEntryV2,
    FeeDistributionPolicySourceV2,
    FeeDistributionPolicyV2,
)


def _field(name: str, schema: SchemaV1) -> DeclaredFieldV1:
    return DeclaredFieldV1(name, schema)


FEE_APPORTIONMENT_TEXT_V2 = ExactString(
    StringRuleV1.NON_EMPTY,
    max_utf8_bytes=MAX_STATE_STRING_UTF8_BYTES_V1,
    max_characters=MAX_STATE_STRING_CHARACTERS_V1,
)
FEE_APPORTIONMENT_U256_V2 = ExactInt(0, MAX_FEE_AMOUNT_V2)
FEE_APPORTIONMENT_BPS_V2 = ExactInt(0, BPS_DENOMINATOR_V2)
FEE_APPORTIONMENT_DEFICIT_V2 = ExactInt(
    -BPS_DENOMINATOR_V2 + 1,
    BPS_DENOMINATOR_V2 - 1,
)

FEE_APPORTIONMENT_KEY_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeApportionmentRecordTagV2.KEY,
    (
        _field("fee_distribution_domain_id", FEE_APPORTIONMENT_TEXT_V2),
        _field("asset", FEE_APPORTIONMENT_TEXT_V2),
    ),
)
FEE_AMOUNT_CANDIDATE_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeApportionmentRecordTagV2.AMOUNT_CANDIDATE,
    (
        _field("key", FEE_APPORTIONMENT_KEY_RECORD_SCHEMA_V2),
        _field("amount", FEE_APPORTIONMENT_U256_V2),
    ),
)
FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_V2 = SequenceOf(
    (SequenceSourceKind.EXACT_TUPLE,),
    FEE_AMOUNT_CANDIDATE_RECORD_SCHEMA_V2,
    0,
    MAX_FEE_AMOUNT_CANDIDATES_V2,
)
FEE_DEFICIT_ENTRY_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeApportionmentRecordTagV2.DEFICIT_ENTRY,
    (
        _field("key", FEE_APPORTIONMENT_KEY_RECORD_SCHEMA_V2),
        _field("deficit_buyback", FEE_APPORTIONMENT_DEFICIT_V2),
        _field("deficit_treasury", FEE_APPORTIONMENT_DEFICIT_V2),
    ),
)
COMMITTED_FEE_APPORTIONMENT_STATE_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeApportionmentRecordTagV2.COMMITTED_STATE,
    (
        _field("algorithm_version", FEE_APPORTIONMENT_TEXT_V2),
        _field(
            "entries",
            SequenceOf(
                (SequenceSourceKind.EXACT_TUPLE,),
                FEE_DEFICIT_ENTRY_RECORD_SCHEMA_V2,
                0,
                MAX_FEE_APPORTIONMENT_KEYS_V2,
            ),
        ),
    ),
)
FEE_DISTRIBUTION_POLICY_RECORD_SCHEMA_V2 = RecordOf(
    FCISFeeApportionmentRecordTagV2.DISTRIBUTION_POLICY,
    (
        _field("buyback_bps", FEE_APPORTIONMENT_BPS_V2),
        _field("treasury_bps", FEE_APPORTIONMENT_BPS_V2),
        _field("rewards_bps", FEE_APPORTIONMENT_BPS_V2),
        _field("buyback_destination", FEE_APPORTIONMENT_TEXT_V2),
        _field("treasury_destination", FEE_APPORTIONMENT_TEXT_V2),
        _field("rewards_destination", FEE_APPORTIONMENT_TEXT_V2),
    ),
)

FCIS_FEE_APPORTIONMENT_RECORD_REGISTRATIONS_V2 = (
    RecordRegistrationV1(
        FCISFeeApportionmentRecordTagV2.KEY,
        FeeApportionmentKeySourceV2,
        FeeApportionmentKeyV2,
    ),
    RecordRegistrationV1(
        FCISFeeApportionmentRecordTagV2.AMOUNT_CANDIDATE,
        FeeAmountCandidateSourceV2,
        FeeAmountCandidateV2,
    ),
    RecordRegistrationV1(
        FCISFeeApportionmentRecordTagV2.DEFICIT_ENTRY,
        FeeDeficitEntrySourceV2,
        FeeDeficitEntryV2,
    ),
    RecordRegistrationV1(
        FCISFeeApportionmentRecordTagV2.COMMITTED_STATE,
        CommittedFeeApportionmentStateSourceV2,
        CommittedFeeApportionmentStateV2,
    ),
    RecordRegistrationV1(
        FCISFeeApportionmentRecordTagV2.DISTRIBUTION_POLICY,
        FeeDistributionPolicySourceV2,
        FeeDistributionPolicyV2,
    ),
)

FCIS_FEE_APPORTIONMENT_SCHEMA_REGISTRATIONS_V2 = (
    SchemaRegistrationV1(
        FEE_APPORTIONMENT_KEY_SCHEMA_ID_V2,
        FEE_APPORTIONMENT_KEY_RECORD_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        FEE_AMOUNT_CANDIDATE_SCHEMA_ID_V2,
        FEE_AMOUNT_CANDIDATE_RECORD_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2,
        FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        FEE_DEFICIT_ENTRY_SCHEMA_ID_V2,
        FEE_DEFICIT_ENTRY_RECORD_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
        COMMITTED_FEE_APPORTIONMENT_STATE_RECORD_SCHEMA_V2,
    ),
    SchemaRegistrationV1(
        FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
        FEE_DISTRIBUTION_POLICY_RECORD_SCHEMA_V2,
    ),
)

__all__ = (
    "COMMITTED_FEE_APPORTIONMENT_STATE_RECORD_SCHEMA_V2",
    "FCIS_FEE_APPORTIONMENT_RECORD_REGISTRATIONS_V2",
    "FCIS_FEE_APPORTIONMENT_SCHEMA_REGISTRATIONS_V2",
    "FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_V2",
    "FEE_AMOUNT_CANDIDATE_RECORD_SCHEMA_V2",
    "FEE_APPORTIONMENT_KEY_RECORD_SCHEMA_V2",
    "FEE_DEFICIT_ENTRY_RECORD_SCHEMA_V2",
    "FEE_DISTRIBUTION_POLICY_RECORD_SCHEMA_V2",
)
