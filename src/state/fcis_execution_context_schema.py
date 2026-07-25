"""Closed declarative schema for deterministic FCIS execution context."""

from __future__ import annotations

from .dex_snapshot_profile import (
    DEX_SNAPSHOT_MAX_VERSION_V1,
    DEX_SNAPSHOT_MIN_VERSION_V1,
)
from .fcis_execution_context_values import (
    BPS_DENOMINATOR_V1,
    FCIS_CONTEXT_STRING_MAX_CHARACTERS_V1,
    FCIS_CONTEXT_STRING_MAX_UTF8_BYTES_V1,
    FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1,
    FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
    FCISExecutionContextEnumTagV1,
    FCISExecutionContextRecordTagV1,
    FCISFeeSplitPolicySourceV1,
    FCISFeeSplitPolicyV1,
    FCISSettlementExecutionContextSourceV1,
    FCISSettlementExecutionContextV1,
    FCISSettlementModeV1,
    FCISStepExecutionContextSourceV1,
    FCISStepExecutionContextV1,
)
from .lp_duration_policy_schema import LPDurationPolicyAdmissionSourceV1
from .lp_duration_policy_values import LPDurationRiskPolicyV1
from .snapshot_combinators import (
    DeclaredFieldV1,
    EnumRegistrationV1,
    ExactBool,
    ExactEnum,
    ExactInt,
    ExactString,
    OptionalValue,
    RecordOf,
    RecordRegistrationV1,
    SchemaRegistrationV1,
    StringRuleV1,
)

FCIS_SETTLEMENT_CONTEXT_FIELD_NAMES_V1 = (
    "now",
    "min_lp_position_age_seconds",
    "mode",
    "allow_cow_netting",
    "allow_snapshot_bound_quote_bindings",
    "protocol_fee_share_bps",
    "protocol_fee_recipient_pubkey",
)
FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1 = (
    "buyback_bps",
    "treasury_bps",
    "rewards_bps",
)
FCIS_LP_DURATION_POLICY_FIELD_NAMES_V1 = (
    "base_age_seconds",
    "max_age_seconds",
    "churn_window_seconds",
    "decay_seconds",
    "multiplier",
    "max_churn_tier",
)
FCIS_STEP_CONTEXT_FIELD_NAMES_V1 = (
    "settlement",
    "require_all_nonces",
    "reject_settlements_with_rejected_intents",
    "fee_split_policy",
    "lp_duration_policy",
    "snapshot_version",
)

FCIS_SETTLEMENT_CONTEXT_RECORD_SCHEMA_V1 = RecordOf(
    FCISExecutionContextRecordTagV1.SETTLEMENT,
    (
        DeclaredFieldV1("now", ExactInt(0, None)),
        DeclaredFieldV1("min_lp_position_age_seconds", ExactInt(0, None)),
        DeclaredFieldV1(
            "mode",
            ExactEnum(FCISExecutionContextEnumTagV1.SETTLEMENT_MODE),
        ),
        DeclaredFieldV1("allow_cow_netting", ExactBool()),
        DeclaredFieldV1("allow_snapshot_bound_quote_bindings", ExactBool()),
        DeclaredFieldV1(
            "protocol_fee_share_bps",
            ExactInt(0, BPS_DENOMINATOR_V1),
        ),
        DeclaredFieldV1(
            "protocol_fee_recipient_pubkey",
            OptionalValue(
                ExactString(
                    StringRuleV1.NON_EMPTY,
                    max_utf8_bytes=FCIS_CONTEXT_STRING_MAX_UTF8_BYTES_V1,
                    max_characters=FCIS_CONTEXT_STRING_MAX_CHARACTERS_V1,
                )
            ),
        ),
    ),
)

FCIS_FEE_SPLIT_POLICY_RECORD_SCHEMA_V1 = RecordOf(
    FCISExecutionContextRecordTagV1.FEE_SPLIT,
    tuple(
        DeclaredFieldV1(field_name, ExactInt(0, BPS_DENOMINATOR_V1))
        for field_name in FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1
    ),
)

FCIS_LP_DURATION_POLICY_RECORD_SCHEMA_V1 = RecordOf(
    FCISExecutionContextRecordTagV1.LP_DURATION_POLICY,
    (
        DeclaredFieldV1("base_age_seconds", ExactInt(0, None)),
        DeclaredFieldV1("max_age_seconds", ExactInt(0, None)),
        DeclaredFieldV1("churn_window_seconds", ExactInt(0, None)),
        DeclaredFieldV1("decay_seconds", ExactInt(0, None)),
        DeclaredFieldV1("multiplier", ExactInt(1, None)),
        DeclaredFieldV1("max_churn_tier", ExactInt(0, None)),
    ),
)

FCIS_STEP_CONTEXT_RECORD_SCHEMA_V1 = RecordOf(
    FCISExecutionContextRecordTagV1.STEP,
    (
        DeclaredFieldV1("settlement", FCIS_SETTLEMENT_CONTEXT_RECORD_SCHEMA_V1),
        DeclaredFieldV1("require_all_nonces", ExactBool()),
        DeclaredFieldV1("reject_settlements_with_rejected_intents", ExactBool()),
        DeclaredFieldV1(
            "fee_split_policy",
            OptionalValue(FCIS_FEE_SPLIT_POLICY_RECORD_SCHEMA_V1),
        ),
        DeclaredFieldV1(
            "lp_duration_policy",
            OptionalValue(FCIS_LP_DURATION_POLICY_RECORD_SCHEMA_V1),
        ),
        DeclaredFieldV1(
            "snapshot_version",
            ExactInt(
                DEX_SNAPSHOT_MIN_VERSION_V1,
                DEX_SNAPSHOT_MAX_VERSION_V1,
            ),
        ),
    ),
)

FCIS_EXECUTION_CONTEXT_ENUM_REGISTRATIONS_V1 = (
    EnumRegistrationV1(
        FCISExecutionContextEnumTagV1.SETTLEMENT_MODE,
        FCISSettlementModeV1,
    ),
)

FCIS_EXECUTION_CONTEXT_RECORD_REGISTRATIONS_V1 = (
    RecordRegistrationV1(
        FCISExecutionContextRecordTagV1.SETTLEMENT,
        FCISSettlementExecutionContextSourceV1,
        FCISSettlementExecutionContextV1,
    ),
    RecordRegistrationV1(
        FCISExecutionContextRecordTagV1.FEE_SPLIT,
        FCISFeeSplitPolicySourceV1,
        FCISFeeSplitPolicyV1,
    ),
    RecordRegistrationV1(
        FCISExecutionContextRecordTagV1.LP_DURATION_POLICY,
        LPDurationPolicyAdmissionSourceV1,
        LPDurationRiskPolicyV1,
    ),
    RecordRegistrationV1(
        FCISExecutionContextRecordTagV1.STEP,
        FCISStepExecutionContextSourceV1,
        FCISStepExecutionContextV1,
    ),
)

FCIS_EXECUTION_CONTEXT_SCHEMA_REGISTRATIONS_V1 = (
    SchemaRegistrationV1(
        FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1,
        FCIS_SETTLEMENT_CONTEXT_RECORD_SCHEMA_V1,
    ),
    SchemaRegistrationV1(
        FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
        FCIS_STEP_CONTEXT_RECORD_SCHEMA_V1,
    ),
)

__all__ = (
    "FCIS_EXECUTION_CONTEXT_ENUM_REGISTRATIONS_V1",
    "FCIS_EXECUTION_CONTEXT_RECORD_REGISTRATIONS_V1",
    "FCIS_EXECUTION_CONTEXT_SCHEMA_REGISTRATIONS_V1",
    "FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1",
    "FCIS_FEE_SPLIT_POLICY_RECORD_SCHEMA_V1",
    "FCIS_LP_DURATION_POLICY_FIELD_NAMES_V1",
    "FCIS_LP_DURATION_POLICY_RECORD_SCHEMA_V1",
    "FCIS_SETTLEMENT_CONTEXT_FIELD_NAMES_V1",
    "FCIS_SETTLEMENT_CONTEXT_RECORD_SCHEMA_V1",
    "FCIS_STEP_CONTEXT_FIELD_NAMES_V1",
    "FCIS_STEP_CONTEXT_RECORD_SCHEMA_V1",
)
