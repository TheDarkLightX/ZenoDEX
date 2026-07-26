"""Closed declarative grammar for the unmounted FCIS M5 authority graph.

This module contains schema data and exact type registrations only. The sole
state admission profile owns executable construction and canonical encoding.
"""

from __future__ import annotations

from ..state.intent_schema import INTENT_ID_V1, PUBKEY_V1
from ..state.owned_json import JSON_OBJECT_SCHEMA_V1
from ..state.snapshot_combinators import (
    DeclaredFieldV1,
    EnumRegistrationV1,
    ExactEnum,
    ExactInt,
    ExactString,
    OptionalValue,
    RecordOf,
    RecordRegistrationV1,
    RecordUnionOf,
    SchemaRegistrationV1,
    SchemaV1,
    SequenceOf,
    SequenceSourceKind,
    StringRuleV1,
)
from ..state.state_snapshot_schema import (
    BALANCE_KEY_SCHEMA_V1,
    FCIS_COMMITTED_STATE_SCHEMA_V1,
    FEE_ACCUMULATOR_SCHEMA_V1,
    LP_KEY_SCHEMA_V1,
    ORACLE_RECORD_SCHEMA_V1,
    PERPS_RECORD_SCHEMA_V1,
    POOL_ID_TEXT,
    POOL_SCHEMA_V1,
    VAULT_RECORD_SCHEMA_V1,
    StateEnumTagV1,
    StateRecordTagV1,
)
from ..state.state_snapshot_values import (
    DEX_LP_AMOUNT_MAX,
    MAX_BALANCES_V1,
    MAX_LP_ENTRIES_V1,
    MAX_NONCES_V1,
    MAX_POOLS_V1,
    MAX_U32_V1,
)
from ..state.state_transitions import (
    BalanceWriteV1,
    LPPositionValueV1,
    LPPositionWriteV1,
    NonceAdvanceV1,
    PoolWriteV1,
)
from .fcis_commit_bundle_values import (
    FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1,
    CommitBundleClaimV1,
    CommitBundleSourceV1,
)
from .fcis_decision_values import (
    FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
    FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1,
    FCIS_DECISION_SCHEMA_ID_V1,
    FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1,
    AcceptanceReceiptClaimV1,
    AcceptanceReceiptSourceV1,
    AcceptClaimV1,
    AcceptSourceV1,
    CommittedFailureClaimV1,
    CommittedFailureReceiptClaimV1,
    CommittedFailureReceiptSourceV1,
    CommittedFailureSourceV1,
    FCISCommittedFailureCodeV1,
    FCISRejectCodeV1,
    ReceiptBindingClaimV1,
    ReceiptBindingSourceV1,
    RejectClaimV1,
    RejectionPathIndexPartSourceV1,
    RejectionPathIndexPartV1,
    RejectionPathTextPartSourceV1,
    RejectionPathTextPartV1,
    RejectionReceiptClaimV1,
    RejectionReceiptSourceV1,
    RejectSourceV1,
)
from .fcis_outbox_values import (
    FCIS_OUTBOX_PLAN_SCHEMA_ID_V1,
    MAX_FCIS_OUTBOX_RECORDS_V1,
    OutboxEffectKindV1,
    OutboxPlanSourceV1,
    OutboxPlanV1,
    OutboxRecordSourceV1,
    OutboxRecordV1,
)
from .fcis_step_evaluation_values import (
    FCISFeeAllocationV1,
    FCISStepEvaluationPhaseV1,
)
from .fcis_transition_budget import (
    FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1,
    MAX_FCIS_CANDIDATES_V1,
    MAX_FCIS_INTENTS_V1,
    TransitionBudgetSourceV1,
    TransitionBudgetV1,
)
from .fcis_transition_values import (
    FCIS_COMMIT_PLAN_SCHEMA_ID_V1,
    FCIS_DEX_PATCH_SCHEMA_ID_V1,
    FCIS_EFFECTS_SCHEMA_ID_V1,
    FCIS_REPLAY_UPDATE_SCHEMA_ID_V1,
    MAX_FCIS_NULLIFIERS_V1,
    BalanceWriteSourceV1,
    CanonicalDexPatchSourceV1,
    CanonicalDexPatchV1,
    CommitPlanSourceV1,
    CommitPlanV1,
    FCISFeeAllocationSourceV1,
    FeeAccumulatorWriteSourceV1,
    FeeAccumulatorWriteV1,
    LPPositionValueSourceV1,
    LPPositionWriteSourceV1,
    NonceAdvanceSourceV1,
    NullifierRecordSourceV1,
    NullifierRecordV1,
    OracleWriteSourceV1,
    OracleWriteV1,
    OwnedDexEffectsSourceV1,
    OwnedDexEffectsV1,
    PerpsWriteSourceV1,
    PerpsWriteV1,
    PoolWriteSourceV1,
    ReplayUpdateSourceV1,
    ReplayUpdateV1,
    VaultWriteSourceV1,
    VaultWriteV1,
)
from .settlement_schema import SETTLEMENT_SCHEMA_V1

MAX_FCIS_SCALAR_V1 = (1 << 256) - 1
MAX_FCIS_PATH_PARTS_V1 = 64
MAX_FCIS_TEXT_CHARACTERS_V1 = 4_096
MAX_FCIS_TEXT_UTF8_BYTES_V1 = 16_384


def _field(name: str, schema: SchemaV1) -> DeclaredFieldV1:
    return DeclaredFieldV1(name, schema)


NONNEGATIVE_V1 = ExactInt(0, MAX_FCIS_SCALAR_V1)
POSITIVE_V1 = ExactInt(1, MAX_FCIS_SCALAR_V1)
U32_V1 = ExactInt(0, MAX_U32_V1)
POSITIVE_U32_V1 = ExactInt(1, MAX_U32_V1)
DIGEST_V1 = ExactString(
    StringRuleV1.LOWERCASE_0X_HEX,
    66,
    exact_utf8_bytes=66,
    max_characters=66,
)
NONEMPTY_TEXT_V1 = ExactString(
    StringRuleV1.NON_EMPTY,
    MAX_FCIS_TEXT_UTF8_BYTES_V1,
    max_characters=MAX_FCIS_TEXT_CHARACTERS_V1,
)
OPTIONAL_DIGEST_V1 = OptionalValue(DIGEST_V1)
OPTIONAL_POSITIVE_V1 = OptionalValue(POSITIVE_V1)

TRANSITION_BUDGET_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_TRANSITION_BUDGET,
    (
        _field("max_canonical_input_bytes", POSITIVE_V1),
        _field("max_depth", POSITIVE_V1),
        _field("max_nodes", POSITIVE_V1),
        _field("max_intents", ExactInt(1, MAX_FCIS_INTENTS_V1)),
        _field("max_state_reads", POSITIVE_V1),
        _field("max_context_reads", POSITIVE_V1),
        _field("max_patch_writes", POSITIVE_V1),
        _field("max_effects", POSITIVE_V1),
        _field("max_outbox_records", ExactInt(1, MAX_FCIS_OUTBOX_RECORDS_V1)),
        _field("max_candidates", ExactInt(1, MAX_FCIS_CANDIDATES_V1)),
        _field("max_witness_bytes", POSITIVE_V1),
        _field("max_receipt_bytes", POSITIVE_V1),
        _field("max_integer_bits", POSITIVE_V1),
    ),
)

BALANCE_WRITE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_BALANCE_WRITE,
    (
        _field("key", BALANCE_KEY_SCHEMA_V1),
        _field("expected_old", NONNEGATIVE_V1),
        _field("replacement", OPTIONAL_POSITIVE_V1),
    ),
)
POOL_WRITE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_POOL_WRITE,
    (
        _field("pool_id", POOL_ID_TEXT),
        _field("expected", OptionalValue(POOL_SCHEMA_V1)),
        _field("replacement", OptionalValue(POOL_SCHEMA_V1)),
    ),
)
LP_POSITION_VALUE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_LP_POSITION_VALUE,
    (
        _field("balance", ExactInt(0, DEX_LP_AMOUNT_MAX)),
        _field("last_mint_timestamp", OptionalValue(NONNEGATIVE_V1)),
        _field("last_remove_timestamp", OptionalValue(NONNEGATIVE_V1)),
        _field("churn_tier", NONNEGATIVE_V1),
        _field("last_churn_update_timestamp", OptionalValue(NONNEGATIVE_V1)),
    ),
)
LP_POSITION_WRITE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_LP_POSITION_WRITE,
    (
        _field("key", LP_KEY_SCHEMA_V1),
        _field("expected", LP_POSITION_VALUE_SCHEMA_V1),
        _field("replacement", LP_POSITION_VALUE_SCHEMA_V1),
    ),
)
NONCE_ADVANCE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_NONCE_ADVANCE,
    (
        _field("pubkey", PUBKEY_V1),
        _field("expected_last", U32_V1),
        _field("new_last", POSITIVE_U32_V1),
    ),
)
FEE_ALLOCATION_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_FEE_ALLOCATION,
    (
        _field("buyback_amount", NONNEGATIVE_V1),
        _field("treasury_amount", NONNEGATIVE_V1),
        _field("rewards_amount", NONNEGATIVE_V1),
        _field("dust_carried", NONNEGATIVE_V1),
    ),
)
FEE_ACCUMULATOR_WRITE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_FEE_ACCUMULATOR_WRITE,
    (
        _field("expected", FEE_ACCUMULATOR_SCHEMA_V1),
        _field("replacement", FEE_ACCUMULATOR_SCHEMA_V1),
    ),
)
VAULT_WRITE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_VAULT_WRITE,
    (
        _field("expected", OptionalValue(VAULT_RECORD_SCHEMA_V1)),
        _field("replacement", OptionalValue(VAULT_RECORD_SCHEMA_V1)),
    ),
)
ORACLE_WRITE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_ORACLE_WRITE,
    (
        _field("expected", OptionalValue(ORACLE_RECORD_SCHEMA_V1)),
        _field("replacement", OptionalValue(ORACLE_RECORD_SCHEMA_V1)),
    ),
)
PERPS_WRITE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_PERPS_WRITE,
    (
        _field("expected", OptionalValue(PERPS_RECORD_SCHEMA_V1)),
        _field("replacement", OptionalValue(PERPS_RECORD_SCHEMA_V1)),
    ),
)

DEX_PATCH_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_DEX_PATCH,
    (
        _field(
            "balance_writes",
            SequenceOf(
                (SequenceSourceKind.EXACT_TUPLE,), BALANCE_WRITE_SCHEMA_V1, 0, MAX_BALANCES_V1
            ),
        ),
        _field(
            "pool_writes",
            SequenceOf((SequenceSourceKind.EXACT_TUPLE,), POOL_WRITE_SCHEMA_V1, 0, MAX_POOLS_V1),
        ),
        _field(
            "lp_writes",
            SequenceOf(
                (SequenceSourceKind.EXACT_TUPLE,), LP_POSITION_WRITE_SCHEMA_V1, 0, MAX_LP_ENTRIES_V1
            ),
        ),
        _field("fee_accumulator_write", OptionalValue(FEE_ACCUMULATOR_WRITE_SCHEMA_V1)),
        _field("vault_write", OptionalValue(VAULT_WRITE_SCHEMA_V1)),
        _field("oracle_write", OptionalValue(ORACLE_WRITE_SCHEMA_V1)),
        _field("perps_write", OptionalValue(PERPS_WRITE_SCHEMA_V1)),
    ),
)
EFFECTS_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_EFFECTS,
    (
        _field("settlement", SETTLEMENT_SCHEMA_V1),
        _field("total_swap_fees", NONNEGATIVE_V1),
        _field("fee_allocation", OptionalValue(FEE_ALLOCATION_SCHEMA_V1)),
    ),
)
NULLIFIER_RECORD_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_NULLIFIER_RECORD,
    (_field("pubkey", PUBKEY_V1), _field("intent_id", INTENT_ID_V1)),
)
REPLAY_UPDATE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_REPLAY_UPDATE,
    (
        _field(
            "nonce_advances",
            SequenceOf(
                (SequenceSourceKind.EXACT_TUPLE,), NONCE_ADVANCE_SCHEMA_V1, 0, MAX_NONCES_V1
            ),
        ),
        _field(
            "nullifiers",
            SequenceOf(
                (SequenceSourceKind.EXACT_TUPLE,),
                NULLIFIER_RECORD_SCHEMA_V1,
                0,
                MAX_FCIS_NULLIFIERS_V1,
            ),
        ),
    ),
)
COMMIT_PLAN_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_COMMIT_PLAN,
    (
        _field("patch", DEX_PATCH_SCHEMA_V1),
        _field("effects", EFFECTS_SCHEMA_V1),
        _field("replay", REPLAY_UPDATE_SCHEMA_V1),
    ),
)

REJECTION_PATH_TEXT_PART_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_REJECTION_PATH_TEXT_PART,
    (_field("text", NONEMPTY_TEXT_V1),),
)
REJECTION_PATH_INDEX_PART_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_REJECTION_PATH_INDEX_PART,
    (_field("index", NONNEGATIVE_V1),),
)
REJECTION_PATH_PART_SCHEMA_V1 = RecordUnionOf(
    (REJECTION_PATH_TEXT_PART_SCHEMA_V1, REJECTION_PATH_INDEX_PART_SCHEMA_V1)
)
RECEIPT_BINDING_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_RECEIPT_BINDING,
    (
        _field("algorithm_id", NONEMPTY_TEXT_V1),
        _field("algorithm_version", POSITIVE_U32_V1),
        _field("schema_version", POSITIVE_U32_V1),
        _field("codec_version", POSITIVE_U32_V1),
        _field("execution_context_hash", DIGEST_V1),
        _field("command_or_batch_root", DIGEST_V1),
        _field("budget_hash", DIGEST_V1),
        _field("pre_state_root", DIGEST_V1),
        _field("next_state_root", DIGEST_V1),
        _field("support_root_version", POSITIVE_U32_V1),
        _field("support_root", DIGEST_V1),
        _field("support_set_commitment", DIGEST_V1),
        _field("snapshot_version", POSITIVE_U32_V1),
        _field("snapshot_commitment", DIGEST_V1),
        _field("patch_root", DIGEST_V1),
        _field("commit_plan_root", DIGEST_V1),
    ),
)
ACCEPTANCE_RECEIPT_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_ACCEPTANCE_RECEIPT,
    (_field("binding", RECEIPT_BINDING_SCHEMA_V1),),
)
REJECTION_RECEIPT_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_REJECTION_RECEIPT,
    (
        _field("algorithm_id", NONEMPTY_TEXT_V1),
        _field("algorithm_version", POSITIVE_U32_V1),
        _field("schema_version", POSITIVE_U32_V1),
        _field("codec_version", POSITIVE_U32_V1),
        _field("command_or_batch_root", OPTIONAL_DIGEST_V1),
        _field("budget_hash", OPTIONAL_DIGEST_V1),
        _field("execution_context_hash", OPTIONAL_DIGEST_V1),
        _field("pre_state_root", OPTIONAL_DIGEST_V1),
        _field("phase", ExactEnum(StateEnumTagV1.FCIS_REJECTION_PHASE)),
        _field("code", ExactEnum(StateEnumTagV1.FCIS_REJECTION_CODE)),
        _field(
            "path",
            SequenceOf(
                (SequenceSourceKind.EXACT_TUPLE,),
                REJECTION_PATH_PART_SCHEMA_V1,
                0,
                MAX_FCIS_PATH_PARTS_V1,
            ),
        ),
        _field("public_reason", NONEMPTY_TEXT_V1),
    ),
)
COMMITTED_FAILURE_RECEIPT_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_COMMITTED_FAILURE_RECEIPT,
    (
        _field("binding", RECEIPT_BINDING_SCHEMA_V1),
        _field(
            "failure_code",
            ExactEnum(StateEnumTagV1.FCIS_COMMITTED_FAILURE_CODE),
        ),
    ),
)
ACCEPT_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_ACCEPT_DECISION,
    (
        _field("next_state", FCIS_COMMITTED_STATE_SCHEMA_V1),
        _field("commit_plan", COMMIT_PLAN_SCHEMA_V1),
        _field("receipt", ACCEPTANCE_RECEIPT_SCHEMA_V1),
    ),
)
REJECT_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_REJECT_DECISION,
    (_field("receipt", REJECTION_RECEIPT_SCHEMA_V1),),
)
COMMITTED_FAILURE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_COMMITTED_FAILURE_DECISION,
    (
        _field("next_state", FCIS_COMMITTED_STATE_SCHEMA_V1),
        _field("commit_plan", COMMIT_PLAN_SCHEMA_V1),
        _field("receipt", COMMITTED_FAILURE_RECEIPT_SCHEMA_V1),
    ),
)
DECISION_SCHEMA_V1 = RecordUnionOf(
    (ACCEPT_SCHEMA_V1, REJECT_SCHEMA_V1, COMMITTED_FAILURE_SCHEMA_V1)
)
COMMITTABLE_DECISION_SCHEMA_V1 = RecordUnionOf((ACCEPT_SCHEMA_V1, COMMITTED_FAILURE_SCHEMA_V1))

OUTBOX_RECORD_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_OUTBOX_RECORD,
    (
        _field("effect_index", ExactInt(0, MAX_FCIS_OUTBOX_RECORDS_V1 - 1)),
        _field("effect_kind", ExactEnum(StateEnumTagV1.OUTBOX_EFFECT_KIND)),
        _field("effect_identity", DIGEST_V1),
        _field("payload", JSON_OBJECT_SCHEMA_V1),
        _field("idempotency_key", DIGEST_V1),
    ),
)
OUTBOX_PLAN_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_OUTBOX_PLAN,
    (
        _field(
            "records",
            SequenceOf(
                (SequenceSourceKind.EXACT_TUPLE,),
                OUTBOX_RECORD_SCHEMA_V1,
                0,
                MAX_FCIS_OUTBOX_RECORDS_V1,
            ),
        ),
    ),
)
COMMIT_BUNDLE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FCIS_COMMIT_BUNDLE,
    (
        _field("expected_pre_root", DIGEST_V1),
        _field("decision", COMMITTABLE_DECISION_SCHEMA_V1),
        _field("receipt_root", DIGEST_V1),
        _field("outbox_plan", OUTBOX_PLAN_SCHEMA_V1),
    ),
)

FCIS_AUTHORITY_ENUM_REGISTRATIONS_V1 = (
    EnumRegistrationV1(StateEnumTagV1.OUTBOX_EFFECT_KIND, OutboxEffectKindV1),
    EnumRegistrationV1(
        StateEnumTagV1.FCIS_REJECTION_PHASE,
        FCISStepEvaluationPhaseV1,
    ),
    EnumRegistrationV1(StateEnumTagV1.FCIS_REJECTION_CODE, FCISRejectCodeV1),
    EnumRegistrationV1(
        StateEnumTagV1.FCIS_COMMITTED_FAILURE_CODE,
        FCISCommittedFailureCodeV1,
    ),
)
FCIS_AUTHORITY_RECORD_REGISTRATIONS_V1 = (
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_TRANSITION_BUDGET, TransitionBudgetSourceV1, TransitionBudgetV1
    ),
    RecordRegistrationV1(StateRecordTagV1.FCIS_BALANCE_WRITE, BalanceWriteSourceV1, BalanceWriteV1),
    RecordRegistrationV1(StateRecordTagV1.FCIS_POOL_WRITE, PoolWriteSourceV1, PoolWriteV1),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_LP_POSITION_VALUE, LPPositionValueSourceV1, LPPositionValueV1
    ),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_LP_POSITION_WRITE, LPPositionWriteSourceV1, LPPositionWriteV1
    ),
    RecordRegistrationV1(StateRecordTagV1.FCIS_NONCE_ADVANCE, NonceAdvanceSourceV1, NonceAdvanceV1),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_FEE_ALLOCATION, FCISFeeAllocationSourceV1, FCISFeeAllocationV1
    ),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_FEE_ACCUMULATOR_WRITE,
        FeeAccumulatorWriteSourceV1,
        FeeAccumulatorWriteV1,
    ),
    RecordRegistrationV1(StateRecordTagV1.FCIS_VAULT_WRITE, VaultWriteSourceV1, VaultWriteV1),
    RecordRegistrationV1(StateRecordTagV1.FCIS_ORACLE_WRITE, OracleWriteSourceV1, OracleWriteV1),
    RecordRegistrationV1(StateRecordTagV1.FCIS_PERPS_WRITE, PerpsWriteSourceV1, PerpsWriteV1),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_DEX_PATCH, CanonicalDexPatchSourceV1, CanonicalDexPatchV1
    ),
    RecordRegistrationV1(StateRecordTagV1.FCIS_EFFECTS, OwnedDexEffectsSourceV1, OwnedDexEffectsV1),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_NULLIFIER_RECORD, NullifierRecordSourceV1, NullifierRecordV1
    ),
    RecordRegistrationV1(StateRecordTagV1.FCIS_REPLAY_UPDATE, ReplayUpdateSourceV1, ReplayUpdateV1),
    RecordRegistrationV1(StateRecordTagV1.FCIS_COMMIT_PLAN, CommitPlanSourceV1, CommitPlanV1),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_REJECTION_PATH_TEXT_PART,
        RejectionPathTextPartSourceV1,
        RejectionPathTextPartV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_REJECTION_PATH_INDEX_PART,
        RejectionPathIndexPartSourceV1,
        RejectionPathIndexPartV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_RECEIPT_BINDING, ReceiptBindingSourceV1, ReceiptBindingClaimV1
    ),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_ACCEPTANCE_RECEIPT,
        AcceptanceReceiptSourceV1,
        AcceptanceReceiptClaimV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_REJECTION_RECEIPT, RejectionReceiptSourceV1, RejectionReceiptClaimV1
    ),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_COMMITTED_FAILURE_RECEIPT,
        CommittedFailureReceiptSourceV1,
        CommittedFailureReceiptClaimV1,
    ),
    RecordRegistrationV1(StateRecordTagV1.FCIS_ACCEPT_DECISION, AcceptSourceV1, AcceptClaimV1),
    RecordRegistrationV1(StateRecordTagV1.FCIS_REJECT_DECISION, RejectSourceV1, RejectClaimV1),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_COMMITTED_FAILURE_DECISION,
        CommittedFailureSourceV1,
        CommittedFailureClaimV1,
    ),
    RecordRegistrationV1(StateRecordTagV1.FCIS_OUTBOX_RECORD, OutboxRecordSourceV1, OutboxRecordV1),
    RecordRegistrationV1(StateRecordTagV1.FCIS_OUTBOX_PLAN, OutboxPlanSourceV1, OutboxPlanV1),
    RecordRegistrationV1(
        StateRecordTagV1.FCIS_COMMIT_BUNDLE, CommitBundleSourceV1, CommitBundleClaimV1
    ),
)
FCIS_AUTHORITY_SCHEMA_REGISTRATIONS_V1 = (
    SchemaRegistrationV1(FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1, TRANSITION_BUDGET_SCHEMA_V1),
    SchemaRegistrationV1(FCIS_DEX_PATCH_SCHEMA_ID_V1, DEX_PATCH_SCHEMA_V1),
    SchemaRegistrationV1(FCIS_EFFECTS_SCHEMA_ID_V1, EFFECTS_SCHEMA_V1),
    SchemaRegistrationV1(FCIS_REPLAY_UPDATE_SCHEMA_ID_V1, REPLAY_UPDATE_SCHEMA_V1),
    SchemaRegistrationV1(FCIS_COMMIT_PLAN_SCHEMA_ID_V1, COMMIT_PLAN_SCHEMA_V1),
    SchemaRegistrationV1(FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1, ACCEPTANCE_RECEIPT_SCHEMA_V1),
    SchemaRegistrationV1(FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1, REJECTION_RECEIPT_SCHEMA_V1),
    SchemaRegistrationV1(
        FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1, COMMITTED_FAILURE_RECEIPT_SCHEMA_V1
    ),
    SchemaRegistrationV1(FCIS_DECISION_SCHEMA_ID_V1, DECISION_SCHEMA_V1),
    SchemaRegistrationV1(FCIS_OUTBOX_PLAN_SCHEMA_ID_V1, OUTBOX_PLAN_SCHEMA_V1),
    SchemaRegistrationV1(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, COMMIT_BUNDLE_SCHEMA_V1),
)
FCIS_AUTHORITY_SCHEMA_IDS_V1 = tuple(
    registration.schema_id for registration in FCIS_AUTHORITY_SCHEMA_REGISTRATIONS_V1
)

__all__ = (
    "FCIS_AUTHORITY_ENUM_REGISTRATIONS_V1",
    "FCIS_AUTHORITY_RECORD_REGISTRATIONS_V1",
    "FCIS_AUTHORITY_SCHEMA_IDS_V1",
    "FCIS_AUTHORITY_SCHEMA_REGISTRATIONS_V1",
)
