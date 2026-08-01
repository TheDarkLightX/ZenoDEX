"""Source-bound construction and projection for the closed M5 grammar.

No authority input selects a constructor or encoder. The sole admission profile
calls these exhaustive dispatch functions after the declarative interpreter has
admitted every child value.
"""

from __future__ import annotations

from typing import Callable, TypeGuard, TypeVar, cast

from ..state.fcis_committed_state_values import FCISCommittedStateV1
from ..state.owned_collections import OwnedEnumV1, OwnedMapV1
from ..state.state_snapshot_schema import StateRecordTagV1
from ..state.state_snapshot_values import (
    CommittedFeeAccumulatorStateV1,
    CommittedOracleStateV1,
    CommittedPerpsStateV1,
    CommittedPoolStateV1,
    CommittedVaultStateV1,
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
)
from .fcis_decision_values import (
    FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
    FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1,
    FCIS_DECISION_SCHEMA_ID_V1,
    FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1,
    AcceptanceReceiptClaimV1,
    AcceptClaimV1,
    CommittedFailureClaimV1,
    CommittedFailureReceiptClaimV1,
    ReceiptBindingClaimV1,
    RejectClaimV1,
    RejectionPathIndexPartV1,
    RejectionPathTextPartV1,
    RejectionReceiptClaimV1,
)
from .fcis_outbox_values import (
    FCIS_OUTBOX_PLAN_SCHEMA_ID_V1,
    OutboxPlanV1,
    OutboxRecordV1,
)
from .fcis_step_evaluation_values import FCISFeeAllocationV1
from .fcis_transition_budget import (
    FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1,
    TransitionBudgetV1,
)
from .fcis_transition_values import (
    FCIS_COMMIT_PLAN_SCHEMA_ID_V1,
    FCIS_DEX_PATCH_SCHEMA_ID_V1,
    FCIS_EFFECTS_SCHEMA_ID_V1,
    FCIS_REPLAY_UPDATE_SCHEMA_ID_V1,
    CanonicalDexPatchV1,
    CommitPlanV1,
    FeeAccumulatorWriteV1,
    NullifierRecordV1,
    OracleWriteV1,
    OwnedDexEffectsV1,
    PerpsWriteV1,
    ReplayUpdateV1,
    VaultWriteV1,
)
from .settlement_snapshots import OwnedSettlementV1, _project_owned_settlement

ProjectChildV1 = Callable[[object], object]
_ExactT = TypeVar("_ExactT")


def _is_exact_type(value: object, expected: type[_ExactT]) -> TypeGuard[_ExactT]:
    return type(value) is expected


FCIS_AUTHORITY_OWNED_TYPES_V1: tuple[type[object], ...] = (
    TransitionBudgetV1,
    BalanceWriteV1,
    PoolWriteV1,
    LPPositionValueV1,
    LPPositionWriteV1,
    NonceAdvanceV1,
    FCISFeeAllocationV1,
    FeeAccumulatorWriteV1,
    VaultWriteV1,
    OracleWriteV1,
    PerpsWriteV1,
    CanonicalDexPatchV1,
    OwnedDexEffectsV1,
    NullifierRecordV1,
    ReplayUpdateV1,
    CommitPlanV1,
    RejectionPathTextPartV1,
    RejectionPathIndexPartV1,
    ReceiptBindingClaimV1,
    AcceptanceReceiptClaimV1,
    RejectionReceiptClaimV1,
    CommittedFailureReceiptClaimV1,
    AcceptClaimV1,
    RejectClaimV1,
    CommittedFailureClaimV1,
    OutboxRecordV1,
    OutboxPlanV1,
    CommitBundleClaimV1,
)

FCIS_AUTHORITY_SCHEMA_EXPECTED_TYPES_V1: tuple[tuple[str, tuple[type[object], ...]], ...] = (
    (FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1, (TransitionBudgetV1,)),
    (FCIS_DEX_PATCH_SCHEMA_ID_V1, (CanonicalDexPatchV1,)),
    (FCIS_EFFECTS_SCHEMA_ID_V1, (OwnedDexEffectsV1,)),
    (FCIS_REPLAY_UPDATE_SCHEMA_ID_V1, (ReplayUpdateV1,)),
    (FCIS_COMMIT_PLAN_SCHEMA_ID_V1, (CommitPlanV1,)),
    (FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1, (AcceptanceReceiptClaimV1,)),
    (FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1, (RejectionReceiptClaimV1,)),
    (FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1, (CommittedFailureReceiptClaimV1,)),
    (
        FCIS_DECISION_SCHEMA_ID_V1,
        (AcceptClaimV1, RejectClaimV1, CommittedFailureClaimV1),
    ),
    (FCIS_OUTBOX_PLAN_SCHEMA_ID_V1, (OutboxPlanV1,)),
    (FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, (CommitBundleClaimV1,)),
)


def _field(
    values: tuple[tuple[str, object], ...],
    index: int,
    expected_name: str,
) -> object:
    if type(values) is not tuple or index >= len(values):
        raise ValueError("M5 record field registry drift")
    item = values[index]
    if type(item) is not tuple or len(item) != 2 or item[0] != expected_name:
        raise ValueError("M5 record field registry drift")
    return item[1]


def _construct_budget(values: tuple[tuple[str, object], ...]) -> TransitionBudgetV1:
    if len(values) != 13:
        raise ValueError("M5 budget field registry drift")
    return TransitionBudgetV1(
        cast(int, _field(values, 0, "max_canonical_input_bytes")),
        cast(int, _field(values, 1, "max_depth")),
        cast(int, _field(values, 2, "max_nodes")),
        cast(int, _field(values, 3, "max_intents")),
        cast(int, _field(values, 4, "max_state_reads")),
        cast(int, _field(values, 5, "max_context_reads")),
        cast(int, _field(values, 6, "max_patch_writes")),
        cast(int, _field(values, 7, "max_effects")),
        cast(int, _field(values, 8, "max_outbox_records")),
        cast(int, _field(values, 9, "max_candidates")),
        cast(int, _field(values, 10, "max_witness_bytes")),
        cast(int, _field(values, 11, "max_receipt_bytes")),
        cast(int, _field(values, 12, "max_integer_bits")),
    )


def _construct_balance_or_pool_write_record(
    tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    if tag is StateRecordTagV1.FCIS_BALANCE_WRITE and len(values) == 3:
        return BalanceWriteV1(
            cast(tuple[str, str], _field(values, 0, "key")),
            cast(int, _field(values, 1, "expected_old")),
            cast(int | None, _field(values, 2, "replacement")),
        )
    if tag is StateRecordTagV1.FCIS_POOL_WRITE and len(values) == 3:
        return PoolWriteV1(
            cast(str, _field(values, 0, "pool_id")),
            cast(CommittedPoolStateV1 | None, _field(values, 1, "expected")),
            cast(CommittedPoolStateV1 | None, _field(values, 2, "replacement")),
        )
    raise ValueError("unsupported balance or pool write record")


def _construct_lp_or_nonce_write_record(
    tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    if tag is StateRecordTagV1.FCIS_LP_POSITION_VALUE and len(values) == 5:
        return LPPositionValueV1(
            cast(int, _field(values, 0, "balance")),
            cast(int | None, _field(values, 1, "last_mint_timestamp")),
            cast(int | None, _field(values, 2, "last_remove_timestamp")),
            cast(int, _field(values, 3, "churn_tier")),
            cast(int | None, _field(values, 4, "last_churn_update_timestamp")),
        )
    if tag is StateRecordTagV1.FCIS_LP_POSITION_WRITE and len(values) == 3:
        return LPPositionWriteV1(
            cast(tuple[str, str], _field(values, 0, "key")),
            cast(LPPositionValueV1, _field(values, 1, "expected")),
            cast(LPPositionValueV1, _field(values, 2, "replacement")),
        )
    if tag is StateRecordTagV1.FCIS_NONCE_ADVANCE and len(values) == 3:
        return NonceAdvanceV1(
            cast(str, _field(values, 0, "pubkey")),
            cast(int, _field(values, 1, "expected_last")),
            cast(int, _field(values, 2, "new_last")),
        )
    raise ValueError("unsupported LP or nonce write record")


def _construct_fee_or_optional_write_record(
    tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    if tag is StateRecordTagV1.FCIS_FEE_ALLOCATION and len(values) == 4:
        return FCISFeeAllocationV1(
            cast(int, _field(values, 0, "buyback_amount")),
            cast(int, _field(values, 1, "treasury_amount")),
            cast(int, _field(values, 2, "rewards_amount")),
            cast(int, _field(values, 3, "dust_carried")),
        )
    if tag is StateRecordTagV1.FCIS_FEE_ACCUMULATOR_WRITE and len(values) == 2:
        return FeeAccumulatorWriteV1(
            cast(CommittedFeeAccumulatorStateV1, _field(values, 0, "expected")),
            cast(CommittedFeeAccumulatorStateV1, _field(values, 1, "replacement")),
        )
    if tag is StateRecordTagV1.FCIS_VAULT_WRITE and len(values) == 2:
        return VaultWriteV1(
            cast(CommittedVaultStateV1 | None, _field(values, 0, "expected")),
            cast(CommittedVaultStateV1 | None, _field(values, 1, "replacement")),
        )
    if tag is StateRecordTagV1.FCIS_ORACLE_WRITE and len(values) == 2:
        return OracleWriteV1(
            cast(CommittedOracleStateV1 | None, _field(values, 0, "expected")),
            cast(CommittedOracleStateV1 | None, _field(values, 1, "replacement")),
        )
    if tag is StateRecordTagV1.FCIS_PERPS_WRITE and len(values) == 2:
        return PerpsWriteV1(
            cast(CommittedPerpsStateV1 | None, _field(values, 0, "expected")),
            cast(CommittedPerpsStateV1 | None, _field(values, 1, "replacement")),
        )
    raise ValueError("unsupported fee or optional-module write record")


def _construct_write_record(
    tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    if tag in (StateRecordTagV1.FCIS_BALANCE_WRITE, StateRecordTagV1.FCIS_POOL_WRITE):
        return _construct_balance_or_pool_write_record(tag, values)
    if tag in (
        StateRecordTagV1.FCIS_LP_POSITION_VALUE,
        StateRecordTagV1.FCIS_LP_POSITION_WRITE,
        StateRecordTagV1.FCIS_NONCE_ADVANCE,
    ):
        return _construct_lp_or_nonce_write_record(tag, values)
    return _construct_fee_or_optional_write_record(tag, values)


def _construct_plan_record(
    tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    if tag is StateRecordTagV1.FCIS_DEX_PATCH and len(values) == 7:
        return CanonicalDexPatchV1(
            cast(tuple[BalanceWriteV1, ...], _field(values, 0, "balance_writes")),
            cast(tuple[PoolWriteV1, ...], _field(values, 1, "pool_writes")),
            cast(tuple[LPPositionWriteV1, ...], _field(values, 2, "lp_writes")),
            cast(FeeAccumulatorWriteV1 | None, _field(values, 3, "fee_accumulator_write")),
            cast(VaultWriteV1 | None, _field(values, 4, "vault_write")),
            cast(OracleWriteV1 | None, _field(values, 5, "oracle_write")),
            cast(PerpsWriteV1 | None, _field(values, 6, "perps_write")),
        )
    if tag is StateRecordTagV1.FCIS_EFFECTS and len(values) == 3:
        return OwnedDexEffectsV1(
            cast(OwnedSettlementV1, _field(values, 0, "settlement")),
            cast(int, _field(values, 1, "total_swap_fees")),
            cast(FCISFeeAllocationV1 | None, _field(values, 2, "fee_allocation")),
        )
    if tag is StateRecordTagV1.FCIS_NULLIFIER_RECORD and len(values) == 2:
        return NullifierRecordV1(
            cast(str, _field(values, 0, "pubkey")),
            cast(str, _field(values, 1, "intent_id")),
        )
    if tag is StateRecordTagV1.FCIS_REPLAY_UPDATE and len(values) == 2:
        return ReplayUpdateV1(
            cast(tuple[NonceAdvanceV1, ...], _field(values, 0, "nonce_advances")),
            cast(tuple[NullifierRecordV1, ...], _field(values, 1, "nullifiers")),
        )
    if tag is StateRecordTagV1.FCIS_COMMIT_PLAN and len(values) == 3:
        return CommitPlanV1(
            cast(CanonicalDexPatchV1, _field(values, 0, "patch")),
            cast(OwnedDexEffectsV1, _field(values, 1, "effects")),
            cast(ReplayUpdateV1, _field(values, 2, "replay")),
        )
    raise ValueError("unsupported M5 plan record")


def _construct_path_or_binding_record(
    tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    if tag is StateRecordTagV1.FCIS_REJECTION_PATH_TEXT_PART and len(values) == 1:
        return RejectionPathTextPartV1(cast(str, _field(values, 0, "text")))
    if tag is StateRecordTagV1.FCIS_REJECTION_PATH_INDEX_PART and len(values) == 1:
        return RejectionPathIndexPartV1(cast(int, _field(values, 0, "index")))
    if tag is not StateRecordTagV1.FCIS_RECEIPT_BINDING or len(values) not in (16, 18):
        raise ValueError("unsupported rejection path or receipt binding record")
    authority_normal_form_version = (
        cast(str | None, _field(values, 16, "authority_normal_form_version"))
        if len(values) == 18
        else None
    )
    authority_normal_form_root = (
        cast(str | None, _field(values, 17, "authority_normal_form_root"))
        if len(values) == 18
        else None
    )
    return ReceiptBindingClaimV1(
        cast(str, _field(values, 0, "algorithm_id")),
        cast(int, _field(values, 1, "algorithm_version")),
        cast(int, _field(values, 2, "schema_version")),
        cast(int, _field(values, 3, "codec_version")),
        cast(str, _field(values, 4, "execution_context_hash")),
        cast(str, _field(values, 5, "command_or_batch_root")),
        cast(str, _field(values, 6, "budget_hash")),
        cast(str, _field(values, 7, "pre_state_root")),
        cast(str, _field(values, 8, "next_state_root")),
        cast(int, _field(values, 9, "support_root_version")),
        cast(str, _field(values, 10, "support_root")),
        cast(str, _field(values, 11, "support_set_commitment")),
        cast(int, _field(values, 12, "snapshot_version")),
        cast(str, _field(values, 13, "snapshot_commitment")),
        cast(str, _field(values, 14, "patch_root")),
        cast(str, _field(values, 15, "commit_plan_root")),
        authority_normal_form_version,
        authority_normal_form_root,
    )


def _construct_receipt_record(
    tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    if tag in (
        StateRecordTagV1.FCIS_REJECTION_PATH_TEXT_PART,
        StateRecordTagV1.FCIS_REJECTION_PATH_INDEX_PART,
        StateRecordTagV1.FCIS_RECEIPT_BINDING,
    ):
        return _construct_path_or_binding_record(tag, values)
    if tag is StateRecordTagV1.FCIS_ACCEPTANCE_RECEIPT and len(values) == 1:
        return AcceptanceReceiptClaimV1(cast(ReceiptBindingClaimV1, _field(values, 0, "binding")))
    if tag is StateRecordTagV1.FCIS_REJECTION_RECEIPT and len(values) == 12:
        return RejectionReceiptClaimV1(
            cast(str, _field(values, 0, "algorithm_id")),
            cast(int, _field(values, 1, "algorithm_version")),
            cast(int, _field(values, 2, "schema_version")),
            cast(int, _field(values, 3, "codec_version")),
            cast(str | None, _field(values, 4, "command_or_batch_root")),
            cast(str | None, _field(values, 5, "budget_hash")),
            cast(str | None, _field(values, 6, "execution_context_hash")),
            cast(str | None, _field(values, 7, "pre_state_root")),
            cast(OwnedEnumV1, _field(values, 8, "phase")),
            cast(OwnedEnumV1, _field(values, 9, "code")),
            cast(
                tuple[RejectionPathTextPartV1 | RejectionPathIndexPartV1, ...],
                _field(values, 10, "path"),
            ),
            cast(str, _field(values, 11, "public_reason")),
        )
    if tag is StateRecordTagV1.FCIS_COMMITTED_FAILURE_RECEIPT and len(values) == 2:
        return CommittedFailureReceiptClaimV1(
            cast(ReceiptBindingClaimV1, _field(values, 0, "binding")),
            cast(OwnedEnumV1, _field(values, 1, "failure_code")),
        )
    raise ValueError("unsupported M5 receipt record")


def _construct_decision_variant_record(
    tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    if tag is StateRecordTagV1.FCIS_ACCEPT_DECISION and len(values) == 3:
        return AcceptClaimV1(
            cast(FCISCommittedStateV1, _field(values, 0, "next_state")),
            cast(CommitPlanV1, _field(values, 1, "commit_plan")),
            cast(AcceptanceReceiptClaimV1, _field(values, 2, "receipt")),
        )
    if tag is StateRecordTagV1.FCIS_REJECT_DECISION and len(values) == 1:
        return RejectClaimV1(cast(RejectionReceiptClaimV1, _field(values, 0, "receipt")))
    if tag is StateRecordTagV1.FCIS_COMMITTED_FAILURE_DECISION and len(values) == 3:
        return CommittedFailureClaimV1(
            cast(FCISCommittedStateV1, _field(values, 0, "next_state")),
            cast(CommitPlanV1, _field(values, 1, "commit_plan")),
            cast(CommittedFailureReceiptClaimV1, _field(values, 2, "receipt")),
        )
    raise ValueError("unsupported M5 decision record")


def _construct_outbox_or_bundle_record(
    tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    if tag is StateRecordTagV1.FCIS_OUTBOX_RECORD and len(values) == 5:
        return OutboxRecordV1(
            cast(int, _field(values, 0, "effect_index")),
            cast(OwnedEnumV1, _field(values, 1, "effect_kind")),
            cast(str, _field(values, 2, "effect_identity")),
            cast(OwnedMapV1[str, object], _field(values, 3, "payload")),
            cast(str, _field(values, 4, "idempotency_key")),
        )
    if tag is StateRecordTagV1.FCIS_OUTBOX_PLAN and len(values) in (1, 2):
        return OutboxPlanV1(
            cast(tuple[OutboxRecordV1, ...], _field(values, 0, "records")),
            cast(str | None, _field(values, 1, "authority_normal_form_root"))
            if len(values) == 2
            else None,
        )
    if tag is StateRecordTagV1.FCIS_COMMIT_BUNDLE and len(values) in (4, 5):
        return CommitBundleClaimV1(
            cast(str, _field(values, 0, "expected_pre_root")),
            cast(AcceptClaimV1 | CommittedFailureClaimV1, _field(values, 1, "decision")),
            cast(str, _field(values, 2, "receipt_root")),
            cast(OutboxPlanV1, _field(values, 3, "outbox_plan")),
            cast(str | None, _field(values, 4, "authority_normal_form_root"))
            if len(values) == 5
            else None,
        )
    raise ValueError("unsupported M5 outbox or bundle record")


def _construct_decision_record(
    tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    if tag in (
        StateRecordTagV1.FCIS_ACCEPT_DECISION,
        StateRecordTagV1.FCIS_REJECT_DECISION,
        StateRecordTagV1.FCIS_COMMITTED_FAILURE_DECISION,
    ):
        return _construct_decision_variant_record(tag, values)
    return _construct_outbox_or_bundle_record(tag, values)


def construct_fcis_authority_record_v1(
    record_tag: StateRecordTagV1,
    values: tuple[tuple[str, object], ...],
) -> object:
    """Construct exactly one registered M5 record from admitted children."""

    if type(record_tag) is not StateRecordTagV1:
        raise ValueError("M5 record tag type drift")
    tag = record_tag
    if tag is StateRecordTagV1.FCIS_TRANSITION_BUDGET:
        return _construct_budget(values)
    if tag in (
        StateRecordTagV1.FCIS_BALANCE_WRITE,
        StateRecordTagV1.FCIS_POOL_WRITE,
        StateRecordTagV1.FCIS_LP_POSITION_VALUE,
        StateRecordTagV1.FCIS_LP_POSITION_WRITE,
        StateRecordTagV1.FCIS_NONCE_ADVANCE,
        StateRecordTagV1.FCIS_FEE_ALLOCATION,
        StateRecordTagV1.FCIS_FEE_ACCUMULATOR_WRITE,
        StateRecordTagV1.FCIS_VAULT_WRITE,
        StateRecordTagV1.FCIS_ORACLE_WRITE,
        StateRecordTagV1.FCIS_PERPS_WRITE,
    ):
        return _construct_write_record(tag, values)
    if tag in (
        StateRecordTagV1.FCIS_DEX_PATCH,
        StateRecordTagV1.FCIS_EFFECTS,
        StateRecordTagV1.FCIS_NULLIFIER_RECORD,
        StateRecordTagV1.FCIS_REPLAY_UPDATE,
        StateRecordTagV1.FCIS_COMMIT_PLAN,
    ):
        return _construct_plan_record(tag, values)
    if tag in (
        StateRecordTagV1.FCIS_REJECTION_PATH_TEXT_PART,
        StateRecordTagV1.FCIS_REJECTION_PATH_INDEX_PART,
        StateRecordTagV1.FCIS_RECEIPT_BINDING,
        StateRecordTagV1.FCIS_ACCEPTANCE_RECEIPT,
        StateRecordTagV1.FCIS_REJECTION_RECEIPT,
        StateRecordTagV1.FCIS_COMMITTED_FAILURE_RECEIPT,
    ):
        return _construct_receipt_record(tag, values)
    return _construct_decision_record(tag, values)


def _project_budget(value: TransitionBudgetV1) -> dict[str, object]:
    return {
        "max_canonical_input_bytes": value.max_canonical_input_bytes,
        "max_depth": value.max_depth,
        "max_nodes": value.max_nodes,
        "max_intents": value.max_intents,
        "max_state_reads": value.max_state_reads,
        "max_context_reads": value.max_context_reads,
        "max_patch_writes": value.max_patch_writes,
        "max_effects": value.max_effects,
        "max_outbox_records": value.max_outbox_records,
        "max_candidates": value.max_candidates,
        "max_witness_bytes": value.max_witness_bytes,
        "max_receipt_bytes": value.max_receipt_bytes,
        "max_integer_bits": value.max_integer_bits,
    }


def _project_primary_write(value: object, child: ProjectChildV1) -> dict[str, object]:
    if _is_exact_type(value, BalanceWriteV1):
        return {
            "key": child(value.key),
            "expected_old": value.expected_old,
            "replacement": value.replacement,
        }
    if _is_exact_type(value, PoolWriteV1):
        return {
            "pool_id": value.pool_id,
            "expected": child(value.expected),
            "replacement": child(value.replacement),
        }
    if _is_exact_type(value, LPPositionValueV1):
        return {
            "balance": value.balance,
            "last_mint_timestamp": value.last_mint_timestamp,
            "last_remove_timestamp": value.last_remove_timestamp,
            "churn_tier": value.churn_tier,
            "last_churn_update_timestamp": value.last_churn_update_timestamp,
        }
    if _is_exact_type(value, LPPositionWriteV1):
        return {
            "key": child(value.key),
            "expected": child(value.expected),
            "replacement": child(value.replacement),
        }
    if _is_exact_type(value, NonceAdvanceV1):
        return {
            "pubkey": value.pubkey,
            "expected_last": value.expected_last,
            "new_last": value.new_last,
        }
    if _is_exact_type(value, FCISFeeAllocationV1):
        return {
            "buyback_amount": value.buyback_amount,
            "treasury_amount": value.treasury_amount,
            "rewards_amount": value.rewards_amount,
            "dust_carried": value.dust_carried,
        }
    raise TypeError("unsupported exact primary write projection")


def _project_optional_write(value: object, child: ProjectChildV1) -> dict[str, object]:
    if _is_exact_type(value, FeeAccumulatorWriteV1):
        return {
            "expected": child(value.expected),
            "replacement": child(value.replacement),
        }
    if _is_exact_type(value, VaultWriteV1):
        return {
            "expected": child(value.expected),
            "replacement": child(value.replacement),
        }
    if _is_exact_type(value, OracleWriteV1):
        return {
            "expected": child(value.expected),
            "replacement": child(value.replacement),
        }
    if _is_exact_type(value, PerpsWriteV1):
        return {
            "expected": child(value.expected),
            "replacement": child(value.replacement),
        }
    raise TypeError("unsupported exact optional write projection")


def _project_write(value: object, child: ProjectChildV1) -> dict[str, object]:
    if type(value) in (
        BalanceWriteV1,
        PoolWriteV1,
        LPPositionValueV1,
        LPPositionWriteV1,
        NonceAdvanceV1,
        FCISFeeAllocationV1,
    ):
        return _project_primary_write(value, child)
    return _project_optional_write(value, child)


def _project_plan_value(value: object, child: ProjectChildV1) -> dict[str, object]:
    if _is_exact_type(value, CanonicalDexPatchV1):
        return {
            "balance_writes": child(value.balance_writes),
            "pool_writes": child(value.pool_writes),
            "lp_writes": child(value.lp_writes),
            "fee_accumulator_write": child(value.fee_accumulator_write),
            "vault_write": child(value.vault_write),
            "oracle_write": child(value.oracle_write),
            "perps_write": child(value.perps_write),
        }
    if _is_exact_type(value, OwnedDexEffectsV1):
        return {
            "settlement": _project_owned_settlement(value.settlement),
            "total_swap_fees": value.total_swap_fees,
            "fee_allocation": child(value.fee_allocation),
        }
    if _is_exact_type(value, NullifierRecordV1):
        return {"pubkey": value.pubkey, "intent_id": value.intent_id}
    if _is_exact_type(value, ReplayUpdateV1):
        return {
            "nonce_advances": child(value.nonce_advances),
            "nullifiers": child(value.nullifiers),
        }
    if _is_exact_type(value, CommitPlanV1):
        return {
            "patch": child(value.patch),
            "effects": child(value.effects),
            "replay": child(value.replay),
        }
    raise TypeError("unsupported exact M5 plan projection")


def _project_receipt_value(value: object, child: ProjectChildV1) -> dict[str, object]:
    if _is_exact_type(value, RejectionPathTextPartV1):
        return {"text": value.text}
    if _is_exact_type(value, RejectionPathIndexPartV1):
        return {"index": value.index}
    if _is_exact_type(value, ReceiptBindingClaimV1):
        return {
            "algorithm_id": value.algorithm_id,
            "algorithm_version": value.algorithm_version,
            "schema_version": value.schema_version,
            "codec_version": value.codec_version,
            "execution_context_hash": value.execution_context_hash,
            "command_or_batch_root": value.command_or_batch_root,
            "budget_hash": value.budget_hash,
            "pre_state_root": value.pre_state_root,
            "next_state_root": value.next_state_root,
            "support_root_version": value.support_root_version,
            "support_root": value.support_root,
            "support_set_commitment": value.support_set_commitment,
            "snapshot_version": value.snapshot_version,
            "snapshot_commitment": value.snapshot_commitment,
            "patch_root": value.patch_root,
            "commit_plan_root": value.commit_plan_root,
            "authority_normal_form_version": value.authority_normal_form_version,
            "authority_normal_form_root": value.authority_normal_form_root,
        }
    if _is_exact_type(value, AcceptanceReceiptClaimV1):
        return {"binding": child(value.binding)}
    if _is_exact_type(value, RejectionReceiptClaimV1):
        return {
            "algorithm_id": value.algorithm_id,
            "algorithm_version": value.algorithm_version,
            "schema_version": value.schema_version,
            "codec_version": value.codec_version,
            "command_or_batch_root": value.command_or_batch_root,
            "budget_hash": value.budget_hash,
            "execution_context_hash": value.execution_context_hash,
            "pre_state_root": value.pre_state_root,
            "phase": child(value.phase),
            "code": child(value.code),
            "path": child(value.path),
            "public_reason": value.public_reason,
        }
    if _is_exact_type(value, CommittedFailureReceiptClaimV1):
        return {
            "binding": child(value.binding),
            "failure_code": child(value.failure_code),
        }
    raise TypeError("unsupported exact M5 receipt projection")


def _project_decision_or_bundle_value(
    value: object,
    child: ProjectChildV1,
) -> dict[str, object]:
    if _is_exact_type(value, AcceptClaimV1):
        return {
            "next_state": child(value.next_state),
            "commit_plan": child(value.commit_plan),
            "receipt": child(value.receipt),
        }
    if _is_exact_type(value, RejectClaimV1):
        return {"receipt": child(value.receipt)}
    if _is_exact_type(value, CommittedFailureClaimV1):
        return {
            "next_state": child(value.next_state),
            "commit_plan": child(value.commit_plan),
            "receipt": child(value.receipt),
        }
    if _is_exact_type(value, OutboxRecordV1):
        return {
            "effect_index": value.effect_index,
            "effect_kind": child(value.effect_kind),
            "effect_identity": value.effect_identity,
            "payload": child(value.payload),
            "idempotency_key": value.idempotency_key,
        }
    if _is_exact_type(value, OutboxPlanV1):
        return {
            "records": child(value.records),
            "authority_normal_form_root": value.authority_normal_form_root,
        }
    if _is_exact_type(value, CommitBundleClaimV1):
        return {
            "expected_pre_root": value.expected_pre_root,
            "decision": child(value.decision),
            "receipt_root": value.receipt_root,
            "outbox_plan": child(value.outbox_plan),
            "authority_normal_form_root": value.authority_normal_form_root,
        }
    raise TypeError("unsupported exact M5 decision or bundle projection")


def project_fcis_authority_v1(value: object, child: ProjectChildV1) -> object:
    """Project one exact M5 value into its declared canonical JSON tree."""

    if _is_exact_type(value, TransitionBudgetV1):
        return _project_budget(value)
    if type(value) in (
        BalanceWriteV1,
        PoolWriteV1,
        LPPositionValueV1,
        LPPositionWriteV1,
        NonceAdvanceV1,
        FCISFeeAllocationV1,
        FeeAccumulatorWriteV1,
        VaultWriteV1,
        OracleWriteV1,
        PerpsWriteV1,
    ):
        return _project_write(value, child)
    if type(value) in (
        CanonicalDexPatchV1,
        OwnedDexEffectsV1,
        NullifierRecordV1,
        ReplayUpdateV1,
        CommitPlanV1,
    ):
        return _project_plan_value(value, child)
    if type(value) in (
        RejectionPathTextPartV1,
        RejectionPathIndexPartV1,
        ReceiptBindingClaimV1,
        AcceptanceReceiptClaimV1,
        RejectionReceiptClaimV1,
        CommittedFailureReceiptClaimV1,
    ):
        return _project_receipt_value(value, child)
    if type(value) in (
        AcceptClaimV1,
        RejectClaimV1,
        CommittedFailureClaimV1,
        OutboxRecordV1,
        OutboxPlanV1,
        CommitBundleClaimV1,
    ):
        return _project_decision_or_bundle_value(value, child)
    raise TypeError("unsupported exact M5 authority projection")


__all__ = (
    "FCIS_AUTHORITY_OWNED_TYPES_V1",
    "FCIS_AUTHORITY_SCHEMA_EXPECTED_TYPES_V1",
    "construct_fcis_authority_record_v1",
    "project_fcis_authority_v1",
)
