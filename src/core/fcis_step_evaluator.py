"""Pure, unmounted FCIS spot-step evaluation over exact committed values.

The evaluator exists to prove composition before the M5 authority switch.  It
returns an exact local candidate plus canonical differential evidence.  The
legacy settlement and intent graph remains a temporary PR #478 input, so this
module cannot authorize a shell commit.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import cast, final

from ..state.canonical import domain_sep_bytes, sha256_hex
from ..state.committed_dex_snapshot import (
    canonical_committed_state_root_binding_v1,
)
from ..state.fcis_committed_state_admission import admit_fcis_committed_state_v1
from ..state.fcis_committed_state_values import FCISCommittedStateV1
from ..state.fcis_execution_context import (
    admit_fcis_settlement_execution_context_v1,
    admit_fcis_step_execution_context_v1,
)
from ..state.fcis_execution_context_codec import encode_fcis_execution_context_v1
from ..state.fcis_execution_context_values import (
    FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
    FCISSettlementExecutionContextV1,
    FCISStepExecutionContextV1,
    settlement_mode_label_v1,
)
from ..state.intent_snapshots import (
    OwnedIntentV1,
    admit_intent_batch,
)
from ..state.intents import Intent
from ..state.lp_duration_policy_context import admit_optional_lp_duration_policy_v1
from ..state.lp_duration_policy_values import LPDurationRiskPolicyV1
from ..state.owned_collections import OwnedMapV1
from ..state.snapshot_combinators import AdmitOk, AdmitReject, format_admit_path
from ..state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedPoolStateV1,
)
from ..state.state_snapshots import (
    StateAdmissionError,
    snapshot_balance_table,
    snapshot_lp_table,
    snapshot_pool_map,
)
from .fcis_fee_occurrence_normal_form import fee_amount_candidates_from_segment_v1
from .fcis_state_read_trace_v5 import (
    FCISContextReadTraceV5,
    FCISStateReadTraceV5,
    merge_fcis_state_read_traces_v5,
)
from .fcis_step_evaluation_values import (
    FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1,
    FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1,
    FCISEvaluatedMaterialV1,
    FCISFeeAllocationV1,
    FCISFeeOccurrenceBindingV1,
    FCISStepCandidateV1,
    FCISStepEvaluationEvidenceV1,
    FCISStepEvaluationOkV1,
    FCISStepEvaluationPhaseV1,
    FCISStepEvaluationRejectV1,
    FCISStepEvaluationResultV1,
    _evaluation_ok_from_evaluator_v1,
    _fee_occurrence_binding_from_evaluator_v1,
)
from .fcis_support_profile_constants_v5 import (
    FCIS_SUPPORT_PROFILE_ID_V5,
    FCIS_SUPPORT_PROFILE_VERSION_V5,
)
from .fcis_support_profile_v5 import (
    _command_preimage_v5,
    _compute_fcis_support_root_v5_admitted,
)
from .fcis_traced_reads_v5 import (
    read_fee_accumulator_v5,
    read_step_execution_context_v5,
)
from .fee_accumulator_transition import (
    FeeAccumulatorTransitionOkV1,
    FeeAccumulatorTransitionRejectV1,
    split_fee_with_owned_policy_v1,
)
from .nonce_batch_transition import (
    IntentNonceBatchOkV1,
    IntentNonceBatchRejectV1,
    _validate_and_apply_intent_nonce_batch_admitted_observed_v5,
)
from .settlement import Settlement
from .settlement_schema import fill_action_text_v1
from .settlement_snapshots import OwnedSettlementV1, snapshot_settlement
from .settlement_strong_validator import (
    StrongSettlementEvaluationResultV1,
    StrongSettlementRejectV1,
    StrongSettlementStateCandidateV1,
    _evaluate_settlement_strong_admitted_observed_v5,
    evaluate_settlement_strong_legacy_committed_for_differential_v1,
)

FCIS_STEP_EVALUATOR_UNMOUNTED_V1 = True
FCIS_STEP_CONTEXT_HASH_DOMAIN_V1 = "fcis_step_execution_context"
MAX_LEGACY_INTENTS_V1 = 256


def _reject(
    phase: FCISStepEvaluationPhaseV1,
    code: str,
    path: tuple[str | int, ...],
    public_reason: str,
) -> FCISStepEvaluationRejectV1:
    return FCISStepEvaluationRejectV1(phase, code, path, public_reason)


@final
@dataclass(frozen=True, slots=True)
class _FCISStepEvaluationBoundRejectV1:
    """Private rejection plus only the canonical prefix reached before it."""

    reject: FCISStepEvaluationRejectV1
    command_root: str | None
    execution_context_hash: str | None
    pre_state_root: str | None

    def __post_init__(self) -> None:
        if type(self.reject) is not FCISStepEvaluationRejectV1:
            raise TypeError("bound rejection requires an exact public rejection")
        for field_name in (
            "command_root",
            "execution_context_hash",
            "pre_state_root",
        ):
            value = object.__getattribute__(self, field_name)
            if value is None:
                continue
            if type(value) is not str or len(value) != 66:
                raise TypeError(f"{field_name} must be None or a canonical digest")
            if not value.startswith("0x") or not all(
                character in "0123456789abcdef" for character in value[2:]
            ):
                raise TypeError(f"{field_name} must be None or a canonical digest")


def _bound_reject_v1(
    reject: FCISStepEvaluationRejectV1,
    *,
    command_root: str | None = None,
    execution_context_hash: str | None = None,
    pre_state_root: str | None = None,
) -> _FCISStepEvaluationBoundRejectV1:
    return _FCISStepEvaluationBoundRejectV1(
        reject,
        command_root,
        execution_context_hash,
        pre_state_root,
    )


def _admit_exact_command_v1(
    settlement: object,
    intents: object,
) -> tuple[OwnedSettlementV1, tuple[OwnedIntentV1, ...]] | FCISStepEvaluationRejectV1:
    """Admit one exact owned command graph at the evaluator boundary."""

    if type(settlement) is not OwnedSettlementV1:
        return _reject(
            FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
            "wrong_exact_type",
            ("settlement",),
            "step settlement requires an exact OwnedSettlementV1",
        )
    if type(intents) is not tuple:
        return _reject(
            FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
            "wrong_exact_type",
            ("intents",),
            "step intents require an exact owned tuple",
        )
    if len(intents) > MAX_LEGACY_INTENTS_V1:
        return _reject(
            FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
            "item_limit",
            ("intents",),
            "step intent batch exceeds the mounted limit",
        )
    for index, intent in enumerate(intents):
        if type(intent) is not OwnedIntentV1:
            return _reject(
                FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
                "wrong_exact_type",
                ("intents", index),
                "step intent requires an exact OwnedIntentV1",
            )
    field = "settlement"
    try:
        exact_settlement = snapshot_settlement(settlement)
    except StateAdmissionError as error:
        path = (field, *error.path)
        detail = f"{error.code.value}:{format_admit_path(path)}"
        return _reject(
            FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
            error.code.value,
            path,
            f"step command admission rejected: {detail}",
        )
    except (TypeError, ValueError):
        return _reject(
            FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
            "admission_rejected",
            (field,),
            "step command admission rejected: admission_rejected:settlement",
        )
    field = "intents"
    try:
        exact_intents = admit_intent_batch(intents)
    except StateAdmissionError as error:
        path = (field, *error.path)
        detail = f"{error.code.value}:{format_admit_path(path)}"
        return _reject(
            FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
            error.code.value,
            path,
            f"step command admission rejected: {detail}",
        )
    except (TypeError, ValueError):
        return _reject(
            FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
            "admission_rejected",
            (field,),
            "step command admission rejected: admission_rejected:intents",
        )
    return exact_settlement, exact_intents


def _admit_legacy_command_shape_for_differential_v1(
    settlement: object,
    intents: object,
) -> tuple[Settlement, list[Intent]] | FCISStepEvaluationRejectV1:
    """Temporary unmounted oracle for the pre-M4 legacy command graph."""

    if type(settlement) is not Settlement:
        return _reject(
            FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
            "wrong_exact_type",
            ("settlement",),
            "step settlement requires an exact legacy Settlement",
        )
    if type(intents) is not list:
        return _reject(
            FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
            "wrong_exact_type",
            ("intents",),
            "step intents require an exact legacy list",
        )
    if len(intents) > MAX_LEGACY_INTENTS_V1:
        return _reject(
            FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
            "item_limit",
            ("intents",),
            "step intent batch exceeds the mounted limit",
        )
    for index, intent in enumerate(intents):
        if type(intent) is not Intent:
            return _reject(
                FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
                "wrong_exact_type",
                ("intents", index),
                "step intent requires an exact legacy Intent",
            )
    return settlement, intents


def _first_rejected_owned_settlement_intent_error_v1(
    settlement: OwnedSettlementV1,
) -> str | None:
    """Return the mounted first-rejected-intent error for an owned settlement."""

    fills_by_id = {fill.intent_id: fill for fill in settlement.fills}
    for intent_id, action in settlement.included_intents:
        if fill_action_text_v1(action) == "FILL":
            continue
        fill = fills_by_id.get(intent_id)
        action_text = fill_action_text_v1(action)
        reason = fill.reason if fill is not None and fill.reason else action_text
        return f"settlement rejected intent_id={intent_id}: {reason}"
    return None


def _context_reject_v1(reject: AdmitReject) -> FCISStepEvaluationRejectV1:
    detail = f"{reject.code.value}:{format_admit_path(reject.path)}"
    return _reject(
        FCISStepEvaluationPhaseV1.CONTEXT_ADMISSION,
        reject.code.value,
        reject.path,
        f"step context admission rejected: {detail}",
    )


def _admit_context_v1(
    source: object,
) -> FCISStepExecutionContextV1 | FCISStepEvaluationRejectV1:
    result = admit_fcis_step_execution_context_v1(source)
    if type(result) is AdmitReject:
        return _context_reject_v1(result)
    if type(result) is not AdmitOk or type(result.value) is not FCISStepExecutionContextV1:
        return _reject(
            FCISStepEvaluationPhaseV1.CONTEXT_ADMISSION,
            "impossible_result",
            (),
            "step context admission returned an impossible result",
        )
    return result.value


def _state_reject_v1(
    reject: AdmitReject,
) -> FCISStepEvaluationRejectV1:
    detail = f"{reject.code.value}:{format_admit_path(reject.path)}"
    return _reject(
        FCISStepEvaluationPhaseV1.STATE_ADMISSION,
        reject.code.value,
        reject.path,
        f"step state admission rejected: {detail}",
    )


def _admit_exact_state_v1(
    source: object,
) -> FCISCommittedStateV1 | FCISStepEvaluationRejectV1:
    """Admit the complete state through one closed aggregate schema."""

    result = admit_fcis_committed_state_v1(source)
    if type(result) is AdmitReject:
        return _state_reject_v1(result)
    if type(result) is not AdmitOk or type(result.value) is not FCISCommittedStateV1:
        return _reject(
            FCISStepEvaluationPhaseV1.STATE_ADMISSION,
            "impossible_result",
            (),
            "step state admission returned an impossible result",
        )
    return result.value


def _evaluate_spot_v1(
    *,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
) -> StrongSettlementEvaluationResultV1:
    result, _state_read_trace = _evaluate_spot_observed_v5(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        settlement=settlement,
        intents=intents,
        context=context,
    )
    return result


def _evaluate_spot_observed_v5(
    *,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
) -> tuple[StrongSettlementEvaluationResultV1, FCISStateReadTraceV5]:
    settlement_context = context.settlement
    observed = _evaluate_settlement_strong_admitted_observed_v5(
        settlement=settlement,
        intents=intents,
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=lp_balances,
        now=settlement_context.now,
        min_lp_position_age_seconds=settlement_context.min_lp_position_age_seconds,
        lp_duration_policy=context.lp_duration_policy,
        mode=settlement_mode_label_v1(settlement_context.mode),
        allow_cow_netting=settlement_context.allow_cow_netting,
        allow_snapshot_bound_quote_bindings=(
            settlement_context.allow_snapshot_bound_quote_bindings
        ),
        protocol_fee_share_bps=settlement_context.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=settlement_context.protocol_fee_recipient_pubkey,
    )
    result: object = observed.result
    if type(result) is StrongSettlementStateCandidateV1:
        return result, observed.state_read_trace
    if type(result) is StrongSettlementRejectV1:
        return result, observed.state_read_trace
    return (
        StrongSettlementRejectV1("strong validator returned an impossible private observed result"),
        observed.state_read_trace,
    )


def _evaluate_spot_legacy_for_differential_v1(
    *,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    settlement: Settlement,
    intents: list[Intent],
    context: FCISStepExecutionContextV1,
) -> StrongSettlementEvaluationResultV1:
    """Temporary unmounted oracle for the pre-M4 legacy command graph."""

    settlement_context = context.settlement
    return evaluate_settlement_strong_legacy_committed_for_differential_v1(
        settlement=settlement,
        intents=intents,
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=lp_balances,
        now=settlement_context.now,
        min_lp_position_age_seconds=settlement_context.min_lp_position_age_seconds,
        lp_duration_policy=context.lp_duration_policy,
        mode=settlement_mode_label_v1(settlement_context.mode),
        allow_cow_netting=settlement_context.allow_cow_netting,
        allow_snapshot_bound_quote_bindings=(
            settlement_context.allow_snapshot_bound_quote_bindings
        ),
        protocol_fee_share_bps=settlement_context.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=settlement_context.protocol_fee_recipient_pubkey,
    )


def _nonce_candidate_v1(
    *,
    state: FCISCommittedStateV1,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
) -> IntentNonceBatchOkV1 | FCISStepEvaluationRejectV1:
    result, _state_read_trace = _nonce_candidate_observed_v5(
        state=state,
        intents=intents,
        context=context,
    )
    return result


def _nonce_candidate_observed_v5(
    *,
    state: FCISCommittedStateV1,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
) -> tuple[IntentNonceBatchOkV1 | FCISStepEvaluationRejectV1, FCISStateReadTraceV5]:
    observed = _validate_and_apply_intent_nonce_batch_admitted_observed_v5(
        nonces=state.nonces,
        intents=intents,
        require_all_nonces=context.require_all_nonces,
    )
    result: object = observed.result
    if type(result) is IntentNonceBatchRejectV1:
        reject_result = cast(IntentNonceBatchRejectV1, result)
        return (
            _reject(
                FCISStepEvaluationPhaseV1.NONCE,
                reject_result.code.value,
                (),
                reject_result.public_reason,
            ),
            observed.state_read_trace,
        )
    if type(result) is not IntentNonceBatchOkV1:
        return (
            _reject(
                FCISStepEvaluationPhaseV1.NONCE,
                "impossible_result",
                (),
                "step nonce transition returned an impossible result",
            ),
            observed.state_read_trace,
        )
    return result, observed.state_read_trace


def _spot_candidate_v1(
    *,
    state: FCISCommittedStateV1,
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
) -> StrongSettlementStateCandidateV1 | FCISStepEvaluationRejectV1:
    result, _state_read_trace = _spot_candidate_observed_v5(
        state=state,
        settlement=settlement,
        intents=intents,
        context=context,
    )
    return result


def _spot_candidate_observed_v5(
    *,
    state: FCISCommittedStateV1,
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
) -> tuple[
    StrongSettlementStateCandidateV1 | FCISStepEvaluationRejectV1,
    FCISStateReadTraceV5,
]:
    evaluated_result, state_read_trace = _evaluate_spot_observed_v5(
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        settlement=settlement,
        intents=intents,
        context=context,
    )
    result: object = evaluated_result
    if type(result) is StrongSettlementRejectV1:
        reject = cast(StrongSettlementRejectV1, result)
        return (
            _reject(
                FCISStepEvaluationPhaseV1.SETTLEMENT,
                "strong_settlement_rejected",
                (),
                reject.reason,
            ),
            state_read_trace,
        )
    if type(result) is not StrongSettlementStateCandidateV1:
        return (
            _reject(
                FCISStepEvaluationPhaseV1.SETTLEMENT,
                "impossible_result",
                (),
                "step settlement transition returned an impossible result",
            ),
            state_read_trace,
        )
    if context.reject_settlements_with_rejected_intents:
        rejected_intent_error = _first_rejected_owned_settlement_intent_error_v1(settlement)
        if rejected_intent_error is not None:
            return (
                _reject(
                    FCISStepEvaluationPhaseV1.SETTLEMENT,
                    "rejected_intent",
                    (),
                    rejected_intent_error,
                ),
                state_read_trace,
            )
    return result, state_read_trace


def _total_settlement_fees_v1(
    settlement: OwnedSettlementV1,
) -> int | FCISStepEvaluationRejectV1:
    total = 0
    for index, fill in enumerate(settlement.fills):
        fee = fill.fee_paid
        if fee is None:
            continue
        if type(fee) is not int or fee < 0:
            return _reject(
                FCISStepEvaluationPhaseV1.FEE,
                "wrong_exact_type",
                ("settlement", "fills", index, "fee_paid"),
                "settlement fee must be an exact nonnegative int",
            )
        total += fee
    return total


def _fee_candidate_v1(
    *,
    state: FCISCommittedStateV1,
    settlement: OwnedSettlementV1,
    context: FCISStepExecutionContextV1,
    source_fee_occurrence: object | None = None,
) -> tuple[CommittedFeeAccumulatorStateV1, FCISFeeAllocationV1 | None] | FCISStepEvaluationRejectV1:
    result, _state_read_trace = _fee_candidate_observed_v5(
        state=state,
        settlement=settlement,
        context=context,
        state_read_trace=FCISStateReadTraceV5(),
        source_fee_occurrence=source_fee_occurrence,
    )
    return result


def _fee_candidate_observed_v5(
    *,
    state: FCISCommittedStateV1,
    settlement: OwnedSettlementV1,
    context: FCISStepExecutionContextV1,
    state_read_trace: FCISStateReadTraceV5,
    source_fee_occurrence: object | None = None,
) -> tuple[
    tuple[CommittedFeeAccumulatorStateV1, FCISFeeAllocationV1 | None] | FCISStepEvaluationRejectV1,
    FCISStateReadTraceV5,
]:
    if source_fee_occurrence is not None:
        if type(source_fee_occurrence) is not FCISFeeOccurrenceBindingV1:
            return (
                _reject(
                    FCISStepEvaluationPhaseV1.FEE,
                    "source_occurrence_rejected",
                    ("source_fee_occurrence",),
                    "fee source occurrence requires the exact evaluator binding",
                ),
                state_read_trace,
            )
        exact_source_fee_occurrence = source_fee_occurrence
        try:
            fee_amount_candidates_from_segment_v1(exact_source_fee_occurrence.segment)
        except (TypeError, ValueError, ArithmeticError):
            return (
                _reject(
                    FCISStepEvaluationPhaseV1.FEE,
                    "source_occurrence_rejected",
                    ("source_fee_occurrence", "segment"),
                    "fee source occurrence segment failed exact projection",
                ),
                state_read_trace,
            )
    policy = context.fee_split_policy
    if policy is None:
        return (state.fee_accumulator, None), state_read_trace
    fee_accumulator, next_trace = read_fee_accumulator_v5(
        state.fee_accumulator,
        state_read_trace,
    )
    total = _total_settlement_fees_v1(settlement)
    if type(total) is FCISStepEvaluationRejectV1:
        return total, next_trace
    result: object = split_fee_with_owned_policy_v1(
        fee_amount=total,
        policy=policy,
        state=fee_accumulator,
    )
    if type(result) is FeeAccumulatorTransitionRejectV1:
        reject = cast(FeeAccumulatorTransitionRejectV1, result)
        return (
            _reject(
                FCISStepEvaluationPhaseV1.FEE,
                reject.code.value,
                (reject.field,),
                f"{reject.code.value}:{reject.field}",
            ),
            next_trace,
        )
    if type(result) is not FeeAccumulatorTransitionOkV1:
        return (
            _reject(
                FCISStepEvaluationPhaseV1.FEE,
                "impossible_result",
                (),
                "step fee transition returned an impossible result",
            ),
            next_trace,
        )
    ok = cast(FeeAccumulatorTransitionOkV1, result)
    allocation = ok.allocation
    return (
        (
            ok.state,
            FCISFeeAllocationV1(
                buyback_amount=allocation.buyback_amount,
                treasury_amount=allocation.treasury_amount,
                rewards_amount=allocation.rewards_amount,
                dust_carried=allocation.dust_carried,
            ),
        ),
        next_trace,
    )


def _canonical_state_root_binding_v1(
    state: FCISCommittedStateV1,
    snapshot_version: int,
) -> tuple[bytes, bytes, str]:
    """Delegate all eight fields to the shared canonical state binding."""

    return cast(
        tuple[bytes, bytes, str], canonical_committed_state_root_binding_v1(state, snapshot_version)
    )


def _pre_state_binding_v1(
    state: FCISCommittedStateV1,
    context: FCISStepExecutionContextV1,
) -> tuple[bytes, str, bytes, str] | FCISStepEvaluationRejectV1:
    try:
        context_bytes = encode_fcis_execution_context_v1(
            FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
            context,
        )
        _, root_preimage, root = _canonical_state_root_binding_v1(state, context.snapshot_version)
    except (StateAdmissionError, TypeError, ValueError):
        return _reject(
            FCISStepEvaluationPhaseV1.PRE_STATE_BINDING,
            "canonical_binding_rejected",
            (),
            "step pre-state canonical binding rejected",
        )
    context_hash = sha256_hex(
        domain_sep_bytes(FCIS_STEP_CONTEXT_HASH_DOMAIN_V1, version=1) + context_bytes
    )
    return context_bytes, context_hash, root_preimage, root


def _candidate_evidence_v1(
    *,
    pre_state: FCISCommittedStateV1,
    candidate: FCISStepCandidateV1,
    settlement: OwnedSettlementV1,
    context: FCISStepExecutionContextV1,
    intents: tuple[OwnedIntentV1, ...],
    pre_binding: tuple[bytes, str, bytes, str],
    state_read_trace: FCISStateReadTraceV5,
    context_read_trace: FCISContextReadTraceV5,
    source_fee_occurrence: FCISFeeOccurrenceBindingV1 | None = None,
) -> FCISStepEvaluationEvidenceV1 | FCISStepEvaluationRejectV1:
    context_bytes, context_hash, preimage, pre_root = pre_binding
    try:
        snapshot_bytes, post_preimage, post_root = _canonical_state_root_binding_v1(
            candidate.state,
            context.snapshot_version,
        )
        support_evidence = _compute_fcis_support_root_v5_admitted(
            settlement=settlement,
            intents=intents,
            context=context,
            balances=pre_state.balances,
            pools=pre_state.pools,
            lp_balances=pre_state.lp_balances,
            nonces=pre_state.nonces,
            fee_accumulator=pre_state.fee_accumulator,
            state_read_trace=state_read_trace,
            context_read_trace=context_read_trace,
        )
        if support_evidence.execution_context_hash != context_hash:
            raise ValueError("support-root context binding mismatch")
        command_preimage = _command_preimage_v5(settlement, intents)
        trace = support_evidence.trace
        state_read_count = (
            len(trace.balance_keys)
            + len(trace.pool_ids)
            + len(trace.lp_keys)
            + len(trace.nonce_keys)
            + (1 if trace.reads_fee_accumulator else 0)
        )
        context_read_count = len(trace.context_paths)
        canonical_input_bytes = len(command_preimage) + len(context_bytes) + len(preimage)
        witness_bytes = len(support_evidence.support_set_preimage) + len(
            support_evidence.root_preimage
        )
    except (StateAdmissionError, TypeError, ValueError):
        return _reject(
            FCISStepEvaluationPhaseV1.EVIDENCE,
            "canonical_evidence_rejected",
            (),
            "step candidate canonical evidence rejected",
        )
    return FCISStepEvaluationEvidenceV1(
        algorithm_id=FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1,
        algorithm_version=FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1,
        execution_context_bytes=context_bytes,
        execution_context_hash=context_hash,
        command_root=support_evidence.command_root,
        pre_state_root_preimage=preimage,
        pre_state_root=pre_root,
        post_state_root_preimage=post_preimage,
        post_state_root=post_root,
        snapshot_version=context.snapshot_version,
        canonical_snapshot_bytes=snapshot_bytes,
        snapshot_commitment=post_root,
        support_root_version=FCIS_SUPPORT_PROFILE_VERSION_V5,
        support_profile_id=FCIS_SUPPORT_PROFILE_ID_V5,
        support_set_commitment=support_evidence.support_set_commitment,
        support_root=support_evidence.root,
        canonical_input_bytes=canonical_input_bytes,
        state_read_count=state_read_count,
        context_read_count=context_read_count,
        witness_bytes=witness_bytes,
        source_fee_occurrence=source_fee_occurrence,
    )


def _reject_after_trace_containment_v5(
    *,
    reject: FCISStepEvaluationRejectV1,
    pre_state: FCISCommittedStateV1,
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
    state_read_trace: FCISStateReadTraceV5,
    context_read_trace: FCISContextReadTraceV5,
) -> FCISStepEvaluationRejectV1:
    """Check a rejection prefix, then discard all success-only evidence."""

    try:
        _compute_fcis_support_root_v5_admitted(
            settlement=settlement,
            intents=intents,
            context=context,
            balances=pre_state.balances,
            pools=pre_state.pools,
            lp_balances=pre_state.lp_balances,
            nonces=pre_state.nonces,
            fee_accumulator=pre_state.fee_accumulator,
            state_read_trace=state_read_trace,
            context_read_trace=context_read_trace,
        )
    except (StateAdmissionError, TypeError, ValueError):
        return _reject(
            FCISStepEvaluationPhaseV1.EVIDENCE,
            "support_trace_rejected",
            (),
            "step rejection read trace escaped declared support",
        )
    return reject


def _evaluate_fcis_step_candidate_bound_v1(
    *,
    state_source: object,
    settlement: object,
    intents: object,
    context: object,
    source_occurrence_segment: object | None = None,
) -> FCISStepEvaluationOkV1 | _FCISStepEvaluationBoundRejectV1:
    """Evaluate once while retaining only canonical rejection-prefix roots."""

    source_binding: FCISFeeOccurrenceBindingV1 | None = None
    if source_occurrence_segment is not None:
        try:
            source_binding = _fee_occurrence_binding_from_evaluator_v1(source_occurrence_segment)
        except (TypeError, ValueError, ArithmeticError):
            return _bound_reject_v1(
                _reject(
                    FCISStepEvaluationPhaseV1.EVIDENCE,
                    "source_occurrence_rejected",
                    ("source_fee_occurrence",),
                    "source fee occurrence binding rejected before candidate construction",
                )
            )

    command = _admit_exact_command_v1(settlement, intents)
    if type(command) is FCISStepEvaluationRejectV1:
        return _bound_reject_v1(command)
    exact_settlement, exact_intents = command
    try:
        command_root = sha256_hex(_command_preimage_v5(exact_settlement, exact_intents))
    except (TypeError, ValueError):
        return _bound_reject_v1(
            _reject(
                FCISStepEvaluationPhaseV1.PRE_STATE_BINDING,
                "canonical_binding_rejected",
                (),
                "step command canonical binding rejected",
            )
        )
    exact_context = _admit_context_v1(context)
    if type(exact_context) is FCISStepEvaluationRejectV1:
        return _bound_reject_v1(exact_context, command_root=command_root)
    state = _admit_exact_state_v1(state_source)
    if type(state) is FCISStepEvaluationRejectV1:
        return _bound_reject_v1(state, command_root=command_root)
    _context_projection, context_read_trace = read_step_execution_context_v5(exact_context)
    pre_binding = _pre_state_binding_v1(state, exact_context)
    if type(pre_binding) is FCISStepEvaluationRejectV1:
        return _bound_reject_v1(pre_binding, command_root=command_root)
    (
        _context_bytes,
        execution_context_hash,
        _pre_state_root_preimage,
        pre_state_root,
    ) = pre_binding
    nonce, nonce_read_trace = _nonce_candidate_observed_v5(
        state=state,
        intents=exact_intents,
        context=exact_context,
    )
    if type(nonce) is FCISStepEvaluationRejectV1:
        checked_reject = _reject_after_trace_containment_v5(
            reject=nonce,
            pre_state=state,
            settlement=exact_settlement,
            intents=exact_intents,
            context=exact_context,
            state_read_trace=nonce_read_trace,
            context_read_trace=context_read_trace,
        )
        return _bound_reject_v1(
            checked_reject,
            command_root=command_root,
            execution_context_hash=execution_context_hash,
            pre_state_root=pre_state_root,
        )
    spot, spot_read_trace = _spot_candidate_observed_v5(
        state=state,
        settlement=exact_settlement,
        intents=exact_intents,
        context=exact_context,
    )
    combined_read_trace = merge_fcis_state_read_traces_v5(
        nonce_read_trace,
        spot_read_trace,
    )
    if type(spot) is FCISStepEvaluationRejectV1:
        checked_reject = _reject_after_trace_containment_v5(
            reject=spot,
            pre_state=state,
            settlement=exact_settlement,
            intents=exact_intents,
            context=exact_context,
            state_read_trace=combined_read_trace,
            context_read_trace=context_read_trace,
        )
        return _bound_reject_v1(
            checked_reject,
            command_root=command_root,
            execution_context_hash=execution_context_hash,
            pre_state_root=pre_state_root,
        )
    fee, complete_read_trace = _fee_candidate_observed_v5(
        state=state,
        settlement=exact_settlement,
        context=exact_context,
        state_read_trace=combined_read_trace,
        source_fee_occurrence=source_binding,
    )
    if type(fee) is FCISStepEvaluationRejectV1:
        checked_reject = _reject_after_trace_containment_v5(
            reject=fee,
            pre_state=state,
            settlement=exact_settlement,
            intents=exact_intents,
            context=exact_context,
            state_read_trace=complete_read_trace,
            context_read_trace=context_read_trace,
        )
        return _bound_reject_v1(
            checked_reject,
            command_root=command_root,
            execution_context_hash=execution_context_hash,
            pre_state_root=pre_state_root,
        )
    successor = FCISCommittedStateV1(
        balances=spot.balances,
        pools=spot.pools,
        lp_balances=spot.lp_balances,
        nonces=nonce.state,
        vault=state.vault,
        oracle=state.oracle,
        fee_accumulator=fee[0],
        perps=state.perps,
    )
    candidate = FCISStepCandidateV1(
        state=successor,
        balance_patch=spot.balance_patch,
        pool_patch=spot.pool_patch,
        lp_patch=spot.lp_patch,
        nonce_patch=nonce.patch,
        fee_allocation=fee[1],
        source_fee_occurrence=source_binding,
    )
    evidence = _candidate_evidence_v1(
        pre_state=state,
        candidate=candidate,
        settlement=exact_settlement,
        context=exact_context,
        intents=exact_intents,
        pre_binding=pre_binding,
        state_read_trace=complete_read_trace,
        context_read_trace=context_read_trace,
        source_fee_occurrence=source_binding,
    )
    if type(evidence) is FCISStepEvaluationRejectV1:
        return _bound_reject_v1(
            evidence,
            command_root=command_root,
            execution_context_hash=execution_context_hash,
            pre_state_root=pre_state_root,
        )
    material = FCISEvaluatedMaterialV1(
        pre_state=state,
        settlement=exact_settlement,
        intents=exact_intents,
        context=exact_context,
    )
    return _evaluation_ok_from_evaluator_v1(material, candidate, evidence)


def evaluate_fcis_step_candidate_v1(
    *,
    state_source: object,
    settlement: object,
    intents: object,
    context: object,
) -> FCISStepEvaluationResultV1:
    """Evaluate one exact local candidate without exposing private prefixes."""

    result = _evaluate_fcis_step_candidate_bound_v1(
        state_source=state_source,
        settlement=settlement,
        intents=intents,
        context=context,
    )
    if type(result) is _FCISStepEvaluationBoundRejectV1:
        return result.reject
    return result


def evaluate_source_bound_fcis_step_candidate_v1(
    *,
    source_occurrence: object,
) -> FCISStepEvaluationResultV1:
    """Evaluate a candidate only after verifying its source-derived SLNF segment."""

    from .fcis_fee_occurrence_extractor import (
        SourceBoundFeeOccurrenceRejectV1,
        SourceBoundFeeOccurrenceV1,
        verify_source_bound_fee_occurrence_v1,
    )

    if type(source_occurrence) is not SourceBoundFeeOccurrenceV1:
        return _reject(
            FCISStepEvaluationPhaseV1.EVIDENCE,
            "wrong_exact_type",
            ("source_occurrence",),
            "source-bound evaluation requires an exact source occurrence",
        )
    exact_occurrence = cast(SourceBoundFeeOccurrenceV1, source_occurrence)
    source_reject = verify_source_bound_fee_occurrence_v1(exact_occurrence)
    if type(source_reject) is SourceBoundFeeOccurrenceRejectV1:
        return _reject(
            FCISStepEvaluationPhaseV1.EVIDENCE,
            "source_occurrence_rejected",
            ("source_occurrence", source_reject.code.value, *source_reject.path),
            "source-derived fee occurrence failed fresh verification",
        )
    result = _evaluate_fcis_step_candidate_bound_v1(
        state_source=exact_occurrence.material.pre_state,
        settlement=exact_occurrence.material.settlement,
        intents=exact_occurrence.material.intents,
        context=exact_occurrence.material.context,
        source_occurrence_segment=exact_occurrence.segment,
    )
    if type(result) is _FCISStepEvaluationBoundRejectV1:
        return result.reject
    return result


def evaluate_fcis_spot_candidate_v1(
    *,
    balances: object,
    pools: object,
    lp_balances: object,
    settlement: object,
    intents: object,
    context: object,
    lp_duration_policy: object,
) -> StrongSettlementEvaluationResultV1:
    """Evaluate only the exact spot candidate for shadow differential tests.

    This is a temporary unmounted legacy differential oracle.  It admits the
    pre-M4 legacy command graph and delegates to the legacy differential
    evaluator.  The exact evaluator path uses ``_admit_exact_command_v1`` and
    then forwards that one admitted graph to private exact consumers.
    """

    command = _admit_legacy_command_shape_for_differential_v1(settlement, intents)
    if type(command) is FCISStepEvaluationRejectV1:
        return StrongSettlementRejectV1(command.public_reason)
    exact_command = command
    context_result = admit_fcis_settlement_execution_context_v1(context)
    if type(context_result) is AdmitReject:
        return StrongSettlementRejectV1(_context_reject_v1(context_result).public_reason)
    policy_result = admit_optional_lp_duration_policy_v1(lp_duration_policy)
    if type(policy_result) is AdmitReject:
        detail = f"{policy_result.code.value}:{format_admit_path(policy_result.path)}"
        return StrongSettlementRejectV1(f"spot LP duration-policy admission rejected: {detail}")
    try:
        exact_balances = snapshot_balance_table(balances)
        exact_pools = snapshot_pool_map(pools)
        exact_lp_balances = snapshot_lp_table(lp_balances)
    except StateAdmissionError as error:
        return StrongSettlementRejectV1(
            f"spot state admission rejected: {error.code.value}:{format_admit_path(error.path)}"
        )
    if (
        type(context_result) is not AdmitOk
        or type(context_result.value) is not FCISSettlementExecutionContextV1
    ):
        return StrongSettlementRejectV1("spot context admission returned an impossible result")
    if type(policy_result) is not AdmitOk or (
        policy_result.value is not None and type(policy_result.value) is not LPDurationRiskPolicyV1
    ):
        return StrongSettlementRejectV1(
            "spot LP duration-policy admission returned an impossible result"
        )
    exact_settlement, exact_intents = exact_command
    step_context = FCISStepExecutionContextV1(
        settlement=context_result.value,
        require_all_nonces=False,
        reject_settlements_with_rejected_intents=False,
        fee_split_policy=None,
        lp_duration_policy=policy_result.value,
        snapshot_version=1,
    )
    return _evaluate_spot_legacy_for_differential_v1(
        balances=exact_balances,
        pools=exact_pools,
        lp_balances=exact_lp_balances,
        settlement=exact_settlement,
        intents=exact_intents,
        context=step_context,
    )


__all__ = (
    "FCIS_STEP_EVALUATOR_UNMOUNTED_V1",
    "evaluate_fcis_spot_candidate_v1",
    "evaluate_fcis_step_candidate_v1",
    "evaluate_source_bound_fcis_step_candidate_v1",
)
