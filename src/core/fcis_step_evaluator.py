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
from ..state.committed_dex_snapshot import canonical_snapshot_bytes_from_committed_state_v1
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
from ..state.intents import Intent
from ..state.lp_duration_policy_context import admit_optional_lp_duration_policy_v1
from ..state.lp_duration_policy_values import LPDurationRiskPolicyV1
from ..state.owned_collections import OwnedMapV1
from ..state.snapshot_combinators import AdmitOk, AdmitReject, format_admit_path
from ..state.state_root import state_root_preimage_with_committed_spot_state_v1
from ..state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedOracleStateV1,
    CommittedPerpsStateV1,
    CommittedPoolStateV1,
    CommittedVaultStateV1,
)
from ..state.state_snapshots import (
    StateAdmissionError,
    snapshot_balance_table,
    snapshot_fee_accumulator,
    snapshot_lp_table,
    snapshot_nonce_table,
    snapshot_oracle,
    snapshot_perps,
    snapshot_pool_map,
    snapshot_vault,
)
from ..state.support_root import compute_support_state_root_for_batch_committed_v1
from .fcis_step_evaluation_values import (
    FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1,
    FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1,
    FCISFeeAllocationV1,
    FCISStepCandidateV1,
    FCISStepEvaluationEvidenceV1,
    FCISStepEvaluationOkV1,
    FCISStepEvaluationPhaseV1,
    FCISStepEvaluationRejectV1,
    FCISStepEvaluationResultV1,
)
from .fee_accumulator_transition import (
    FeeAccumulatorTransitionOkV1,
    FeeAccumulatorTransitionRejectV1,
    split_fee_with_owned_policy_v1,
)
from .nonce_batch_transition import (
    IntentNonceBatchOkV1,
    IntentNonceBatchRejectV1,
    validate_and_apply_intent_nonce_batch_committed_v1,
)
from .settlement import Settlement, first_rejected_settlement_intent_error
from .settlement_strong_validator import (
    StrongSettlementEvaluationResultV1,
    StrongSettlementRejectV1,
    StrongSettlementStateCandidateV1,
    evaluate_settlement_strong_legacy_committed_for_differential_v1,
)

FCIS_STEP_EVALUATOR_UNMOUNTED_V1 = True
FCIS_STEP_CONTEXT_HASH_DOMAIN_V1 = "fcis_step_execution_context"
MAX_LEGACY_INTENTS_V1 = 256


@final
@dataclass(frozen=True, slots=True)
class _ExactStepStateV1:
    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1
    nonces: CommittedNonceTableV1
    vault: CommittedVaultStateV1 | None
    oracle: CommittedOracleStateV1 | None
    fee_accumulator: CommittedFeeAccumulatorStateV1
    perps: CommittedPerpsStateV1 | None


def _reject(
    phase: FCISStepEvaluationPhaseV1,
    code: str,
    path: tuple[str | int, ...],
    public_reason: str,
) -> FCISStepEvaluationRejectV1:
    return FCISStepEvaluationRejectV1(phase, code, path, public_reason)


def _admit_legacy_command_shape_v1(
    settlement: object,
    intents: object,
) -> tuple[Settlement, list[Intent]] | FCISStepEvaluationRejectV1:
    """Bound the temporary PR #478 carrier without claiming owned authority."""

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
    field: str,
    error: StateAdmissionError,
) -> FCISStepEvaluationRejectV1:
    path = (field, *error.path)
    detail = f"{error.code.value}:{format_admit_path(path)}"
    return _reject(
        FCISStepEvaluationPhaseV1.STATE_ADMISSION,
        error.code.value,
        path,
        f"step state admission rejected: {detail}",
    )


def _wrong_state_type_v1(field: str) -> FCISStepEvaluationRejectV1:
    return _reject(
        FCISStepEvaluationPhaseV1.STATE_ADMISSION,
        "wrong_exact_type",
        (field,),
        f"step {field} requires exact committed state",
    )


def _admit_exact_state_v1(
    *,
    balances: object,
    pools: object,
    lp_balances: object,
    nonces: object,
    vault: object,
    oracle: object,
    fee_accumulator: object,
    perps: object,
) -> _ExactStepStateV1 | FCISStepEvaluationRejectV1:
    """Revalidate all eight exact fields in the normative M5 field order."""

    exact_types = (
        ("balances", balances, CommittedBalanceTableV1),
        ("pools", pools, OwnedMapV1),
        ("lp_balances", lp_balances, CommittedLPTableV1),
        ("nonces", nonces, CommittedNonceTableV1),
        ("vault", vault, CommittedVaultStateV1),
        ("oracle", oracle, CommittedOracleStateV1),
        ("fee_accumulator", fee_accumulator, CommittedFeeAccumulatorStateV1),
        ("perps", perps, CommittedPerpsStateV1),
    )
    for field, value, exact_type in exact_types:
        if field in ("vault", "oracle", "perps") and value is None:
            continue
        if type(value) is not exact_type:
            return _wrong_state_type_v1(field)

    field = "balances"
    try:
        exact_balances = snapshot_balance_table(balances)
        field = "pools"
        exact_pools = snapshot_pool_map(pools)
        field = "lp_balances"
        exact_lp = snapshot_lp_table(lp_balances)
        field = "nonces"
        exact_nonces = snapshot_nonce_table(nonces)
        field = "vault"
        exact_vault = snapshot_vault(vault)
        field = "oracle"
        exact_oracle = snapshot_oracle(oracle)
        field = "fee_accumulator"
        exact_fees = snapshot_fee_accumulator(fee_accumulator)
        field = "perps"
        exact_perps = snapshot_perps(perps)
    except StateAdmissionError as error:
        return _state_reject_v1(field, error)
    return _ExactStepStateV1(
        balances=exact_balances,
        pools=exact_pools,
        lp_balances=exact_lp,
        nonces=exact_nonces,
        vault=exact_vault,
        oracle=exact_oracle,
        fee_accumulator=exact_fees,
        perps=exact_perps,
    )


def _evaluate_spot_v1(
    *,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    settlement: Settlement,
    intents: list[Intent],
    context: FCISStepExecutionContextV1,
) -> StrongSettlementEvaluationResultV1:
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
    state: _ExactStepStateV1,
    intents: list[Intent],
    context: FCISStepExecutionContextV1,
) -> IntentNonceBatchOkV1 | FCISStepEvaluationRejectV1:
    result = validate_and_apply_intent_nonce_batch_committed_v1(
        nonces=state.nonces,
        intents=intents,
        require_all_nonces=context.require_all_nonces,
    )
    if type(result) is IntentNonceBatchRejectV1:
        return _reject(
            FCISStepEvaluationPhaseV1.NONCE,
            result.code.value,
            (),
            result.public_reason,
        )
    if type(result) is not IntentNonceBatchOkV1:
        return _reject(
            FCISStepEvaluationPhaseV1.NONCE,
            "impossible_result",
            (),
            "step nonce transition returned an impossible result",
        )
    return result


def _spot_candidate_v1(
    *,
    state: _ExactStepStateV1,
    settlement: Settlement,
    intents: list[Intent],
    context: FCISStepExecutionContextV1,
) -> StrongSettlementStateCandidateV1 | FCISStepEvaluationRejectV1:
    result: object = _evaluate_spot_v1(
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        settlement=settlement,
        intents=intents,
        context=context,
    )
    if type(result) is StrongSettlementRejectV1:
        return _reject(
            FCISStepEvaluationPhaseV1.SETTLEMENT,
            "strong_settlement_rejected",
            (),
            result.reason,
        )
    if type(result) is not StrongSettlementStateCandidateV1:
        return _reject(
            FCISStepEvaluationPhaseV1.SETTLEMENT,
            "impossible_result",
            (),
            "step settlement transition returned an impossible result",
        )
    if context.reject_settlements_with_rejected_intents:
        rejected_intent_error = first_rejected_settlement_intent_error(settlement)
        if rejected_intent_error is not None:
            return _reject(
                FCISStepEvaluationPhaseV1.SETTLEMENT,
                "rejected_intent",
                (),
                rejected_intent_error,
            )
    return result


def _total_settlement_fees_v1(
    settlement: Settlement,
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
    state: _ExactStepStateV1,
    settlement: Settlement,
    context: FCISStepExecutionContextV1,
) -> tuple[CommittedFeeAccumulatorStateV1, FCISFeeAllocationV1 | None] | FCISStepEvaluationRejectV1:
    policy = context.fee_split_policy
    if policy is None:
        return state.fee_accumulator, None
    total = _total_settlement_fees_v1(settlement)
    if type(total) is FCISStepEvaluationRejectV1:
        return total
    result = split_fee_with_owned_policy_v1(
        fee_amount=total,
        policy=policy,
        state=state.fee_accumulator,
    )
    if type(result) is FeeAccumulatorTransitionRejectV1:
        return _reject(
            FCISStepEvaluationPhaseV1.FEE,
            result.code.value,
            (result.field,),
            f"{result.code.value}:{result.field}",
        )
    if type(result) is not FeeAccumulatorTransitionOkV1:
        return _reject(
            FCISStepEvaluationPhaseV1.FEE,
            "impossible_result",
            (),
            "step fee transition returned an impossible result",
        )
    allocation = result.allocation
    return (
        result.state,
        FCISFeeAllocationV1(
            buyback_amount=allocation.buyback_amount,
            treasury_amount=allocation.treasury_amount,
            rewards_amount=allocation.rewards_amount,
            dust_carried=allocation.dust_carried,
        ),
    )


def _pre_state_binding_v1(
    state: _ExactStepStateV1,
    context: FCISStepExecutionContextV1,
) -> tuple[bytes, str, bytes, str] | FCISStepEvaluationRejectV1:
    try:
        context_bytes = encode_fcis_execution_context_v1(
            FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
            context,
        )
        root_preimage = state_root_preimage_with_committed_spot_state_v1(
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
            nonces=state.nonces,
            fee_accumulator=state.fee_accumulator,
        )
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
    return context_bytes, context_hash, root_preimage, sha256_hex(root_preimage)


def _candidate_evidence_v1(
    *,
    candidate: FCISStepCandidateV1,
    context: FCISStepExecutionContextV1,
    intents: list[Intent],
    pre_binding: tuple[bytes, str, bytes, str],
) -> FCISStepEvaluationEvidenceV1 | FCISStepEvaluationRejectV1:
    context_bytes, context_hash, preimage, pre_root = pre_binding
    try:
        snapshot_bytes = canonical_snapshot_bytes_from_committed_state_v1(
            version=context.snapshot_version,
            balances=candidate.spot.balances,
            pools=candidate.spot.pools,
            lp_balances=candidate.spot.lp_balances,
            nonces=candidate.nonces,
            fee_accumulator=candidate.fee_accumulator,
            vault=candidate.vault,
            oracle=candidate.oracle,
            perps=candidate.perps,
        )
        post_preimage = state_root_preimage_with_committed_spot_state_v1(
            balances=candidate.spot.balances,
            pools=candidate.spot.pools,
            lp_balances=candidate.spot.lp_balances,
            nonces=candidate.nonces,
            fee_accumulator=candidate.fee_accumulator,
        )
        support_root = compute_support_state_root_for_batch_committed_v1(
            intents=intents,
            balances=candidate.spot.balances,
            pools=candidate.spot.pools,
            lp_balances=candidate.spot.lp_balances,
            nonces=candidate.nonces,
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
        pre_state_root_preimage=preimage,
        pre_state_root=pre_root,
        post_state_root_preimage=post_preimage,
        post_state_root=sha256_hex(post_preimage),
        snapshot_version=context.snapshot_version,
        canonical_snapshot_bytes=snapshot_bytes,
        snapshot_commitment=sha256_hex(
            domain_sep_bytes("dex_snapshot", version=context.snapshot_version) + snapshot_bytes
        ),
        support_root=support_root,
    )


def evaluate_fcis_step_candidate_v1(
    *,
    balances: object,
    pools: object,
    lp_balances: object,
    nonces: object,
    vault: object,
    oracle: object,
    fee_accumulator: object,
    perps: object,
    settlement: object,
    intents: object,
    context: object,
) -> FCISStepEvaluationResultV1:
    """Evaluate one exact local candidate without mounting authority."""

    command = _admit_legacy_command_shape_v1(settlement, intents)
    if type(command) is FCISStepEvaluationRejectV1:
        return command
    exact_context = _admit_context_v1(context)
    if type(exact_context) is FCISStepEvaluationRejectV1:
        return exact_context
    state = _admit_exact_state_v1(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        nonces=nonces,
        vault=vault,
        oracle=oracle,
        fee_accumulator=fee_accumulator,
        perps=perps,
    )
    if type(state) is FCISStepEvaluationRejectV1:
        return state
    pre_binding = _pre_state_binding_v1(state, exact_context)
    if type(pre_binding) is FCISStepEvaluationRejectV1:
        return pre_binding
    exact_settlement, exact_intents = command
    nonce = _nonce_candidate_v1(
        state=state,
        intents=exact_intents,
        context=exact_context,
    )
    if type(nonce) is FCISStepEvaluationRejectV1:
        return nonce
    spot = _spot_candidate_v1(
        state=state,
        settlement=exact_settlement,
        intents=exact_intents,
        context=exact_context,
    )
    if type(spot) is FCISStepEvaluationRejectV1:
        return spot
    fee = _fee_candidate_v1(
        state=state,
        settlement=exact_settlement,
        context=exact_context,
    )
    if type(fee) is FCISStepEvaluationRejectV1:
        return fee
    candidate = FCISStepCandidateV1(
        spot=spot,
        nonces=nonce.state,
        nonce_patch=nonce.patch,
        fee_accumulator=fee[0],
        fee_allocation=fee[1],
        vault=state.vault,
        oracle=state.oracle,
        perps=state.perps,
    )
    evidence = _candidate_evidence_v1(
        candidate=candidate,
        context=exact_context,
        intents=exact_intents,
        pre_binding=pre_binding,
    )
    if type(evidence) is FCISStepEvaluationRejectV1:
        return evidence
    return FCISStepEvaluationOkV1(candidate, evidence)


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
    """Evaluate only the exact spot candidate for shadow differential tests."""

    command = _admit_legacy_command_shape_v1(settlement, intents)
    if type(command) is FCISStepEvaluationRejectV1:
        reject = cast(FCISStepEvaluationRejectV1, command)
        return StrongSettlementRejectV1(reject.public_reason)
    exact_command = cast(tuple[Settlement, list[Intent]], command)
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
    return _evaluate_spot_v1(
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
)
