"""Controlled derivation of one exhaustive FCIS decision from one evaluation.

Decoded M5 claim values remain replay data.  This module is the only place
that may mint the authoritative ``AcceptV1`` and ``RejectV1`` wrappers.  The
current spot profile has no production path to ``CommittedFailureV1``.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from typing import TypeAlias, cast, final

from ..state.canonical import domain_sep_bytes, sha256_hex
from ..state.committed_dex_snapshot import canonical_committed_state_root_binding_v1
from ..state.fcis_committed_state_values import FCISCommittedStateV1
from ..state.fcis_execution_context_codec import encode_fcis_execution_context_v1
from ..state.fcis_execution_context_values import FCIS_STEP_CONTEXT_SCHEMA_ID_V1
from ..state.snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
    MAX_COLLECTION_ITEMS_V1,
    MAX_SORTABLE_KEY_INTEGER_BITS_V1,
    AdmitCode,
    AdmitOk,
    AdmitReject,
    format_admit_path,
)
from ..state.state_transitions import (
    BalancePatchApplyOkV1,
    BalanceWriteV1,
    CanonicalBalancePatchV1,
    CanonicalLPPositionPatchV1,
    CanonicalNoncePatchV1,
    CanonicalPoolPatchV1,
    LPPositionPatchApplyOkV1,
    LPPositionWriteV1,
    NoncePatchApplyOkV1,
    PoolPatchApplyOkV1,
    PoolWriteV1,
    apply_canonical_balance_patch_v1,
    apply_canonical_lp_position_patch_v1,
    apply_canonical_nonce_patch_v1,
    apply_canonical_pool_patch_v1,
)
from .fcis_authority_admission import (
    CanonicalAuthorityClaimBytesV1,
    admit_fcis_authority_claim_v1,
    encode_fcis_authority_claim_v1,
)
from .fcis_decision_values import (
    FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
    FCIS_AUTHORITY_CODEC_VERSION_V1,
    FCIS_AUTHORITY_SCHEMA_VERSION_V1,
    FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1,
    AcceptanceReceiptClaimV1,
    CommittedFailureReceiptClaimV1,
    FCISRejectCodeV1,
    ReceiptBindingClaimV1,
    RejectionPathIndexPartSourceV1,
    RejectionPathTextPartSourceV1,
    RejectionReceiptClaimV1,
    RejectionReceiptSourceV1,
)
from .fcis_step_evaluation_values import (
    FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1,
    FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1,
    FCISStepEvaluationOkV1,
    FCISStepEvaluationPhaseV1,
    FCISStepEvaluationRejectV1,
)
from .fcis_step_evaluator import (
    _evaluate_fcis_step_candidate_bound_v1,
    _FCISStepEvaluationBoundRejectV1,
    evaluate_source_bound_fcis_step_candidate_v1,
)
from .fcis_support_profile_v5 import _command_preimage_v5
from .fcis_transition_budget import (
    FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1,
    MAX_FCIS_CANDIDATES_V1,
    MAX_FCIS_INTENTS_V1,
    MAX_FCIS_OUTBOX_RECORDS_V1,
    TransitionBudgetV1,
)
from .fcis_transition_values import (
    FCIS_COMMIT_PLAN_SCHEMA_ID_V1,
    FCIS_DEX_PATCH_SCHEMA_ID_V1,
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

FCIS_SPOT_TRANSITION_BUDGET_V1 = TransitionBudgetV1(
    max_canonical_input_bytes=MAX_CANONICAL_BYTES_V1,
    max_depth=MAX_ADMISSION_DEPTH_V1,
    max_nodes=MAX_ADMISSION_NODES_V1,
    max_intents=MAX_FCIS_INTENTS_V1,
    max_state_reads=MAX_COLLECTION_ITEMS_V1,
    max_context_reads=MAX_COLLECTION_ITEMS_V1,
    max_patch_writes=MAX_COLLECTION_ITEMS_V1,
    max_effects=MAX_COLLECTION_ITEMS_V1,
    max_outbox_records=MAX_FCIS_OUTBOX_RECORDS_V1,
    max_candidates=MAX_FCIS_CANDIDATES_V1,
    max_witness_bytes=MAX_CANONICAL_BYTES_V1,
    max_receipt_bytes=MAX_CANONICAL_BYTES_V1,
    max_integer_bits=MAX_SORTABLE_KEY_INTEGER_BITS_V1,
)

_DECISION_CONSTRUCTION_TOKEN_V1 = object()


@final
@dataclass(frozen=True, slots=True)
class AcceptV1:
    """One successor, one plan, and one receipt from one evaluator lineage."""

    next_state: FCISCommittedStateV1
    commit_plan: CommitPlanV1
    receipt: AcceptanceReceiptClaimV1
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _DECISION_CONSTRUCTION_TOKEN_V1:
            raise TypeError("AcceptV1 requires controlled derivation")
        if type(self.next_state) is not FCISCommittedStateV1:
            raise TypeError("accepted next_state must be exact")
        if type(self.commit_plan) is not CommitPlanV1:
            raise TypeError("accepted commit_plan must be exact")
        if type(self.receipt) is not AcceptanceReceiptClaimV1:
            raise TypeError("accepted receipt must be exact")


@final
@dataclass(frozen=True, slots=True)
class RejectV1:
    """Ordinary rejection contains one receipt and no committable output."""

    receipt: RejectionReceiptClaimV1
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _DECISION_CONSTRUCTION_TOKEN_V1:
            raise TypeError("RejectV1 requires controlled derivation")
        if type(self.receipt) is not RejectionReceiptClaimV1:
            raise TypeError("rejection receipt must be exact")


@final
@dataclass(frozen=True, slots=True)
class CommittedFailureV1:
    """Reserved exact variant; the current spot profile cannot construct it."""

    next_state: FCISCommittedStateV1
    commit_plan: CommitPlanV1
    receipt: CommittedFailureReceiptClaimV1
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _DECISION_CONSTRUCTION_TOKEN_V1:
            raise TypeError("CommittedFailureV1 requires controlled derivation")
        if type(self.next_state) is not FCISCommittedStateV1:
            raise TypeError("committed-failure next_state must be exact")
        if type(self.commit_plan) is not CommitPlanV1:
            raise TypeError("committed-failure commit_plan must be exact")
        if type(self.receipt) is not CommittedFailureReceiptClaimV1:
            raise TypeError("committed-failure receipt must be exact")


DecisionV1: TypeAlias = AcceptV1 | RejectV1 | CommittedFailureV1


def _claim_root_v1(schema_id: str, value: object) -> tuple[bytes, str]:
    encoded = encode_fcis_authority_claim_v1(schema_id, value)
    if type(encoded) is not CanonicalAuthorityClaimBytesV1:
        raise ValueError(f"canonical encoding rejected for {schema_id}")
    preimage = domain_sep_bytes(schema_id, version=1) + encoded.payload
    return encoded.payload, sha256_hex(preimage)


def _admit_budget_v1(source: object) -> TransitionBudgetV1 | AdmitReject:
    admitted = admit_fcis_authority_claim_v1(FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1, source)
    if type(admitted) is AdmitReject:
        return admitted
    if type(admitted) is not AdmitOk or type(admitted.value) is not TransitionBudgetV1:
        return AdmitReject(code=AdmitCode.DOMAIN_INVARIANT, path=())
    return cast(TransitionBudgetV1, admitted.value)


def _path_sources_v1(
    path: tuple[str | int, ...],
) -> tuple[RejectionPathTextPartSourceV1 | RejectionPathIndexPartSourceV1, ...]:
    result: list[RejectionPathTextPartSourceV1 | RejectionPathIndexPartSourceV1] = []
    for part in path:
        if type(part) is str and part:
            result.append(RejectionPathTextPartSourceV1(part))
        elif type(part) is int and part >= 0:
            result.append(RejectionPathIndexPartSourceV1(part))
        else:
            raise ValueError("rejection path escaped its exact grammar")
    return tuple(result)


def _registered_reject_v1(reject: FCISStepEvaluationRejectV1) -> FCISStepEvaluationRejectV1:
    try:
        FCISRejectCodeV1(reject.code)
        _path_sources_v1(reject.path)
    except ValueError:
        return FCISStepEvaluationRejectV1(
            FCISStepEvaluationPhaseV1.EVIDENCE,
            FCISRejectCodeV1.REGISTRY_DRIFT.value,
            (),
            "FCIS rejection registry drift",
        )
    return reject


def _authoritative_reject_v1(
    reject: FCISStepEvaluationRejectV1,
    *,
    budget_hash: str | None,
    command_root: str | None,
    execution_context_hash: str | None,
    pre_state_root: str | None,
) -> RejectV1:
    exact_reject = _registered_reject_v1(reject)
    source = RejectionReceiptSourceV1(
        algorithm_id=FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1,
        algorithm_version=FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1,
        schema_version=FCIS_AUTHORITY_SCHEMA_VERSION_V1,
        codec_version=FCIS_AUTHORITY_CODEC_VERSION_V1,
        command_or_batch_root=command_root,
        budget_hash=budget_hash,
        execution_context_hash=execution_context_hash,
        pre_state_root=pre_state_root,
        phase=exact_reject.phase,
        code=FCISRejectCodeV1(exact_reject.code),
        path=_path_sources_v1(exact_reject.path),
        public_reason=exact_reject.public_reason,
    )
    admitted = admit_fcis_authority_claim_v1(
        FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1,
        source,
    )
    if type(admitted) is not AdmitOk or type(admitted.value) is not RejectionReceiptClaimV1:
        raise ValueError("controlled rejection receipt admission failed")
    receipt = cast(RejectionReceiptClaimV1, admitted.value)
    _claim_root_v1(FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1, receipt)
    return RejectV1(receipt, _DECISION_CONSTRUCTION_TOKEN_V1)


def _bundle_derivation_reject_v1(
    decision: AcceptV1 | CommittedFailureV1,
) -> RejectV1:
    """Return one canonical no-bundle rejection for internal derivation mismatch."""

    if type(decision) not in (AcceptV1, CommittedFailureV1):
        raise TypeError("bundle rejection requires an exact committable decision")
    binding = decision.receipt.binding
    public = FCISStepEvaluationRejectV1(
        phase=FCISStepEvaluationPhaseV1.EVIDENCE,
        code=FCISRejectCodeV1.CANONICAL_BINDING_REJECTED.value,
        path=("commit_bundle",),
        public_reason="commit bundle derivation rejected",
    )
    return _authoritative_reject_v1(
        public,
        budget_hash=binding.budget_hash,
        command_root=binding.command_or_batch_root,
        execution_context_hash=binding.execution_context_hash,
        pre_state_root=binding.pre_state_root,
    )


def _budget_admission_reject_v1(reject: AdmitReject) -> RejectV1:
    code = reject.code.value
    if code not in {member.value for member in FCISRejectCodeV1}:
        code = FCISRejectCodeV1.REGISTRY_DRIFT.value
    public = FCISStepEvaluationRejectV1(
        FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
        code,
        ("budget", *reject.path),
        f"transition budget admission rejected: {code}:{format_admit_path(reject.path)}",
    )
    return _authoritative_reject_v1(
        public,
        budget_hash=None,
        command_root=None,
        execution_context_hash=None,
        pre_state_root=None,
    )


def _prefix_reject_v1(
    reject: FCISStepEvaluationRejectV1,
    *,
    budget_hash: str,
    evaluation: FCISStepEvaluationOkV1 | _FCISStepEvaluationBoundRejectV1,
) -> RejectV1:
    if type(evaluation) is _FCISStepEvaluationBoundRejectV1:
        return _authoritative_reject_v1(
            reject,
            budget_hash=budget_hash,
            command_root=evaluation.command_root,
            execution_context_hash=evaluation.execution_context_hash,
            pre_state_root=evaluation.pre_state_root,
        )
    evidence = evaluation.evidence
    return _authoritative_reject_v1(
        reject,
        budget_hash=budget_hash,
        command_root=evidence.command_root,
        execution_context_hash=evidence.execution_context_hash,
        pre_state_root=evidence.pre_state_root,
    )


def _verify_balance_writes_v1(
    evaluation: FCISStepEvaluationOkV1,
) -> tuple[BalanceWriteV1, ...]:
    pre = evaluation.material.pre_state.balances
    post = evaluation.candidate.state.balances
    patch = evaluation.candidate.balance_patch
    if patch is None:
        if pre != post:
            raise ValueError("changed balances require a complete patch")
        return ()
    if type(patch) is not CanonicalBalancePatchV1 or pre == post:
        raise ValueError("balance patch is not an exact changed-cell normal form")
    applied = apply_canonical_balance_patch_v1(pre, patch)
    if type(applied) is not BalancePatchApplyOkV1 or applied.state != post:
        raise ValueError("balance patch does not reproduce the successor")
    return cast(tuple[BalanceWriteV1, ...], patch.writes)


def _verify_pool_writes_v1(
    evaluation: FCISStepEvaluationOkV1,
) -> tuple[PoolWriteV1, ...]:
    pre = evaluation.material.pre_state.pools
    post = evaluation.candidate.state.pools
    patch = evaluation.candidate.pool_patch
    if patch is None:
        if pre != post:
            raise ValueError("changed pools require a complete patch")
        return ()
    if type(patch) is not CanonicalPoolPatchV1 or pre == post:
        raise ValueError("pool patch is not an exact changed-cell normal form")
    applied = apply_canonical_pool_patch_v1(pre, patch)
    if type(applied) is not PoolPatchApplyOkV1 or applied.state != post:
        raise ValueError("pool patch does not reproduce the successor")
    return cast(tuple[PoolWriteV1, ...], patch.writes)


def _verify_lp_writes_v1(
    evaluation: FCISStepEvaluationOkV1,
) -> tuple[LPPositionWriteV1, ...]:
    pre = evaluation.material.pre_state.lp_balances
    post = evaluation.candidate.state.lp_balances
    patch = evaluation.candidate.lp_patch
    if patch is None:
        if pre != post:
            raise ValueError("changed LP state requires a complete patch")
        return ()
    if type(patch) is not CanonicalLPPositionPatchV1 or pre == post:
        raise ValueError("LP patch is not an exact changed-cell normal form")
    applied = apply_canonical_lp_position_patch_v1(pre, patch)
    if type(applied) is not LPPositionPatchApplyOkV1 or applied.state != post:
        raise ValueError("LP patch does not reproduce the successor")
    return cast(tuple[LPPositionWriteV1, ...], patch.writes)


def _derive_patch_v1(evaluation: FCISStepEvaluationOkV1) -> CanonicalDexPatchV1:
    pre = evaluation.material.pre_state
    post = evaluation.candidate.state
    balance_writes = _verify_balance_writes_v1(evaluation)
    pool_writes = _verify_pool_writes_v1(evaluation)
    lp_writes = _verify_lp_writes_v1(evaluation)
    fee_write = (
        None
        if pre.fee_accumulator == post.fee_accumulator
        else FeeAccumulatorWriteV1(pre.fee_accumulator, post.fee_accumulator)
    )
    vault_write = None if pre.vault == post.vault else VaultWriteV1(pre.vault, post.vault)
    oracle_write = None if pre.oracle == post.oracle else OracleWriteV1(pre.oracle, post.oracle)
    perps_write = None if pre.perps == post.perps else PerpsWriteV1(pre.perps, post.perps)
    return CanonicalDexPatchV1(
        balance_writes,
        pool_writes,
        lp_writes,
        fee_write,
        vault_write,
        oracle_write,
        perps_write,
    )


def _derive_replay_v1(evaluation: FCISStepEvaluationOkV1) -> ReplayUpdateV1:
    pre = evaluation.material.pre_state.nonces
    post = evaluation.candidate.state.nonces
    patch = evaluation.candidate.nonce_patch
    if patch is None:
        if pre != post:
            raise ValueError("changed nonces require a complete replay patch")
        advances = ()
    else:
        if type(patch) is not CanonicalNoncePatchV1 or pre == post:
            raise ValueError("nonce patch is not an exact changed-cell normal form")
        applied = apply_canonical_nonce_patch_v1(pre, patch)
        if type(applied) is not NoncePatchApplyOkV1 or applied.state != post:
            raise ValueError("nonce patch does not reproduce the successor")
        advances = patch.advances
    nullifiers = tuple(
        sorted(
            (
                NullifierRecordV1(intent.sender_pubkey, intent.intent_id)
                for intent in evaluation.material.intents
            ),
            key=lambda record: (record.pubkey, record.intent_id),
        )
    )
    return ReplayUpdateV1(advances, nullifiers)


def _derive_plan_v1(evaluation: FCISStepEvaluationOkV1) -> CommitPlanV1:
    settlement = evaluation.material.settlement
    total_fees = sum(0 if fill.fee_paid is None else fill.fee_paid for fill in settlement.fills)
    effects = OwnedDexEffectsV1(
        settlement,
        total_fees,
        evaluation.candidate.fee_allocation,
    )
    return CommitPlanV1(
        _derive_patch_v1(evaluation),
        effects,
        _derive_replay_v1(evaluation),
    )


def _revalidate_evaluation_v1(evaluation: FCISStepEvaluationOkV1) -> None:
    if type(evaluation) is not FCISStepEvaluationOkV1:
        raise TypeError("decision derivation requires an exact evaluation")
    material = evaluation.material
    candidate = evaluation.candidate
    evidence = evaluation.evidence
    _, pre_preimage, pre_root = canonical_committed_state_root_binding_v1(
        material.pre_state,
        material.context.snapshot_version,
    )
    snapshot_bytes, post_preimage, post_root = canonical_committed_state_root_binding_v1(
        candidate.state,
        material.context.snapshot_version,
    )
    context_bytes = encode_fcis_execution_context_v1(
        FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
        material.context,
    )
    context_hash = sha256_hex(
        domain_sep_bytes("fcis_step_execution_context", version=1) + context_bytes
    )
    command_root = sha256_hex(_command_preimage_v5(material.settlement, material.intents))
    if (
        evidence.execution_context_bytes != context_bytes
        or evidence.execution_context_hash != context_hash
        or evidence.command_root != command_root
        or evidence.pre_state_root_preimage != pre_preimage
        or evidence.pre_state_root != pre_root
        or evidence.post_state_root_preimage != post_preimage
        or evidence.post_state_root != post_root
        or evidence.canonical_snapshot_bytes != snapshot_bytes
        or evidence.snapshot_commitment != post_root
    ):
        raise ValueError("evaluation evidence does not match its retained lineage")


def _effect_count_v1(evaluation: FCISStepEvaluationOkV1) -> int:
    settlement = evaluation.material.settlement
    return (
        len(settlement.fills)
        + len(settlement.balance_deltas)
        + len(settlement.reserve_deltas)
        + len(settlement.lp_deltas)
        + _observed_outbox_records_v1(evaluation)
    )


def _observed_outbox_records_v1(evaluation: FCISStepEvaluationOkV1) -> int:
    """Count retained settlement events that will become outbox records."""

    events = evaluation.material.settlement.events
    return 0 if events is None else len(events)


def _budget_violation_v1(
    evaluation: FCISStepEvaluationOkV1,
    plan: CommitPlanV1,
    budget: TransitionBudgetV1,
) -> str | None:
    evidence = evaluation.evidence
    if budget.max_depth != MAX_ADMISSION_DEPTH_V1:
        return "max_depth"
    if budget.max_nodes != MAX_ADMISSION_NODES_V1:
        return "max_nodes"
    if budget.max_integer_bits != MAX_SORTABLE_KEY_INTEGER_BITS_V1:
        return "max_integer_bits"
    checks = (
        (
            "max_canonical_input_bytes",
            evidence.canonical_input_bytes,
            budget.max_canonical_input_bytes,
        ),
        ("max_intents", len(evaluation.material.intents), budget.max_intents),
        ("max_state_reads", evidence.state_read_count, budget.max_state_reads),
        ("max_context_reads", evidence.context_read_count, budget.max_context_reads),
        (
            "max_patch_writes",
            len(plan.patch.balance_writes)
            + len(plan.patch.pool_writes)
            + len(plan.patch.lp_writes)
            + sum(
                write is not None
                for write in (
                    plan.patch.fee_accumulator_write,
                    plan.patch.vault_write,
                    plan.patch.oracle_write,
                    plan.patch.perps_write,
                )
            )
            + len(plan.replay.nonce_advances),
            budget.max_patch_writes,
        ),
        ("max_effects", _effect_count_v1(evaluation), budget.max_effects),
        (
            "max_outbox_records",
            _observed_outbox_records_v1(evaluation),
            budget.max_outbox_records,
        ),
        ("max_candidates", 1, budget.max_candidates),
        ("max_witness_bytes", evidence.witness_bytes, budget.max_witness_bytes),
    )
    for field_name, observed, limit in checks:
        if observed > limit:
            return field_name
    return None


def _budget_reject_v1(
    evaluation: FCISStepEvaluationOkV1,
    budget_hash: str,
    field_name: str,
) -> RejectV1:
    reject = FCISStepEvaluationRejectV1(
        FCISStepEvaluationPhaseV1.EVIDENCE,
        FCISRejectCodeV1.BUDGET_EXCEEDED.value,
        ("budget", field_name),
        f"transition budget exceeded: {field_name}",
    )
    return _prefix_reject_v1(reject, budget_hash=budget_hash, evaluation=evaluation)


def _derive_accept_v1(
    evaluation: FCISStepEvaluationOkV1,
    budget: TransitionBudgetV1,
    budget_hash: str,
) -> DecisionV1:
    try:
        _revalidate_evaluation_v1(evaluation)
        plan = _derive_plan_v1(evaluation)
        violation = _budget_violation_v1(evaluation, plan, budget)
        if violation is not None:
            return _budget_reject_v1(evaluation, budget_hash, violation)
        _, patch_root = _claim_root_v1(FCIS_DEX_PATCH_SCHEMA_ID_V1, plan.patch)
        _, plan_root = _claim_root_v1(FCIS_COMMIT_PLAN_SCHEMA_ID_V1, plan)
        evidence = evaluation.evidence
        binding = ReceiptBindingClaimV1(
            algorithm_id=evidence.algorithm_id,
            algorithm_version=evidence.algorithm_version,
            schema_version=FCIS_AUTHORITY_SCHEMA_VERSION_V1,
            codec_version=FCIS_AUTHORITY_CODEC_VERSION_V1,
            execution_context_hash=evidence.execution_context_hash,
            command_or_batch_root=evidence.command_root,
            budget_hash=budget_hash,
            pre_state_root=evidence.pre_state_root,
            next_state_root=evidence.post_state_root,
            support_root_version=evidence.support_root_version,
            support_root=evidence.support_root,
            support_set_commitment=evidence.support_set_commitment,
            snapshot_version=evidence.snapshot_version,
            snapshot_commitment=evidence.snapshot_commitment,
            patch_root=patch_root,
            commit_plan_root=plan_root,
        )
        receipt = AcceptanceReceiptClaimV1(binding)
        receipt_bytes, _receipt_root = _claim_root_v1(
            FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
            receipt,
        )
        if len(receipt_bytes) > budget.max_receipt_bytes:
            return _budget_reject_v1(evaluation, budget_hash, "max_receipt_bytes")
        return AcceptV1(
            evaluation.candidate.state,
            plan,
            receipt,
            _DECISION_CONSTRUCTION_TOKEN_V1,
        )
    except (TypeError, ValueError):
        reject = FCISStepEvaluationRejectV1(
            FCISStepEvaluationPhaseV1.EVIDENCE,
            FCISRejectCodeV1.PATCH_REJECTED.value,
            (),
            "FCIS same-candidate derivation rejected",
        )
        return _prefix_reject_v1(reject, budget_hash=budget_hash, evaluation=evaluation)


def evaluate_source_bound_fcis_decision_v1(
    *,
    source_occurrence: object,
    budget: object,
) -> DecisionV1:
    """Derive the controlled decision from one verified source-bound evaluation."""

    admitted_budget = _admit_budget_v1(budget)
    if type(admitted_budget) is AdmitReject:
        return _budget_admission_reject_v1(admitted_budget)
    exact_budget = admitted_budget
    try:
        _, budget_hash = _claim_root_v1(
            FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1,
            exact_budget,
        )
    except (TypeError, ValueError):
        synthetic = AdmitReject(code=AdmitCode.DOMAIN_INVARIANT, path=())
        return _budget_admission_reject_v1(synthetic)
    evaluation = evaluate_source_bound_fcis_step_candidate_v1(
        source_occurrence=source_occurrence,
    )
    if type(evaluation) is FCISStepEvaluationRejectV1:
        public = FCISStepEvaluationRejectV1(
            evaluation.phase,
            FCISRejectCodeV1.CANONICAL_EVIDENCE_REJECTED.value,
            evaluation.path,
            evaluation.public_reason,
        )
        return _authoritative_reject_v1(
            public,
            budget_hash=budget_hash,
            command_root=None,
            execution_context_hash=None,
            pre_state_root=None,
        )
    return _derive_accept_v1(evaluation, exact_budget, budget_hash)


def evaluate_fcis_decision_v1(
    *,
    state_source: object,
    settlement: object,
    intents: object,
    context: object,
    budget: object,
) -> DecisionV1:
    """Return exactly one authoritative decision and never a partial candidate."""

    admitted_budget = _admit_budget_v1(budget)
    if type(admitted_budget) is AdmitReject:
        return _budget_admission_reject_v1(admitted_budget)
    exact_budget = admitted_budget
    try:
        _, budget_hash = _claim_root_v1(
            FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1,
            exact_budget,
        )
    except (TypeError, ValueError):
        synthetic = AdmitReject(code=AdmitCode.DOMAIN_INVARIANT, path=())
        return _budget_admission_reject_v1(synthetic)
    evaluation = _evaluate_fcis_step_candidate_bound_v1(
        state_source=state_source,
        settlement=settlement,
        intents=intents,
        context=context,
    )
    if type(evaluation) is _FCISStepEvaluationBoundRejectV1:
        return _prefix_reject_v1(
            evaluation.reject,
            budget_hash=budget_hash,
            evaluation=evaluation,
        )
    return _derive_accept_v1(evaluation, exact_budget, budget_hash)


def acceptance_receipt_root_v1(decision: AcceptV1) -> str:
    """Revalidate and hash the exact receipt inside one controlled acceptance."""

    if type(decision) is not AcceptV1:
        raise TypeError("receipt root requires an exact AcceptV1")
    _payload, root = _claim_root_v1(
        FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
        decision.receipt,
    )
    return root


__all__ = (
    "AcceptV1",
    "CommittedFailureV1",
    "DecisionV1",
    "FCIS_SPOT_TRANSITION_BUDGET_V1",
    "RejectV1",
    "acceptance_receipt_root_v1",
    "evaluate_source_bound_fcis_decision_v1",
    "evaluate_fcis_decision_v1",
)
