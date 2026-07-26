"""Owned values for the unmounted FCIS spot-step evaluator.

The evaluation result retains the exact admitted command, context, pre-state,
successor, and evidence as one immutable lineage. Its controlled constructor is
a misuse barrier. M5 must still re-evaluate this unmounted result before using
it as authority.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import TypeAlias, final

from ..state.fcis_committed_state_values import FCISCommittedStateV1
from ..state.fcis_execution_context_values import FCISStepExecutionContextV1
from ..state.intent_snapshots import OwnedIntentV1
from ..state.state_transitions import (
    CanonicalBalancePatchV1,
    CanonicalLPPositionPatchV1,
    CanonicalNoncePatchV1,
    CanonicalPoolPatchV1,
)
from .fcis_support_profile_constants_v5 import (
    FCIS_SUPPORT_PROFILE_ID_V5,
    FCIS_SUPPORT_PROFILE_VERSION_V5,
)
from .settlement_snapshots import OwnedSettlementV1

FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1 = "zenodex/fcis/spot-step-evaluator/v1"
FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1 = 1


class FCISStepEvaluationPhaseV1(Enum):
    """Stable phase order for one no-candidate evaluator rejection."""

    COMMAND_ADMISSION = "command_admission"
    CONTEXT_ADMISSION = "context_admission"
    STATE_ADMISSION = "state_admission"
    PRE_STATE_BINDING = "pre_state_binding"
    NONCE = "nonce"
    SETTLEMENT = "settlement"
    FEE = "fee"
    EVIDENCE = "evidence"


@final
@dataclass(frozen=True, slots=True)
class FCISStepEvaluationRejectV1:
    """Typed rejection carrying no candidate or success evidence."""

    phase: FCISStepEvaluationPhaseV1
    code: str
    path: tuple[str | int, ...]
    public_reason: str

    def __post_init__(self) -> None:
        if type(self.phase) is not FCISStepEvaluationPhaseV1:
            raise TypeError("evaluation rejection phase must be exact")
        if type(self.code) is not str or not self.code:
            raise TypeError("evaluation rejection code must be an exact nonempty string")
        if type(self.path) is not tuple or any(type(part) not in (str, int) for part in self.path):
            raise TypeError("evaluation rejection path must contain exact strings or ints")
        if type(self.public_reason) is not str or not self.public_reason:
            raise TypeError("evaluation public reason must be an exact nonempty string")


@final
@dataclass(frozen=True, slots=True)
class FCISFeeAllocationV1:
    """Exact fee-allocation data retained from the evaluated fee candidate."""

    buyback_amount: int
    treasury_amount: int
    rewards_amount: int
    dust_carried: int

    def __post_init__(self) -> None:
        amounts = (
            self.buyback_amount,
            self.treasury_amount,
            self.rewards_amount,
            self.dust_carried,
        )
        if any(type(amount) is not int or amount < 0 for amount in amounts):
            raise TypeError("fee allocation amounts must be exact nonnegative ints")


@final
@dataclass(frozen=True, slots=True)
class FCISStepCandidateV1:
    """One successor plus every canonical patch produced by its evaluation."""

    state: FCISCommittedStateV1
    balance_patch: CanonicalBalancePatchV1 | None
    pool_patch: CanonicalPoolPatchV1 | None
    lp_patch: CanonicalLPPositionPatchV1 | None
    nonce_patch: CanonicalNoncePatchV1 | None
    fee_allocation: FCISFeeAllocationV1 | None

    def __post_init__(self) -> None:
        if type(self.state) is not FCISCommittedStateV1:
            raise TypeError("step successor state must be exact")
        if (
            self.balance_patch is not None
            and type(self.balance_patch) is not CanonicalBalancePatchV1
        ):
            raise TypeError("step balance patch must be exact or None")
        if self.pool_patch is not None and type(self.pool_patch) is not CanonicalPoolPatchV1:
            raise TypeError("step pool patch must be exact or None")
        if self.lp_patch is not None and type(self.lp_patch) is not CanonicalLPPositionPatchV1:
            raise TypeError("step LP patch must be exact or None")
        if self.nonce_patch is not None and type(self.nonce_patch) is not CanonicalNoncePatchV1:
            raise TypeError("step nonce patch must be exact or None")
        if self.fee_allocation is not None and type(self.fee_allocation) is not FCISFeeAllocationV1:
            raise TypeError("step fee allocation must be exact or None")


@final
@dataclass(frozen=True, slots=True)
class FCISEvaluatedMaterialV1:
    """Exact admitted inputs retained for same-lineage downstream derivation."""

    pre_state: FCISCommittedStateV1
    settlement: OwnedSettlementV1
    intents: tuple[OwnedIntentV1, ...]
    context: FCISStepExecutionContextV1

    def __post_init__(self) -> None:
        if type(self.pre_state) is not FCISCommittedStateV1:
            raise TypeError("evaluated pre-state must be exact")
        if type(self.settlement) is not OwnedSettlementV1:
            raise TypeError("evaluated settlement must be exact")
        if type(self.intents) is not tuple or any(
            type(intent) is not OwnedIntentV1 for intent in self.intents
        ):
            raise TypeError("evaluated intents must be an exact owned tuple")
        if type(self.context) is not FCISStepExecutionContextV1:
            raise TypeError("evaluated context must be exact")


def _is_digest_v1(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 66
        and value.startswith("0x")
        and all(character in "0123456789abcdef" for character in value[2:])
    )


@final
@dataclass(frozen=True, slots=True)
class FCISStepEvaluationEvidenceV1:
    """Canonical evidence derived from the same accepted local candidate."""

    algorithm_id: str
    algorithm_version: int
    execution_context_bytes: bytes
    execution_context_hash: str
    command_root: str
    pre_state_root_preimage: bytes
    pre_state_root: str
    post_state_root_preimage: bytes
    post_state_root: str
    snapshot_version: int
    canonical_snapshot_bytes: bytes
    snapshot_commitment: str
    support_root_version: int
    support_profile_id: str
    support_set_commitment: str
    support_root: str
    canonical_input_bytes: int
    state_read_count: int
    context_read_count: int
    witness_bytes: int

    def __post_init__(self) -> None:
        if self.algorithm_id != FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1:
            raise ValueError("unexpected FCIS step evaluator algorithm")
        if self.algorithm_version != FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1:
            raise ValueError("unexpected FCIS step evaluator version")
        for field_name in (
            "execution_context_bytes",
            "pre_state_root_preimage",
            "post_state_root_preimage",
            "canonical_snapshot_bytes",
        ):
            if type(object.__getattribute__(self, field_name)) is not bytes:
                raise TypeError(f"{field_name} must be exact bytes")
        for field_name in (
            "execution_context_hash",
            "command_root",
            "pre_state_root",
            "post_state_root",
            "snapshot_commitment",
            "support_set_commitment",
            "support_root",
        ):
            if not _is_digest_v1(object.__getattribute__(self, field_name)):
                raise TypeError(f"{field_name} must be a lowercase 32-byte hex digest")
        if type(self.snapshot_version) is not int or self.snapshot_version <= 0:
            raise TypeError("snapshot version must be an exact positive int")
        if self.support_root_version != FCIS_SUPPORT_PROFILE_VERSION_V5:
            raise ValueError("unexpected FCIS exact support-root version")
        if self.support_profile_id != FCIS_SUPPORT_PROFILE_ID_V5:
            raise ValueError("unexpected FCIS support profile")
        if type(self.canonical_input_bytes) is not int or self.canonical_input_bytes <= 0:
            raise TypeError("canonical_input_bytes must be an exact positive int")
        for field_name in (
            "state_read_count",
            "context_read_count",
            "witness_bytes",
        ):
            value = object.__getattribute__(self, field_name)
            if type(value) is not int or value < 0:
                raise TypeError(f"{field_name} must be an exact nonnegative int")
        if self.witness_bytes == 0:
            raise ValueError("witness_bytes must account for support evidence")


_EVALUATION_OK_CONSTRUCTION_TOKEN_V1 = object()


@final
@dataclass(frozen=True, slots=True)
class FCISStepEvaluationOkV1:
    """One exact input lineage, candidate, and evidence derived from both."""

    material: FCISEvaluatedMaterialV1
    candidate: FCISStepCandidateV1
    evidence: FCISStepEvaluationEvidenceV1
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _EVALUATION_OK_CONSTRUCTION_TOKEN_V1:
            raise TypeError("evaluation success requires the controlled constructor")
        if type(self.material) is not FCISEvaluatedMaterialV1:
            raise TypeError("evaluation material must be exact")
        if type(self.candidate) is not FCISStepCandidateV1:
            raise TypeError("evaluation candidate must be exact")
        if type(self.evidence) is not FCISStepEvaluationEvidenceV1:
            raise TypeError("evaluation evidence must be exact")


def _evaluation_ok_from_evaluator_v1(
    material: FCISEvaluatedMaterialV1,
    candidate: FCISStepCandidateV1,
    evidence: FCISStepEvaluationEvidenceV1,
) -> FCISStepEvaluationOkV1:
    """Package one success inside the evaluator module boundary."""

    return FCISStepEvaluationOkV1(
        material,
        candidate,
        evidence,
        _EVALUATION_OK_CONSTRUCTION_TOKEN_V1,
    )


FCISStepEvaluationResultV1: TypeAlias = FCISStepEvaluationOkV1 | FCISStepEvaluationRejectV1

__all__ = (
    "FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1",
    "FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1",
    "FCISEvaluatedMaterialV1",
    "FCISFeeAllocationV1",
    "FCISStepCandidateV1",
    "FCISStepEvaluationEvidenceV1",
    "FCISStepEvaluationOkV1",
    "FCISStepEvaluationPhaseV1",
    "FCISStepEvaluationRejectV1",
    "FCISStepEvaluationResultV1",
)
