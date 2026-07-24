"""Owned values for the unmounted FCIS spot-step evaluator.

These values are pre-M5 differential evidence.  They are intentionally not a
``DexState``, aggregate ``Decision``, ``CommitPlan``, or ``CommitBundle`` and
cannot authorize publication.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, final

from ..state.state_snapshot_values import (
    CommittedFeeAccumulatorStateV1,
    CommittedNonceTableV1,
    CommittedOracleStateV1,
    CommittedPerpsStateV1,
    CommittedVaultStateV1,
)
from ..state.state_transitions import CanonicalNoncePatchV1
from .settlement_strong_validator import StrongSettlementStateCandidateV1

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
    """One unmounted candidate retaining every exact transition output."""

    spot: StrongSettlementStateCandidateV1
    nonces: CommittedNonceTableV1
    nonce_patch: CanonicalNoncePatchV1 | None
    fee_accumulator: CommittedFeeAccumulatorStateV1
    fee_allocation: FCISFeeAllocationV1 | None
    vault: CommittedVaultStateV1 | None
    oracle: CommittedOracleStateV1 | None
    perps: CommittedPerpsStateV1 | None

    def __post_init__(self) -> None:
        if type(self.spot) is not StrongSettlementStateCandidateV1:
            raise TypeError("step spot candidate must be exact")
        if type(self.nonces) is not CommittedNonceTableV1:
            raise TypeError("step nonce candidate must be exact")
        if self.nonce_patch is not None and type(self.nonce_patch) is not CanonicalNoncePatchV1:
            raise TypeError("step nonce patch must be exact or None")
        if type(self.fee_accumulator) is not CommittedFeeAccumulatorStateV1:
            raise TypeError("step fee-accumulator candidate must be exact")
        if self.fee_allocation is not None and type(self.fee_allocation) is not FCISFeeAllocationV1:
            raise TypeError("step fee allocation must be exact or None")
        if self.vault is not None and type(self.vault) is not CommittedVaultStateV1:
            raise TypeError("step vault candidate must be exact or None")
        if self.oracle is not None and type(self.oracle) is not CommittedOracleStateV1:
            raise TypeError("step Oracle candidate must be exact or None")
        if self.perps is not None and type(self.perps) is not CommittedPerpsStateV1:
            raise TypeError("step perps candidate must be exact or None")


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
    pre_state_root_preimage: bytes
    pre_state_root: str
    post_state_root_preimage: bytes
    post_state_root: str
    snapshot_version: int
    canonical_snapshot_bytes: bytes
    snapshot_commitment: str
    support_root: str

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
            "pre_state_root",
            "post_state_root",
            "snapshot_commitment",
            "support_root",
        ):
            if not _is_digest_v1(object.__getattribute__(self, field_name)):
                raise TypeError(f"{field_name} must be a lowercase 32-byte hex digest")
        if type(self.snapshot_version) is not int or self.snapshot_version <= 0:
            raise TypeError("snapshot version must be an exact positive int")


@final
@dataclass(frozen=True, slots=True)
class FCISStepEvaluationOkV1:
    """One candidate and the evidence derived from that candidate."""

    candidate: FCISStepCandidateV1
    evidence: FCISStepEvaluationEvidenceV1

    def __post_init__(self) -> None:
        if type(self.candidate) is not FCISStepCandidateV1:
            raise TypeError("evaluation candidate must be exact")
        if type(self.evidence) is not FCISStepEvaluationEvidenceV1:
            raise TypeError("evaluation evidence must be exact")


FCISStepEvaluationResultV1: TypeAlias = FCISStepEvaluationOkV1 | FCISStepEvaluationRejectV1


__all__ = (
    "FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1",
    "FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1",
    "FCISFeeAllocationV1",
    "FCISStepCandidateV1",
    "FCISStepEvaluationEvidenceV1",
    "FCISStepEvaluationOkV1",
    "FCISStepEvaluationPhaseV1",
    "FCISStepEvaluationRejectV1",
    "FCISStepEvaluationResultV1",
)
