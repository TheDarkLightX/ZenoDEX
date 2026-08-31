"""Deterministic accepted/rejected outcomes for global ABI V2 refinement.

The existing refinement checker remains the normal API producer of accepted
results.  This adapter closes its currently reachable validation failures over
stable wire codes and turns them into an explicit reject-is-no-op value.  Its
underscore token provides API discipline rather than hostile same-process
isolation.  It grants no publication, settlement, verifier, or production
authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias

from .global_economic_proof_v2 import EconomicCommandOccurrenceV2
from .global_economic_state_effect_refinement_v2 import (
    GlobalEconomicStateEffectRefinementCandidateV2,
    GlobalEconomicStateEffectRefinementV2,
    refine_global_economic_state_effects_v2,
)
from .global_settlement_types_v2 import (
    ExternalOutboxEnqueueV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
)

GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2: Final = "NONE"


class GlobalEconomicRefinementRejectCodeV2(str, Enum):
    """Closed Python/Rust wire codes for the current V2 reject surface."""

    MALFORMED_CANDIDATE = "MALFORMED_CANDIDATE"
    EXTERNAL_OUTBOX_REQUIRES_PUBLISHER = "EXTERNAL_OUTBOX_REQUIRES_PUBLISHER"
    ZERO_OCCURRENCE_NOT_STATIC = "ZERO_OCCURRENCE_NOT_STATIC"
    FIXED_CONTEXT_CHANGED = "FIXED_CONTEXT_CHANGED"
    LANE_OWNERSHIP_CHANGED = "LANE_OWNERSHIP_CHANGED"
    DISABLED_LANE_WRITE = "DISABLED_LANE_WRITE"
    LANE_WRITE_COVERAGE_MISMATCH = "LANE_WRITE_COVERAGE_MISMATCH"
    LANE_WRITE_ROOT_MISMATCH = "LANE_WRITE_ROOT_MISMATCH"
    SIGNED_STATE_DELTA_OVERFLOW = "SIGNED_STATE_DELTA_OVERFLOW"
    BALANCES_STATE_EFFECT_MISMATCH = "BALANCES_STATE_EFFECT_MISMATCH"
    CUSTODY_STATE_EFFECT_MISMATCH = "CUSTODY_STATE_EFFECT_MISMATCH"
    LIABILITIES_STATE_EFFECT_MISMATCH = "LIABILITIES_STATE_EFFECT_MISMATCH"
    RESERVES_STATE_EFFECT_MISMATCH = "RESERVES_STATE_EFFECT_MISMATCH"
    SUPPLY_EFFECT_TOTAL_OVERFLOW = "SUPPLY_EFFECT_TOTAL_OVERFLOW"
    SUPPLY_ISSUE_BURN_MISMATCH = "SUPPLY_ISSUE_BURN_MISMATCH"
    OWNED_ACCOUNTING_TOTAL_OVERFLOW = "OWNED_ACCOUNTING_TOTAL_OVERFLOW"
    OWNED_TOTAL_NOT_SUPPLY = "OWNED_TOTAL_NOT_SUPPLY"
    CONSERVATION_ASSET_COVERAGE_MISMATCH = (
        "CONSERVATION_ASSET_COVERAGE_MISMATCH"
    )
    CONSERVATION_STATE_MISMATCH = "CONSERVATION_STATE_MISMATCH"
    ANNOTATION_MIRROR_OVERFLOW = "ANNOTATION_MIRROR_OVERFLOW"
    FEE_ALLOCATION_NOT_MIRRORED = "FEE_ALLOCATION_NOT_MIRRORED"
    REWARD_OR_SLASH_NOT_MIRRORED = "REWARD_OR_SLASH_NOT_MIRRORED"
    ZERO_FEE_CONSERVATION_ROW = "ZERO_FEE_CONSERVATION_ROW"
    FEE_RESIDUE_OVERFLOW = "FEE_RESIDUE_OVERFLOW"
    FEE_RESIDUE_STATE_MISMATCH = "FEE_RESIDUE_STATE_MISMATCH"
    CUSTODY_BACKING_TOTAL_OVERFLOW = "CUSTODY_BACKING_TOTAL_OVERFLOW"
    LIABILITY_TOTAL_OVERFLOW = "LIABILITY_TOTAL_OVERFLOW"
    LIABILITIES_EXCEED_BACKING = "LIABILITIES_EXCEED_BACKING"
    OPEN_TERMINAL_TOTAL_OVERFLOW = "OPEN_TERMINAL_TOTAL_OVERFLOW"
    OPEN_TERMINAL_EXCEEDS_LIABILITY = "OPEN_TERMINAL_EXCEEDS_LIABILITY"
    TERMINAL_LIABILITY_DELTA_OVERFLOW = "TERMINAL_LIABILITY_DELTA_OVERFLOW"
    TERMINAL_PRE_STATE_MISMATCH = "TERMINAL_PRE_STATE_MISMATCH"
    TERMINAL_OWNING_LANE_WRITE_MISSING = "TERMINAL_OWNING_LANE_WRITE_MISSING"
    TERMINAL_PLAN_MISMATCH = "TERMINAL_PLAN_MISMATCH"
    TERMINAL_LIABILITY_MISMATCH = "TERMINAL_LIABILITY_MISMATCH"
    ORACLE_LANE_WRITE_MISSING = "ORACLE_LANE_WRITE_MISSING"
    ORACLE_PRE_STATE_MISMATCH = "ORACLE_PRE_STATE_MISMATCH"
    ORACLE_PLAN_MISMATCH = "ORACLE_PLAN_MISMATCH"
    OCCURRENCES_NOT_ORDERED_UNIQUE = "OCCURRENCES_NOT_ORDERED_UNIQUE"
    REPLAY_CONSUMPTION_MISMATCH = "REPLAY_CONSUMPTION_MISMATCH"
    OCCURRENCE_CONTEXT_MISMATCH = "OCCURRENCE_CONTEXT_MISMATCH"
    REPLAY_ALREADY_CONSUMED = "REPLAY_ALREADY_CONSUMED"
    REPLAY_POST_STATE_MISMATCH = "REPLAY_POST_STATE_MISMATCH"
    HEIGHT_PROGRESSION_MISMATCH = "HEIGHT_PROGRESSION_MISMATCH"
    OCCURRENCE_HEIGHT_MISMATCH = "OCCURRENCE_HEIGHT_MISMATCH"
    INTERNAL_CONTRACT_DRIFT = "INTERNAL_CONTRACT_DRIFT"


ALL_GLOBAL_ECONOMIC_REFINEMENT_REJECT_CODES_V2: Final = tuple(
    GlobalEconomicRefinementRejectCodeV2
)

_CODE_BY_VALIDATION_MESSAGE_V2: Final = {
    "global refinement external outbox requires the O-009 publisher": (
        GlobalEconomicRefinementRejectCodeV2.EXTERNAL_OUTBOX_REQUIRES_PUBLISHER
    ),
    "global refinement zero-occurrence relation must be static": (
        GlobalEconomicRefinementRejectCodeV2.ZERO_OCCURRENCE_NOT_STATIC
    ),
    "global refinement fixed context changed": (
        GlobalEconomicRefinementRejectCodeV2.FIXED_CONTEXT_CHANGED
    ),
    "global refinement lane ownership changed outside migration": (
        GlobalEconomicRefinementRejectCodeV2.LANE_OWNERSHIP_CHANGED
    ),
    "global refinement disabled lane write": (
        GlobalEconomicRefinementRejectCodeV2.DISABLED_LANE_WRITE
    ),
    "global refinement lane write coverage mismatch": (
        GlobalEconomicRefinementRejectCodeV2.LANE_WRITE_COVERAGE_MISMATCH
    ),
    "global refinement lane write root mismatch": (
        GlobalEconomicRefinementRejectCodeV2.LANE_WRITE_ROOT_MISMATCH
    ),
    "global refinement signed state delta exceeds signed 128-bit bounds": (
        GlobalEconomicRefinementRejectCodeV2.SIGNED_STATE_DELTA_OVERFLOW
    ),
    "global refinement balances state/effect mismatch": (
        GlobalEconomicRefinementRejectCodeV2.BALANCES_STATE_EFFECT_MISMATCH
    ),
    "global refinement custody state/effect mismatch": (
        GlobalEconomicRefinementRejectCodeV2.CUSTODY_STATE_EFFECT_MISMATCH
    ),
    "global refinement liabilities state/effect mismatch": (
        GlobalEconomicRefinementRejectCodeV2.LIABILITIES_STATE_EFFECT_MISMATCH
    ),
    "global refinement reserves state/effect mismatch": (
        GlobalEconomicRefinementRejectCodeV2.RESERVES_STATE_EFFECT_MISMATCH
    ),
    "global refinement supply issue/burn mismatch": (
        GlobalEconomicRefinementRejectCodeV2.SUPPLY_ISSUE_BURN_MISMATCH
    ),
    "global owned accounting total exceeds unsigned 128-bit bounds": (
        GlobalEconomicRefinementRejectCodeV2.OWNED_ACCOUNTING_TOTAL_OVERFLOW
    ),
    "global refinement owned total does not equal supply": (
        GlobalEconomicRefinementRejectCodeV2.OWNED_TOTAL_NOT_SUPPLY
    ),
    "global refinement conservation asset coverage mismatch": (
        GlobalEconomicRefinementRejectCodeV2.CONSERVATION_ASSET_COVERAGE_MISMATCH
    ),
    "global refinement conservation state mismatch": (
        GlobalEconomicRefinementRejectCodeV2.CONSERVATION_STATE_MISMATCH
    ),
    "global refinement annotation mirror overflow": (
        GlobalEconomicRefinementRejectCodeV2.ANNOTATION_MIRROR_OVERFLOW
    ),
    "global refinement fee allocation is not mirrored": (
        GlobalEconomicRefinementRejectCodeV2.FEE_ALLOCATION_NOT_MIRRORED
    ),
    "global refinement reward or slash lacks exact state-bearing mirror": (
        GlobalEconomicRefinementRejectCodeV2.REWARD_OR_SLASH_NOT_MIRRORED
    ),
    "global refinement zero fee conservation row is noncanonical": (
        GlobalEconomicRefinementRejectCodeV2.ZERO_FEE_CONSERVATION_ROW
    ),
    "global refinement fee residue state mapping mismatch": (
        GlobalEconomicRefinementRejectCodeV2.FEE_RESIDUE_STATE_MISMATCH
    ),
    "global liability total exceeds unsigned 128-bit bounds": (
        GlobalEconomicRefinementRejectCodeV2.LIABILITY_TOTAL_OVERFLOW
    ),
    "global refinement liabilities exceed accounting backing": (
        GlobalEconomicRefinementRejectCodeV2.LIABILITIES_EXCEED_BACKING
    ),
    "global refinement open terminal obligation total overflows": (
        GlobalEconomicRefinementRejectCodeV2.OPEN_TERMINAL_TOTAL_OVERFLOW
    ),
    "global refinement open terminal obligations exceed exact liability row": (
        GlobalEconomicRefinementRejectCodeV2.OPEN_TERMINAL_EXCEEDS_LIABILITY
    ),
    "global refinement terminal liability delta overflow": (
        GlobalEconomicRefinementRejectCodeV2.TERMINAL_LIABILITY_DELTA_OVERFLOW
    ),
    "global refinement terminal obligation pre-state mismatch": (
        GlobalEconomicRefinementRejectCodeV2.TERMINAL_PRE_STATE_MISMATCH
    ),
    "global refinement terminal obligation lacks its owning lane write": (
        GlobalEconomicRefinementRejectCodeV2.TERMINAL_OWNING_LANE_WRITE_MISSING
    ),
    "global refinement terminal obligation plan mismatch": (
        GlobalEconomicRefinementRejectCodeV2.TERMINAL_PLAN_MISMATCH
    ),
    "global refinement terminal obligation liability mismatch": (
        GlobalEconomicRefinementRejectCodeV2.TERMINAL_LIABILITY_MISMATCH
    ),
    "global refinement Oracle lane write is missing": (
        GlobalEconomicRefinementRejectCodeV2.ORACLE_LANE_WRITE_MISSING
    ),
    "global refinement Oracle occurrence pre-state mismatch": (
        GlobalEconomicRefinementRejectCodeV2.ORACLE_PRE_STATE_MISMATCH
    ),
    "global refinement Oracle occurrence plan mismatch": (
        GlobalEconomicRefinementRejectCodeV2.ORACLE_PLAN_MISMATCH
    ),
    "global refinement occurrences must be ordered and unique": (
        GlobalEconomicRefinementRejectCodeV2.OCCURRENCES_NOT_ORDERED_UNIQUE
    ),
    "global refinement replay consumption mismatch": (
        GlobalEconomicRefinementRejectCodeV2.REPLAY_CONSUMPTION_MISMATCH
    ),
    "global refinement occurrence context mismatch": (
        GlobalEconomicRefinementRejectCodeV2.OCCURRENCE_CONTEXT_MISMATCH
    ),
    "global refinement replay already consumed": (
        GlobalEconomicRefinementRejectCodeV2.REPLAY_ALREADY_CONSUMED
    ),
    "global refinement replay post-state mismatch": (
        GlobalEconomicRefinementRejectCodeV2.REPLAY_POST_STATE_MISMATCH
    ),
    "global refinement height progression mismatch": (
        GlobalEconomicRefinementRejectCodeV2.HEIGHT_PROGRESSION_MISMATCH
    ),
    "global refinement occurrence height mismatch": (
        GlobalEconomicRefinementRejectCodeV2.OCCURRENCE_HEIGHT_MISMATCH
    ),
}

_OUTCOME_TOKEN_V2 = object()


def classify_global_economic_refinement_error_v2(
    error: BaseException,
) -> GlobalEconomicRefinementRejectCodeV2:
    """Classify an exact current checker error, failing closed on message drift."""

    if type(error) not in (TypeError, ValueError):
        return GlobalEconomicRefinementRejectCodeV2.INTERNAL_CONTRACT_DRIFT
    return _CODE_BY_VALIDATION_MESSAGE_V2.get(
        str(error),
        GlobalEconomicRefinementRejectCodeV2.INTERNAL_CONTRACT_DRIFT,
    )


@dataclass(frozen=True, slots=True, init=False)
class GlobalEconomicRefinementAcceptedV2:
    """Accepted outcome carrying the checker's API-conventional result."""

    witness: GlobalEconomicStateEffectRefinementV2

    def __init__(
        self,
        token: object,
        witness: GlobalEconomicStateEffectRefinementV2,
    ) -> None:
        if token is not _OUTCOME_TOKEN_V2:
            raise TypeError("global refinement outcome is adapter-constructed")
        if type(witness) is not GlobalEconomicStateEffectRefinementV2:
            raise TypeError("accepted global refinement witness must be exact")
        object.__setattr__(self, "witness", witness)

    @property
    def production_authority(self) -> str:
        return GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2


@dataclass(frozen=True, slots=True, init=False)
class GlobalEconomicRefinementRejectedV2:
    """Closed rejection whose observable transition is the exact identity."""

    reject_code: GlobalEconomicRefinementRejectCodeV2
    pre_state_root: str
    post_state_root: str

    def __init__(
        self,
        token: object,
        reject_code: GlobalEconomicRefinementRejectCodeV2,
        pre_state_root: str,
    ) -> None:
        if token is not _OUTCOME_TOKEN_V2:
            raise TypeError("global refinement outcome is adapter-constructed")
        if type(reject_code) is not GlobalEconomicRefinementRejectCodeV2:
            raise TypeError("global refinement reject code must be closed")
        object.__setattr__(self, "reject_code", reject_code)
        object.__setattr__(self, "pre_state_root", pre_state_root)
        object.__setattr__(self, "post_state_root", pre_state_root)

    @property
    def effect_plan(self) -> GlobalEconomicEffectPlanV2:
        return GlobalEconomicEffectPlanV2.empty()

    @property
    def terminal_plan(self) -> GlobalTerminalObligationPlanV2:
        return GlobalTerminalObligationPlanV2.empty()

    @property
    def oracle_plan(self) -> GlobalOracleOccurrencePlanV2:
        return GlobalOracleOccurrencePlanV2.empty()

    @property
    def consumed_occurrences(self) -> tuple[EconomicCommandOccurrenceV2, ...]:
        return ()

    @property
    def outbox(self) -> tuple[ExternalOutboxEnqueueV2, ...]:
        return ()

    @property
    def production_authority(self) -> str:
        return GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2


GlobalEconomicRefinementOutcomeV2: TypeAlias = (
    GlobalEconomicRefinementAcceptedV2 | GlobalEconomicRefinementRejectedV2
)


def refine_global_economic_state_effects_outcome_v2(
    candidate: GlobalEconomicStateEffectRefinementCandidateV2,
) -> GlobalEconomicRefinementOutcomeV2:
    """Return acceptance or an exact no-op for expected validation failures.

    Unexpected internal exception classes propagate so programming defects are
    visible while publication remains closed.
    """

    if type(candidate) is not GlobalEconomicStateEffectRefinementCandidateV2:
        raise TypeError("global refinement candidate must be exact")
    owned_candidate = candidate
    pre_state_root = owned_candidate.pre_state.state_root
    try:
        witness = refine_global_economic_state_effects_v2(owned_candidate)
    except (TypeError, ValueError) as error:
        return GlobalEconomicRefinementRejectedV2(
            _OUTCOME_TOKEN_V2,
            classify_global_economic_refinement_error_v2(error),
            pre_state_root,
        )
    return GlobalEconomicRefinementAcceptedV2(_OUTCOME_TOKEN_V2, witness)


__all__ = [
    "GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2",
    "ALL_GLOBAL_ECONOMIC_REFINEMENT_REJECT_CODES_V2",
    "GlobalEconomicRefinementRejectCodeV2",
    "GlobalEconomicRefinementAcceptedV2",
    "GlobalEconomicRefinementRejectedV2",
    "GlobalEconomicRefinementOutcomeV2",
    "classify_global_economic_refinement_error_v2",
    "refine_global_economic_state_effects_outcome_v2",
]
