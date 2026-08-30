"""Closed input and result types for the SHADOW ZDEX buyback route."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias

from .global_economic_authority_head_v1 import GlobalEconomicAuthorityHeadV1
from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    RouteCompositionJournalV1,
)
from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicProfileSnapshotV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    RouteReleaseV1,
    _require_root,
)
from .zdex_atomic_buyback_lane_receipt_v2 import (
    VerifiedZDEXBuybackLaneCompositionV2,
)
from .zdex_atomic_buyback_receipt_verification_v2 import (
    VerifiedZDEXSpotBuybackLeafV2,
    VerifiedZDEXTokenomicsBuybackLeafV2,
)


class ZDEXAtomicBuybackRouteRejectCodeV2(str, Enum):
    PROFILE_MISMATCH = "PROFILE_MISMATCH"
    OCCURRENCE_MISMATCH = "OCCURRENCE_MISMATCH"
    AUTHORITY_MISMATCH = "AUTHORITY_MISMATCH"
    RECEIPT_BINDING_MISMATCH = "RECEIPT_BINDING_MISMATCH"
    TERMINAL_BINDING_MISMATCH = "TERMINAL_BINDING_MISMATCH"
    EFFECT_COMPOSITION_MISMATCH = "EFFECT_COMPOSITION_MISMATCH"
    STATE_REFINEMENT_MISMATCH = "STATE_REFINEMENT_MISMATCH"


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackRouteCandidateV2:
    profile: EconomicProfileSnapshotV1
    route_release: RouteReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    pre_state: GlobalEconomicStateV1
    authority_head: GlobalEconomicAuthorityHeadV1
    verified_spot_leaf: VerifiedZDEXSpotBuybackLeafV2
    verified_tokenomics_leaf: VerifiedZDEXTokenomicsBuybackLeafV2
    verified_spot_lane: VerifiedZDEXBuybackLaneCompositionV2
    verified_tokenomics_lane: VerifiedZDEXBuybackLaneCompositionV2

    def __post_init__(self) -> None:
        expected = (
            (self.profile, EconomicProfileSnapshotV1),
            (self.route_release, RouteReleaseV1),
            (self.occurrence, EconomicCommandOccurrenceV1),
            (self.pre_state, GlobalEconomicStateV1),
            (self.authority_head, GlobalEconomicAuthorityHeadV1),
            (self.verified_spot_leaf, VerifiedZDEXSpotBuybackLeafV2),
            (self.verified_tokenomics_leaf, VerifiedZDEXTokenomicsBuybackLeafV2),
            (self.verified_spot_lane, VerifiedZDEXBuybackLaneCompositionV2),
            (self.verified_tokenomics_lane, VerifiedZDEXBuybackLaneCompositionV2),
        )
        if any(type(value) is not expected_type for value, expected_type in expected):
            raise TypeError("ZDEX atomic buyback route candidate is not closed")


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackRouteAcceptedV2:
    post_state: GlobalEconomicStateV1
    effects: GlobalEconomicEffectPlanV1
    route_journal: RouteCompositionJournalV1
    ordered_leaf_binding_roots: tuple[str, str]
    ordered_lane_assumption_roots: tuple[str, str]
    ordered_lane_binding_roots: tuple[str, str]
    state_delta_root: str
    fee_disposition_root: str

    def __post_init__(self) -> None:
        if type(self.post_state) is not GlobalEconomicStateV1:
            raise TypeError("ZDEX atomic buyback post-state is not closed")
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("ZDEX atomic buyback route effects are not closed")
        if type(self.route_journal) is not RouteCompositionJournalV1:
            raise TypeError("ZDEX atomic buyback route journal is not closed")
        self.effects.validate()
        self.route_journal.__post_init__()
        if (
            self.route_journal.post_state_root != self.post_state.state_root
            or self.route_journal.effect_plan_root != self.effects.effect_plan_root
            or self.route_journal.terminal_obligations_root != ZERO_ROOT_V1
        ):
            raise ValueError("ZDEX atomic buyback accepted bindings disagree")
        for roots in (
            self.ordered_leaf_binding_roots,
            self.ordered_lane_assumption_roots,
            self.ordered_lane_binding_roots,
        ):
            if type(roots) is not tuple or len(roots) != 2:
                raise TypeError("ZDEX atomic buyback binding roots are not closed")
            for root in roots:
                _require_root(root, name="ZDEX atomic buyback binding root")
        _require_root(self.state_delta_root, name="ZDEX atomic buyback state delta")
        _require_root(
            self.fee_disposition_root,
            name="ZDEX atomic buyback fee disposition",
        )


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackRouteRejectedV2:
    code: ZDEXAtomicBuybackRouteRejectCodeV2
    pre_state: GlobalEconomicStateV1
    post_state: GlobalEconomicStateV1
    effects: GlobalEconomicEffectPlanV1 = GlobalEconomicEffectPlanV1.empty()

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXAtomicBuybackRouteRejectCodeV2:
            raise TypeError("ZDEX atomic buyback route reject code is not closed")
        if type(self.pre_state) is not GlobalEconomicStateV1:
            raise TypeError("ZDEX atomic buyback rejected pre-state is not closed")
        if self.post_state is not self.pre_state or not self.effects.is_empty:
            raise ValueError("ZDEX atomic buyback route rejection must be a no-op")


ZDEXAtomicBuybackRouteResultV2: TypeAlias = (
    ZDEXAtomicBuybackRouteAcceptedV2 | ZDEXAtomicBuybackRouteRejectedV2
)


__all__ = [
    "ZDEXAtomicBuybackRouteAcceptedV2",
    "ZDEXAtomicBuybackRouteCandidateV2",
    "ZDEXAtomicBuybackRouteRejectCodeV2",
    "ZDEXAtomicBuybackRouteRejectedV2",
    "ZDEXAtomicBuybackRouteResultV2",
]
