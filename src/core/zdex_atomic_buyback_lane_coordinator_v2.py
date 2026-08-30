"""SHADOW lane coordinators for the authenticated ZDEX buyback successors.

The module leaves retain their frozen, policy-local effect vocabularies.  These
coordinators convert those effects into the GlobalSettlementABI V1 state-bearing
vocabulary and bind one profile-selected coordinator journal per lane.  The
results remain deterministic data and carry no receipt or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias

from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    LaneCompositionJournalV1,
)
from .global_economic_refinement_snapshot_v1 import _snapshot_occurrence_v1
from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    _require_root,
    hash_global_v1,
)
from .zdex_atomic_buyback_receipt_verification_v2 import (
    VerifiedZDEXSpotBuybackLeafV2,
    VerifiedZDEXTokenomicsBuybackLeafV2,
    snapshot_verified_zdex_spot_buyback_leaf_v2,
    snapshot_verified_zdex_tokenomics_buyback_leaf_v2,
)
from .zdex_purchase_burn_route_types_v1 import AMM_POOL_CUSTODY_DOMAIN_V1


class ZDEXBuybackLaneCoordinatorRejectCodeV2(str, Enum):
    PROFILE_MISMATCH = "PROFILE_MISMATCH"
    OCCURRENCE_MISMATCH = "OCCURRENCE_MISMATCH"
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    EFFECT_SHAPE_MISMATCH = "EFFECT_SHAPE_MISMATCH"


def zdex_buyback_terminal_set_root_v2(obligation_ids: tuple[str, ...]) -> str:
    if type(obligation_ids) is not tuple or any(
        type(value) is not str for value in obligation_ids
    ):
        raise TypeError("ZDEX buyback terminal set must be an exact tuple of roots")
    if obligation_ids != tuple(sorted(set(obligation_ids))):
        raise ValueError("ZDEX buyback terminal set must be sorted and unique")
    for obligation_id in obligation_ids:
        _require_root(obligation_id, name="ZDEX buyback terminal obligation")
    if not obligation_ids:
        return ZERO_ROOT_V1
    return hash_global_v1(
        "zdex-buyback-terminal-set-v2",
        {"obligation_ids": obligation_ids},
    )


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackLaneCandidateV2:
    profile: EconomicProfileSnapshotV1
    occurrence: EconomicCommandOccurrenceV1
    verified_leaf: VerifiedZDEXSpotBuybackLeafV2

    def __post_init__(self) -> None:
        if (
            type(self.profile) is not EconomicProfileSnapshotV1
            or type(self.occurrence) is not EconomicCommandOccurrenceV1
            or type(self.verified_leaf) is not VerifiedZDEXSpotBuybackLeafV2
        ):
            raise TypeError("Spot buyback lane candidate requires exact typed data")


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackLaneCandidateV2:
    profile: EconomicProfileSnapshotV1
    occurrence: EconomicCommandOccurrenceV1
    verified_leaf: VerifiedZDEXTokenomicsBuybackLeafV2

    def __post_init__(self) -> None:
        if (
            type(self.profile) is not EconomicProfileSnapshotV1
            or type(self.occurrence) is not EconomicCommandOccurrenceV1
            or type(self.verified_leaf) is not VerifiedZDEXTokenomicsBuybackLeafV2
        ):
            raise TypeError("Tokenomics buyback lane candidate requires exact typed data")


@dataclass(frozen=True, slots=True)
class ZDEXBuybackLaneCompositionAcceptedV2:
    effects: GlobalEconomicEffectPlanV1
    lane_journal: LaneCompositionJournalV1
    leaf_assumption_root: str
    leaf_binding_root: str
    outstanding_terminal_obligations: tuple[str, ...]
    discharged_terminal_obligations: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("ZDEX buyback lane effects must be exact typed data")
        if type(self.lane_journal) is not LaneCompositionJournalV1:
            raise TypeError("ZDEX buyback lane journal must be exact typed data")
        self.effects.validate()
        self.lane_journal.validate()
        for name in ("leaf_assumption_root", "leaf_binding_root"):
            value = object.__getattribute__(self, name)
            if type(value) is not str:
                raise TypeError(f"ZDEX buyback lane {name} must be exact str")
            _require_root(value, name=f"ZDEX buyback lane {name}")
        for obligations in (
            self.outstanding_terminal_obligations,
            self.discharged_terminal_obligations,
        ):
            zdex_buyback_terminal_set_root_v2(obligations)
        writes = self.effects.lane_writes
        if (
            len(writes) != 1
            or writes[0].lane_id is not self.lane_journal.lane_id
            or writes[0].pre_root != self.lane_journal.pre_lane_root
            or writes[0].post_root != self.lane_journal.post_lane_root
            or self.lane_journal.effect_plan_root != self.effects.effect_plan_root
            or self.lane_journal.terminal_obligations_root
            != zdex_buyback_terminal_set_root_v2(
                self.outstanding_terminal_obligations
            )
        ):
            raise ValueError("ZDEX buyback lane composition bindings disagree")


@dataclass(frozen=True, slots=True)
class ZDEXBuybackLaneCompositionRejectedV2:
    code: ZDEXBuybackLaneCoordinatorRejectCodeV2
    effects: GlobalEconomicEffectPlanV1 = GlobalEconomicEffectPlanV1.empty()

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXBuybackLaneCoordinatorRejectCodeV2:
            raise TypeError("ZDEX buyback lane reject code is not closed")
        if type(self.effects) is not GlobalEconomicEffectPlanV1 or not self.effects.is_empty:
            raise ValueError("ZDEX buyback lane rejection must have no effects")


ZDEXBuybackLaneCompositionResultV2: TypeAlias = (
    ZDEXBuybackLaneCompositionAcceptedV2 | ZDEXBuybackLaneCompositionRejectedV2
)


def _checked_delta_v2(value: int) -> int:
    if not MIN_DELTA_ATOMS_V1 <= value <= MAX_DELTA_ATOMS_V1:
        raise ValueError("ZDEX buyback coordinated effect exceeds signed i128")
    return value


def _materialize_fee_allocations_v2(
    effects: GlobalEconomicEffectPlanV1,
) -> GlobalEconomicEffectPlanV1:
    totals: dict[tuple[str, str, str, str], tuple[EconomicEffectRowV1, int]] = {}
    for row in effects.rows:
        additions: tuple[EconomicEffectRowV1, ...] = (row,)
        if row.kind is EconomicEffectKindV1.FEE_ALLOCATION:
            additions = (
                row,
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    row.principal,
                    row.asset,
                    row.custody_domain,
                    row.delta_atoms,
                ),
            )
        for addition in additions:
            exemplar, prior = totals.get(addition.key, (addition, 0))
            totals[addition.key] = (
                exemplar,
                _checked_delta_v2(prior + addition.delta_atoms),
            )
    rows = tuple(
        EconomicEffectRowV1(
            exemplar.kind,
            exemplar.principal,
            exemplar.asset,
            exemplar.custody_domain,
            total,
        )
        for _, (exemplar, total) in sorted(totals.items())
        if total != 0
    )
    return GlobalEconomicEffectPlanV1(
        rows,
        effects.asset_conservation,
        effects.fee_conservation,
        effects.lane_writes,
        effects.occurrence_consumptions,
        effects.external_outbox_enqueue,
    )


def _materialize_spot_custody_v2(
    effects: GlobalEconomicEffectPlanV1,
) -> GlobalEconomicEffectPlanV1:
    if len(effects.rows) != 2 or any(
        row.kind is not EconomicEffectKindV1.ACCOUNT_MOVEMENT
        or row.custody_domain != AMM_POOL_CUSTODY_DOMAIN_V1
        for row in effects.rows
    ):
        raise ValueError("Spot buyback coordinated effects have an unexpected shape")
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    row.principal,
                    row.asset,
                    row.custody_domain,
                    row.delta_atoms,
                )
                for row in effects.rows
            ),
            key=lambda row: row.key,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows,
        effects.asset_conservation,
        effects.fee_conservation,
        effects.lane_writes,
        effects.occurrence_consumptions,
        effects.external_outbox_enqueue,
    )


def _profile_reject_code_v2(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    verified_leaf: VerifiedZDEXSpotBuybackLeafV2
    | VerifiedZDEXTokenomicsBuybackLeafV2,
    lane_id: LaneIdV1,
) -> ZDEXBuybackLaneCoordinatorRejectCodeV2 | None:
    if (
        profile.status is not ProfileStatusV1.SHADOW
        or profile.profile_id != verified_leaf.profile_root
        or profile.authority_epoch != verified_leaf.writer_epoch
    ):
        return ZDEXBuybackLaneCoordinatorRejectCodeV2.PROFILE_MISMATCH
    if (
        occurrence.profile_root != verified_leaf.profile_root
        or occurrence.occurrence_id != verified_leaf.command_occurrence_id
    ):
        return ZDEXBuybackLaneCoordinatorRejectCodeV2.OCCURRENCE_MISMATCH
    release = profile.lane_registry.release_for(lane_id)
    coordinator = profile.lane_coordinator_registry.release_for(lane_id)
    if (
        release.release_id != verified_leaf.module_release_id
        or release.status is not ReleaseStatusV1.SHADOW
        or release.accepts_new_objects
        or coordinator.status is not ReleaseStatusV1.SHADOW
        or coordinator.accepts_new_objects
    ):
        return ZDEXBuybackLaneCoordinatorRejectCodeV2.RELEASE_MISMATCH
    return None


def _accepted_lane_v2(
    *,
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    lane_id: LaneIdV1,
    leaf_journal_root: str,
    leaf_assumption_root: str,
    leaf_binding_root: str,
    effects: GlobalEconomicEffectPlanV1,
    outstanding: tuple[str, ...],
    discharged: tuple[str, ...],
) -> ZDEXBuybackLaneCompositionAcceptedV2:
    write = effects.lane_writes[0]
    coordinator = profile.lane_coordinator_registry.release_for(lane_id)
    lane_journal = LaneCompositionJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=profile.authority_epoch,
        lane_id=lane_id,
        coordinator_release_id=coordinator.coordinator_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        ordered_module_journal_roots=(leaf_journal_root,),
        pre_lane_root=write.pre_root,
        post_lane_root=write.post_root,
        effect_plan_root=effects.effect_plan_root,
        terminal_obligations_root=zdex_buyback_terminal_set_root_v2(outstanding),
    )
    return ZDEXBuybackLaneCompositionAcceptedV2(
        effects,
        lane_journal,
        leaf_assumption_root,
        leaf_binding_root,
        outstanding,
        discharged,
    )


def compose_zdex_spot_buyback_lane_shadow_v2(
    candidate: ZDEXSpotBuybackLaneCandidateV2,
) -> ZDEXBuybackLaneCompositionResultV2:
    if type(candidate) is not ZDEXSpotBuybackLaneCandidateV2:
        raise TypeError("Spot buyback lane candidate must be exact typed data")
    candidate.__post_init__()
    profile = snapshot_economic_profile_v1(candidate.profile)
    occurrence = _snapshot_occurrence_v1(candidate.occurrence)
    verified = candidate.verified_leaf
    code = _profile_reject_code_v2(
        profile,
        occurrence,
        verified,
        LaneIdV1.SPOT_LIQUIDITY,
    )
    if code is not None:
        return ZDEXBuybackLaneCompositionRejectedV2(code)
    leaf = snapshot_verified_zdex_spot_buyback_leaf_v2(verified)
    try:
        effects = _materialize_spot_custody_v2(leaf.effects)
    except ValueError:
        return ZDEXBuybackLaneCompositionRejectedV2(
            ZDEXBuybackLaneCoordinatorRejectCodeV2.EFFECT_SHAPE_MISMATCH
        )
    return _accepted_lane_v2(
        profile=profile,
        occurrence=occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        leaf_journal_root=leaf.journal_root,
        leaf_assumption_root=verified.assumption_root,
        leaf_binding_root=verified.binding_root,
        effects=effects,
        outstanding=(leaf.journal.terminal_obligation_id,),
        discharged=(),
    )


def compose_zdex_tokenomics_buyback_lane_shadow_v2(
    candidate: ZDEXTokenomicsBuybackLaneCandidateV2,
) -> ZDEXBuybackLaneCompositionResultV2:
    if type(candidate) is not ZDEXTokenomicsBuybackLaneCandidateV2:
        raise TypeError("Tokenomics buyback lane candidate must be exact typed data")
    candidate.__post_init__()
    profile = snapshot_economic_profile_v1(candidate.profile)
    occurrence = _snapshot_occurrence_v1(candidate.occurrence)
    verified = candidate.verified_leaf
    code = _profile_reject_code_v2(
        profile,
        occurrence,
        verified,
        LaneIdV1.ZDEX_TOKENOMICS,
    )
    if code is not None:
        return ZDEXBuybackLaneCompositionRejectedV2(code)
    leaf = snapshot_verified_zdex_tokenomics_buyback_leaf_v2(verified)
    try:
        effects = _materialize_fee_allocations_v2(leaf.effects)
    except ValueError:
        return ZDEXBuybackLaneCompositionRejectedV2(
            ZDEXBuybackLaneCoordinatorRejectCodeV2.EFFECT_SHAPE_MISMATCH
        )
    return _accepted_lane_v2(
        profile=profile,
        occurrence=occurrence,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        leaf_journal_root=leaf.journal_root,
        leaf_assumption_root=verified.assumption_root,
        leaf_binding_root=verified.binding_root,
        effects=effects,
        outstanding=(),
        discharged=(leaf.journal.discharged_obligation_id,),
    )


__all__ = [
    "ZDEXBuybackLaneCompositionAcceptedV2",
    "ZDEXBuybackLaneCompositionRejectedV2",
    "ZDEXBuybackLaneCompositionResultV2",
    "ZDEXBuybackLaneCoordinatorRejectCodeV2",
    "ZDEXSpotBuybackLaneCandidateV2",
    "ZDEXTokenomicsBuybackLaneCandidateV2",
    "compose_zdex_spot_buyback_lane_shadow_v2",
    "compose_zdex_tokenomics_buyback_lane_shadow_v2",
    "zdex_buyback_terminal_set_root_v2",
]
