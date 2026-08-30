"""SHADOW route composition for one authenticated ZDEX buy-and-burn.

The composer consumes exact leaf and lane-coordinator witnesses for one
occurrence.  It closes the Spot terminal obligation, projects the canonical
global post-state, and checks the temporal fee allocation followed by the
same-route buyback spend.  The result is deterministic data and grants no
receipt, settlement, or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from .global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from .global_economic_effect_projector_v1 import (
    project_single_occurrence_global_effects_v1,
)
from .global_economic_profile_snapshot_v1 import (
    _snapshot_route_release_v1,
    snapshot_economic_profile_v1,
)
from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    RouteCompositionJournalV1,
)
from .global_economic_refinement_snapshot_v1 import (
    _snapshot_occurrence_v1,
    _snapshot_state_v1,
)
from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
    EconomicEffectRowV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    validate_global_state_profile_v1,
)
from .zdex_atomic_buyback_lane_receipt_v2 import (
    VerifiedZDEXBuybackLaneCompositionV2,
    snapshot_verified_zdex_buyback_lane_composition_v2,
)
from .zdex_atomic_buyback_receipt_verification_v2 import (
    VerifiedZDEXSpotBuybackLeafV2,
    VerifiedZDEXTokenomicsBuybackLeafV2,
    snapshot_verified_zdex_spot_buyback_leaf_v2,
    snapshot_verified_zdex_tokenomics_buyback_leaf_v2,
)
from .zdex_atomic_buyback_route_contract_v2 import (
    ZDEXAtomicBuybackRouteAcceptedV2,
    ZDEXAtomicBuybackRouteCandidateV2,
    ZDEXAtomicBuybackRouteRejectCodeV2,
    ZDEXAtomicBuybackRouteRejectedV2,
    ZDEXAtomicBuybackRouteResultV2,
)
from .zdex_atomic_buyback_route_refinement_v2 import (
    ZDEXAtomicBuybackStateRefinementCandidateV2,
    refine_zdex_atomic_buyback_route_state_v2,
)
from .zdex_atomic_buyback_route_types_v2 import (
    require_zdex_atomic_buyback_route_shape_v2,
)


def _reject_v2(
    code: ZDEXAtomicBuybackRouteRejectCodeV2,
    pre_state: GlobalEconomicStateV1,
) -> ZDEXAtomicBuybackRouteRejectedV2:
    return ZDEXAtomicBuybackRouteRejectedV2(code, pre_state, pre_state)


@dataclass(frozen=True, slots=True)
class _OwnedRouteCandidateV2:
    profile: EconomicProfileSnapshotV1
    route: RouteReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    pre_state: GlobalEconomicStateV1
    head: GlobalEconomicAuthorityHeadV1
    spot_leaf: VerifiedZDEXSpotBuybackLeafV2
    tokenomics_leaf: VerifiedZDEXTokenomicsBuybackLeafV2
    spot_lane: VerifiedZDEXBuybackLaneCompositionV2
    tokenomics_lane: VerifiedZDEXBuybackLaneCompositionV2


def _snapshot_candidate_v2(
    candidate: ZDEXAtomicBuybackRouteCandidateV2,
) -> _OwnedRouteCandidateV2:
    return _OwnedRouteCandidateV2(
        snapshot_economic_profile_v1(candidate.profile),
        _snapshot_route_release_v1(candidate.route_release),
        _snapshot_occurrence_v1(candidate.occurrence),
        _snapshot_state_v1(candidate.pre_state),
        replace(candidate.authority_head),
        candidate.verified_spot_leaf,
        candidate.verified_tokenomics_leaf,
        candidate.verified_spot_lane,
        candidate.verified_tokenomics_lane,
    )


def _checked_delta_v2(value: int) -> int:
    if not MIN_DELTA_ATOMS_V1 <= value <= MAX_DELTA_ATOMS_V1:
        raise ValueError("ZDEX atomic buyback aggregate exceeds signed i128")
    return value


def _compose_effects_v2(
    spot: GlobalEconomicEffectPlanV1,
    tokenomics: GlobalEconomicEffectPlanV1,
) -> GlobalEconomicEffectPlanV1:
    totals: dict[tuple[str, str, str, str], tuple[EconomicEffectRowV1, int]] = {}
    for plan in (spot, tokenomics):
        if plan.external_outbox_enqueue:
            raise ValueError("ZDEX atomic buyback forbids external effects")
        for row in plan.rows:
            exemplar, prior = totals.get(row.key, (row, 0))
            totals[row.key] = (exemplar, _checked_delta_v2(prior + row.delta_atoms))
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
    if spot.asset_conservation or spot.fee_conservation:
        raise ValueError("Spot coordinator owns no route conservation rows")
    if spot.occurrence_consumptions or len(tokenomics.occurrence_consumptions) != 1:
        raise ValueError("ZDEX atomic buyback must consume one occurrence once")
    writes = tuple(sorted((*spot.lane_writes, *tokenomics.lane_writes)))
    if tuple(write.lane_id for write in writes) != (
        LaneIdV1.SPOT_LIQUIDITY,
        LaneIdV1.ZDEX_TOKENOMICS,
    ):
        raise ValueError("ZDEX atomic buyback lane writes are incomplete")
    return GlobalEconomicEffectPlanV1(
        rows,
        tokenomics.asset_conservation,
        tokenomics.fee_conservation,
        writes,
        tokenomics.occurrence_consumptions,
        (),
    )


def _profile_matches_v2(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
) -> bool:
    selected = tuple(
        item for item in profile.route_registry.routes if item.command_kind == route.command_kind
    )
    return (
        profile.status is ProfileStatusV1.SHADOW
        and route.status is ReleaseStatusV1.SHADOW
        and not route.accepts_new_objects
        and selected == (route,)
    )


def _authority_matches_v2(
    profile: EconomicProfileSnapshotV1,
    head: GlobalEconomicAuthorityHeadV1,
    handles: tuple[
        VerifiedZDEXSpotBuybackLeafV2
        | VerifiedZDEXTokenomicsBuybackLeafV2
        | VerifiedZDEXBuybackLaneCompositionV2,
        ...,
    ],
) -> bool:
    return (
        head.status is GlobalEconomicAuthorityStatusV1.ACTIVE
        and head.profile_root == profile.profile_id
        and head.writer_epoch == profile.authority_epoch
        and head.verifier_registry_root == profile.verifier_registry_root
        and head.root_image_id == profile.root_image_id
        and all(handle.profile_root == profile.profile_id for handle in handles)
        and all(handle.writer_epoch == profile.authority_epoch for handle in handles)
        and all(handle.authority_head_root == head.authority_root for handle in handles)
        and len({handle.verifier_binding_root for handle in handles}) == 1
        and handles[0].verifier_binding_root == head.verifier_binding_root
    )


def _receipt_bindings_match_v2(
    occurrence: EconomicCommandOccurrenceV1,
    spot_leaf: VerifiedZDEXSpotBuybackLeafV2,
    tokenomics_leaf: VerifiedZDEXTokenomicsBuybackLeafV2,
    spot_lane: VerifiedZDEXBuybackLaneCompositionV2,
    tokenomics_lane: VerifiedZDEXBuybackLaneCompositionV2,
) -> bool:
    spot_composition = snapshot_verified_zdex_buyback_lane_composition_v2(spot_lane)
    tokenomics_composition = snapshot_verified_zdex_buyback_lane_composition_v2(
        tokenomics_lane
    )
    return (
        spot_leaf.command_occurrence_id == occurrence.occurrence_id
        and tokenomics_leaf.command_occurrence_id == occurrence.occurrence_id
        and spot_lane.route_occurrence_id == occurrence.occurrence_id
        and tokenomics_lane.route_occurrence_id == occurrence.occurrence_id
        and spot_lane.lane_id is LaneIdV1.SPOT_LIQUIDITY
        and tokenomics_lane.lane_id is LaneIdV1.ZDEX_TOKENOMICS
        and spot_composition.leaf_binding_root == spot_leaf.binding_root
        and tokenomics_composition.leaf_binding_root == tokenomics_leaf.binding_root
        and spot_composition.leaf_assumption_root == spot_leaf.assumption_root
        and tokenomics_composition.leaf_assumption_root
        == tokenomics_leaf.assumption_root
        and spot_composition.lane_journal.ordered_module_journal_roots
        == (spot_leaf.journal_root,)
        and tokenomics_composition.lane_journal.ordered_module_journal_roots
        == (tokenomics_leaf.journal_root,)
    )


def _terminal_bindings_match_v2(
    spot_leaf: VerifiedZDEXSpotBuybackLeafV2,
    tokenomics_leaf: VerifiedZDEXTokenomicsBuybackLeafV2,
    spot_lane: VerifiedZDEXBuybackLaneCompositionV2,
    tokenomics_lane: VerifiedZDEXBuybackLaneCompositionV2,
) -> bool:
    spot = snapshot_verified_zdex_spot_buyback_leaf_v2(spot_leaf)
    tokenomics = snapshot_verified_zdex_tokenomics_buyback_leaf_v2(tokenomics_leaf)
    spot_composition = snapshot_verified_zdex_buyback_lane_composition_v2(spot_lane)
    tokenomics_composition = snapshot_verified_zdex_buyback_lane_composition_v2(
        tokenomics_lane
    )
    return (
        spot_composition.outstanding_terminal_obligations
        == (spot.journal.terminal_obligation_id,)
        and tokenomics_composition.outstanding_terminal_obligations == ()
        and tokenomics_composition.discharged_terminal_obligations
        == (spot.journal.terminal_obligation_id,)
        and tokenomics.journal.discharged_obligation_id
        == spot.journal.terminal_obligation_id
        and tokenomics.journal.spot_context_root == spot.journal.context.context_root
        and tokenomics.journal.spot_coordinates_root
        == spot.journal.context.coordinates.coordinates_root
        and tokenomics.journal.spot_post_state_root == spot.journal.post_state_root
        and tokenomics.journal.quote_port_root
        == spot.journal.context.coordinates.quote_port_root
        and tokenomics.journal.selected_pool_id == spot.journal.selected_pool_id
        and tokenomics.journal.quote_spend_atoms == spot.journal.quote_input_atoms
        and tokenomics.journal.purchased_zdex_atoms == spot.journal.purchased_zdex_atoms
        and tokenomics.journal.burned_zdex_atoms == spot.journal.purchased_zdex_atoms
    )


def _first_reject_code_v2(
    owned: _OwnedRouteCandidateV2,
) -> ZDEXAtomicBuybackRouteRejectCodeV2 | None:
    try:
        require_zdex_atomic_buyback_route_shape_v2(owned.route)
    except (TypeError, ValueError):
        return ZDEXAtomicBuybackRouteRejectCodeV2.PROFILE_MISMATCH
    if not _profile_matches_v2(owned.profile, owned.route):
        return ZDEXAtomicBuybackRouteRejectCodeV2.PROFILE_MISMATCH
    occurrence = owned.occurrence
    if (
        occurrence.route_release_id != owned.route.route_release_id
        or occurrence.profile_root != owned.profile.profile_id
        or occurrence.pre_state_root != owned.pre_state.state_root
        or occurrence.command_kind != owned.route.command_kind
        or occurrence.height != owned.pre_state.height + 1
    ):
        return ZDEXAtomicBuybackRouteRejectCodeV2.OCCURRENCE_MISMATCH
    try:
        validate_global_state_profile_v1(owned.pre_state, owned.profile)
    except (TypeError, ValueError):
        return ZDEXAtomicBuybackRouteRejectCodeV2.PROFILE_MISMATCH
    handles = (owned.spot_leaf, owned.tokenomics_leaf, owned.spot_lane, owned.tokenomics_lane)
    if not _authority_matches_v2(owned.profile, owned.head, handles):
        return ZDEXAtomicBuybackRouteRejectCodeV2.AUTHORITY_MISMATCH
    if not _receipt_bindings_match_v2(
        occurrence,
        owned.spot_leaf,
        owned.tokenomics_leaf,
        owned.spot_lane,
        owned.tokenomics_lane,
    ):
        return ZDEXAtomicBuybackRouteRejectCodeV2.RECEIPT_BINDING_MISMATCH
    if not _terminal_bindings_match_v2(
        owned.spot_leaf,
        owned.tokenomics_leaf,
        owned.spot_lane,
        owned.tokenomics_lane,
    ):
        return ZDEXAtomicBuybackRouteRejectCodeV2.TERMINAL_BINDING_MISMATCH
    return None


def _route_journal_v2(
    owned: _OwnedRouteCandidateV2,
    effects: GlobalEconomicEffectPlanV1,
    post_state: GlobalEconomicStateV1,
    lane_roots: tuple[str, str],
) -> RouteCompositionJournalV1:
    occurrence = owned.occurrence
    return RouteCompositionJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=owned.profile.authority_epoch,
        route_release_id=owned.route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        ordered_lane_journal_roots=lane_roots,
        pre_state_root=owned.pre_state.state_root,
        post_state_root=post_state.state_root,
        effect_plan_root=effects.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
    )


def compose_zdex_atomic_buyback_route_shadow_v2(
    candidate: ZDEXAtomicBuybackRouteCandidateV2,
) -> ZDEXAtomicBuybackRouteResultV2:
    """Compose one exact authenticated two-lane buy-and-burn occurrence."""

    if type(candidate) is not ZDEXAtomicBuybackRouteCandidateV2:
        raise TypeError("ZDEX atomic buyback route candidate must be exact typed data")
    candidate.__post_init__()
    owned = _snapshot_candidate_v2(candidate)
    reject_code = _first_reject_code_v2(owned)
    if reject_code is not None:
        return _reject_v2(reject_code, owned.pre_state)
    spot_lane = snapshot_verified_zdex_buyback_lane_composition_v2(
        owned.spot_lane
    )
    tokenomics_lane = snapshot_verified_zdex_buyback_lane_composition_v2(
        owned.tokenomics_lane
    )
    try:
        effects = _compose_effects_v2(spot_lane.effects, tokenomics_lane.effects)
        if effects.occurrence_consumptions != (owned.occurrence.occurrence_id,):
            raise ValueError("ZDEX atomic buyback occurrence consumption mismatch")
        post_state = project_single_occurrence_global_effects_v1(
            owned.pre_state,
            effects,
            owned.occurrence,
        )
    except (TypeError, ValueError):
        return _reject_v2(
            ZDEXAtomicBuybackRouteRejectCodeV2.EFFECT_COMPOSITION_MISMATCH,
            owned.pre_state,
        )
    route_journal = _route_journal_v2(
        owned,
        effects,
        post_state,
        (
            spot_lane.lane_journal.journal_root,
            tokenomics_lane.lane_journal.journal_root,
        ),
    )
    try:
        refinement = refine_zdex_atomic_buyback_route_state_v2(
            ZDEXAtomicBuybackStateRefinementCandidateV2(
                owned.pre_state,
                post_state,
                effects,
                owned.occurrence,
                route_journal,
                owned.spot_leaf,
                owned.tokenomics_leaf,
            )
        )
    except (TypeError, ValueError):
        return _reject_v2(
            ZDEXAtomicBuybackRouteRejectCodeV2.STATE_REFINEMENT_MISMATCH,
            owned.pre_state,
        )
    return ZDEXAtomicBuybackRouteAcceptedV2(
        post_state,
        effects,
        route_journal,
        (
            owned.spot_leaf.binding_root,
            owned.tokenomics_leaf.binding_root,
        ),
        (
            owned.spot_lane.assumption_root,
            owned.tokenomics_lane.assumption_root,
        ),
        (
            owned.spot_lane.binding_root,
            owned.tokenomics_lane.binding_root,
        ),
        refinement.state_delta_root,
        refinement.fee_disposition_root,
    )


__all__ = [
    "ZDEXAtomicBuybackRouteAcceptedV2",
    "ZDEXAtomicBuybackRouteCandidateV2",
    "ZDEXAtomicBuybackRouteRejectCodeV2",
    "ZDEXAtomicBuybackRouteRejectedV2",
    "ZDEXAtomicBuybackRouteResultV2",
    "compose_zdex_atomic_buyback_route_shadow_v2",
]
