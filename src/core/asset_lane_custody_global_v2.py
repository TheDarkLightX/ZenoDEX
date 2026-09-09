"""Bind the custody successor's complete lane frame to V2 global refinement.

This restricted relation consumes complete economic tables with empty reserves.
It checks no signature, receipt or store authority and cannot publish a state.
The derivation helper builds the one successor state this relation admits and
returns it only after that same relation accepts it.
"""

from dataclasses import replace

from .asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    snapshot_asset_lane_custody_accepted_v2,
)
from .asset_lane_custody_state_v2 import (
    AssetLaneCustodyStateV2,
    snapshot_asset_lane_custody_state_v2,
)
from .global_economic_proof_v2 import EconomicCommandOccurrenceV2, _snapshot_occurrence_v2
from .global_economic_state_effect_refinement_v2 import (
    GlobalEconomicStateEffectRefinementCandidateV2,
    GlobalEconomicStateEffectRefinementV2,
    refine_global_economic_state_effects_v2,
)
from .global_economic_state_v2 import (
    GlobalEconomicStateV2,
    LaneStateRootV2,
    ReplayStateV2,
    snapshot_global_economic_state_v2,
)
from .global_settlement_types_v2 import (
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
)


def _require_complete_projection(
    lane: AssetLaneCustodyStateV2, state: GlobalEconomicStateV2
) -> None:
    leaf = lane.transfer_state
    root = next(row for row in state.lane_roots if row.lane_id is LaneIdV2.ASSET_TRANSFER)
    # Global tables are sparse; the lane and registry retain dormant identities.
    if (
        state.balances != leaf.balances
        or state.custody != lane.custody
        or state.supplies != tuple(row for row in leaf.supplies if row.amount_atoms)
        or state.reserves
        or root.state_root != lane.state_root
        or root.module_release_id != leaf.module_release_id
        or not root.enabled
    ):
        raise ValueError("custody lane/global complete projection mismatch")


def refine_asset_lane_custody_global_v2(
    lane_pre: AssetLaneCustodyStateV2,
    accepted: AssetLaneCustodyAcceptedV2,
    global_pre: GlobalEconomicStateV2,
    global_post: GlobalEconomicStateV2,
    occurrence: EconomicCommandOccurrenceV2,
) -> GlobalEconomicStateEffectRefinementV2:
    """Check exact producer roots, physical rows, claimant frame and full outcome."""

    accepted = snapshot_asset_lane_custody_accepted_v2(accepted)
    pre = snapshot_asset_lane_custody_state_v2(lane_pre)
    before = snapshot_global_economic_state_v2(global_pre)
    after = snapshot_global_economic_state_v2(global_post)
    post, journal = accepted.post_state, accepted.module_journal
    _require_complete_projection(pre, before)
    _require_complete_projection(post, after)
    if (
        journal.chain_id,
        journal.deployment_root,
        journal.profile_root,
        journal.writer_epoch,
        journal.command_occurrence_id,
        journal.pre_lane_root,
        journal.post_lane_root,
        journal.effect_plan_root,
    ) != (
        before.chain_id,
        before.deployment_root,
        before.profile_root,
        before.writer_epoch,
        occurrence.occurrence_id,
        pre.state_root,
        post.state_root,
        accepted.effects.effect_plan_root,
    ):
        raise ValueError("custody global source journal binding mismatch")
    if before.liabilities != after.liabilities or before.custody != after.custody:
        raise ValueError("custody global claimant or custody frame changed")
    return refine_global_economic_state_effects_v2(
        GlobalEconomicStateEffectRefinementCandidateV2(
            before,
            after,
            accepted.effects,
            (occurrence,),
            GlobalTerminalObligationPlanV2.empty(),
            GlobalOracleOccurrencePlanV2.empty(),
        )
    )


def _successor_lane_roots(
    state: GlobalEconomicStateV2,
    lane_post: AssetLaneCustodyStateV2,
) -> tuple[LaneStateRootV2, ...]:
    return tuple(
        replace(row, state_root=lane_post.state_root)
        if row.lane_id is LaneIdV2.ASSET_TRANSFER
        else row
        for row in state.lane_roots
    )


def _successor_replay_state(
    state: GlobalEconomicStateV2,
    occurrence: EconomicCommandOccurrenceV2,
) -> tuple[ReplayStateV2, ...]:
    # Insert without overwriting. State validation rejects repeated replay ids
    # and independently checks occurrence-id uniqueness across all rows.
    inserted = ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id)
    return tuple(sorted((*state.replay_state, inserted), key=lambda row: row.replay_id))


def derive_asset_lane_custody_global_post_v2(
    lane_pre: AssetLaneCustodyStateV2,
    accepted: AssetLaneCustodyAcceptedV2,
    global_pre: GlobalEconomicStateV2,
    occurrence: EconomicCommandOccurrenceV2,
) -> GlobalEconomicStateV2:
    """Return the one successor state this relation admits for an accepted command.

    Post balances and positive supplies come from the accepted lane, only the
    ASSET_TRANSFER root is rewritten, every other global row is retained, height
    advances once under the owned u64 ceiling, and this occurrence's replay
    identity is inserted canonically.  The successor is derived from and checked
    against one owned acceptance snapshot, and the existing custody/global
    refiner performs every admission check before it is returned.  Callers keep
    unchanged inputs and receive no state on rejection.
    """

    before = snapshot_global_economic_state_v2(global_pre)
    consumed = _snapshot_occurrence_v2(occurrence)
    owned = snapshot_asset_lane_custody_accepted_v2(accepted)
    lane_post = owned.post_state
    leaf = lane_post.transfer_state
    after = GlobalEconomicStateV2(
        before.chain_id,
        before.deployment_root,
        before.writer_epoch,
        before.height + 1,
        before.profile_root,
        _successor_lane_roots(before, lane_post),
        balances=leaf.balances,
        supplies=tuple(row for row in leaf.supplies if row.amount_atoms),
        custody=before.custody,
        liabilities=before.liabilities,
        reserves=before.reserves,
        oracle_occurrences=before.oracle_occurrences,
        replay_state=_successor_replay_state(before, consumed),
        terminal_obligations=before.terminal_obligations,
        history_root=before.history_root,
        outbox=before.outbox,
    )
    refine_asset_lane_custody_global_v2(lane_pre, owned, before, after, consumed)
    return after
