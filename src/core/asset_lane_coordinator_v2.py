"""Bounded single-owner coordinator for V2 ``ASSET_TRANSFER`` candidates.

The coordinator owns dispatch, validates policy-to-origin membership, invokes
one closed leaf internally, and rebinds accepted effects to the aggregate lane
root.  The resulting candidate remains SHADOW evidence with authority NONE.
"""

from __future__ import annotations

from typing import TypeAlias, cast

from .asset_lane_coordinator_values_v2 import (
    _ASSET_LANE_ACCEPTED_TOKEN_V2,
    AssetLaneAcceptedV2,
    AssetLaneCommandV2,
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneLeafRejectCodeV2,
    AssetLaneRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneResultV2,
    AssetLaneRouteV2,
)
from .asset_lane_state_v2 import (
    AssetLaneContextV2,
    AssetLaneStateV2,
    _policy_origin_bindings_hold_v2,
    _snapshot_asset_lane_context_v2,
    _snapshot_asset_lane_state_v2,
)
from .asset_transfer_module_v2 import transition_asset_transfer_v2
from .asset_transfer_types_v2 import (
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferRejectedV2,
    _snapshot_asset_transfer_command_v2,
)
from .global_economic_proof_v2 import LaneModuleTransitionJournalV2
from .global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    hash_global_v2,
)
from .managed_asset_lifecycle_module_v2 import (
    transition_managed_asset_lifecycle_v2,
)
from .managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleRejectedV2,
    _snapshot_command_v2,
)

_LeafAcceptedV2: TypeAlias = (
    AssetTransferAcceptedV2 | ManagedAssetLifecycleAcceptedV2
)


def _route_and_owned_command_v2(
    command: AssetLaneCommandV2,
) -> tuple[AssetLaneRouteV2, AssetLaneCommandV2]:
    if type(command) is AssetTransferCommandV2:
        return AssetLaneRouteV2.TRANSFER, _snapshot_asset_transfer_command_v2(command)
    if type(command) is ManagedAssetLifecycleCommandV2:
        return AssetLaneRouteV2.MANAGED_LIFECYCLE, _snapshot_command_v2(command)
    raise TypeError("asset lane command must be one exact closed V2 command")


def _reject_v2(
    state: AssetLaneStateV2,
    route: AssetLaneRouteV2,
    code: AssetLaneRejectCodeV2,
) -> AssetLaneRejectedV2:
    return AssetLaneRejectedV2(
        route,
        code,
        state.state_root,
        state.state_root,
        GlobalEconomicEffectPlanV2.empty(),
    )


def _candidate_binding_holds_v2(
    context: AssetLaneContextV2,
    state: AssetLaneStateV2,
    candidate: _LeafAcceptedV2,
) -> bool:
    occurrence = context.occurrence
    if occurrence is None:
        return False
    journal = candidate.module_journal
    expected_leaf_pre = (
        state.transfer_leaf_state().state_root
        if type(candidate) is AssetTransferAcceptedV2
        else state.managed_leaf_state().state_root
    )
    return (
        journal.chain_id == occurrence.chain_id
        and journal.deployment_root == occurrence.deployment_root
        and journal.profile_root == occurrence.profile_root
        and journal.writer_epoch == context.writer_epoch
        and journal.module_release_id == state.module_release_id
        and journal.command_occurrence_id == occurrence.occurrence_id
        and journal.pre_lane_root == expected_leaf_pre
        and candidate.effects.occurrence_consumptions == (occurrence.occurrence_id,)
        and not candidate.effects.external_outbox_enqueue
        and journal.private_port_root == ZERO_ROOT_V2
        and journal.terminal_obligations_root == ZERO_ROOT_V2
        and journal.oracle_occurrence_plan_root == ZERO_ROOT_V2
    )


def _aggregate_post_state_v2(
    pre_state: AssetLaneStateV2,
    candidate: _LeafAcceptedV2,
) -> AssetLaneStateV2:
    if type(candidate) is AssetTransferAcceptedV2:
        balances = candidate.post_state.balances
        supplies = candidate.post_state.supplies
    else:
        managed_assets = {policy.asset for policy in pre_state.managed_policies}
        balances = tuple(
            sorted(
                (
                    *(row for row in pre_state.balances if row.asset not in managed_assets),
                    *candidate.post_state.balances,
                ),
                key=lambda row: row.key,
            )
        )
        supplies = tuple(
            sorted(
                (
                    *(row for row in pre_state.supplies if row.asset not in managed_assets),
                    *candidate.post_state.supplies,
                ),
                key=lambda row: row.asset,
            )
        )
    return AssetLaneStateV2(
        pre_state.module_release_id,
        pre_state.origin_registry,
        pre_state.transfer_policies,
        pre_state.managed_policies,
        balances,
        supplies,
    )


def _projection_holds_v2(
    route: AssetLaneRouteV2,
    post_state: AssetLaneStateV2,
    candidate: _LeafAcceptedV2,
) -> bool:
    projected_root = (
        post_state.transfer_leaf_state().state_root
        if route is AssetLaneRouteV2.TRANSFER
        else post_state.managed_leaf_state().state_root
    )
    if candidate.post_state.state_root != projected_root:
        return False
    conservation = candidate.effects.asset_conservation
    if len(conservation) != 1:
        return False
    row = conservation[0]
    return (
        row.owned_and_custodied_post_atoms == post_state.supply_atoms(row.asset)
        and row.supply_post_atoms == post_state.supply_atoms(row.asset)
    )


def _rebind_candidate_v2(
    route: AssetLaneRouteV2,
    pre_state: AssetLaneStateV2,
    post_state: AssetLaneStateV2,
    candidate: _LeafAcceptedV2,
) -> AssetLaneAcceptedV2:
    effects = candidate.effects
    rebound_effects = GlobalEconomicEffectPlanV2(
        effects.rows,
        effects.asset_conservation,
        effects.fee_conservation,
        (LaneWriteV2(LaneIdV2.ASSET_TRANSFER, pre_state.state_root, post_state.state_root),),
        effects.occurrence_consumptions,
        (),
    )
    source_journal = candidate.module_journal
    source_leaf_journal_root = source_journal.journal_root
    receipt_root = hash_global_v2(
        "asset-lane-coordinator-receipt-v2",
        {
            "route": route,
            "source_leaf_journal_root": source_leaf_journal_root,
            "source_leaf_receipt_root": source_journal.receipt_root,
            "pre_lane_root": pre_state.state_root,
            "post_lane_root": post_state.state_root,
            "effect_plan_root": rebound_effects.effect_plan_root,
            "private_port_root": ZERO_ROOT_V2,
            "terminal_obligations_root": ZERO_ROOT_V2,
            "oracle_occurrence_plan_root": ZERO_ROOT_V2,
        },
    )
    journal = LaneModuleTransitionJournalV2(
        chain_id=source_journal.chain_id,
        deployment_root=source_journal.deployment_root,
        profile_root=source_journal.profile_root,
        writer_epoch=source_journal.writer_epoch,
        lane_id=LaneIdV2.ASSET_TRANSFER,
        module_release_id=source_journal.module_release_id,
        command_occurrence_id=source_journal.command_occurrence_id,
        pre_lane_root=pre_state.state_root,
        post_lane_root=post_state.state_root,
        effect_plan_root=rebound_effects.effect_plan_root,
        private_port_root=ZERO_ROOT_V2,
        receipt_root=receipt_root,
        terminal_obligations_root=ZERO_ROOT_V2,
        oracle_occurrence_plan_root=ZERO_ROOT_V2,
    )
    return AssetLaneAcceptedV2(
        _ASSET_LANE_ACCEPTED_TOKEN_V2,
        route,
        source_leaf_journal_root,
        post_state,
        rebound_effects,
        journal,
    )


def transition_asset_lane_v2(
    context: AssetLaneContextV2,
    pre_state: AssetLaneStateV2,
    command: AssetLaneCommandV2,
) -> AssetLaneResultV2:
    """Dispatch one owned command and return a rebound aggregate candidate."""

    owned_context = _snapshot_asset_lane_context_v2(context)
    owned_state = _snapshot_asset_lane_state_v2(pre_state)
    route, owned_command = _route_and_owned_command_v2(command)
    if not _policy_origin_bindings_hold_v2(owned_state):
        return _reject_v2(
            owned_state,
            AssetLaneRouteV2.COORDINATOR,
            AssetLaneCoordinatorRejectCodeV2.REGISTRY_BINDING_MISMATCH,
        )
    if route is AssetLaneRouteV2.TRANSFER:
        transfer_command = cast(AssetTransferCommandV2, owned_command)
        candidate = transition_asset_transfer_v2(
            owned_context.transfer_context(),
            owned_state.transfer_leaf_state(),
            transfer_command,
        )
    else:
        managed_command = cast(ManagedAssetLifecycleCommandV2, owned_command)
        candidate = transition_managed_asset_lifecycle_v2(
            owned_context.managed_context(),
            owned_state.managed_leaf_state(),
            managed_command,
        )
    if type(candidate) in {AssetTransferRejectedV2, ManagedAssetLifecycleRejectedV2}:
        return _reject_v2(owned_state, route, candidate.code)
    if not _candidate_binding_holds_v2(owned_context, owned_state, candidate):
        return _reject_v2(
            owned_state,
            route,
            AssetLaneCoordinatorRejectCodeV2.CANDIDATE_BINDING_MISMATCH,
        )
    post_state = _aggregate_post_state_v2(owned_state, candidate)
    if not _projection_holds_v2(route, post_state, candidate):
        return _reject_v2(
            owned_state,
            route,
            AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
        )
    return _rebind_candidate_v2(route, owned_state, post_state, candidate)


__all__ = [
    "AssetLaneRouteV2",
    "AssetLaneCoordinatorRejectCodeV2",
    "AssetLaneLeafRejectCodeV2",
    "AssetLaneRejectCodeV2",
    "AssetLaneCommandV2",
    "AssetLaneAcceptedV2",
    "AssetLaneRejectedV2",
    "AssetLaneResultV2",
    "transition_asset_lane_v2",
]
