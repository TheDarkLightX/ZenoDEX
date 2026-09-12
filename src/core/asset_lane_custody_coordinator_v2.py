"""Custody-preserving V2 leaf composition, without publication authority.

The unchanged leaves own account economics. This successor owns the complete
physical frame and binds newly derived totals to a new receipt and state root.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import TypeAlias, cast

from .asset_lane_coordinator_v2 import _route_and_owned_command_v2
from .asset_lane_coordinator_values_v2 import (
    AssetLaneCommandV2,
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
    _snapshot_effects_v2,
)
from .asset_lane_custody_state_v2 import (
    AssetLaneCustodyStateV2,
    custody_policy_origins_hold_v2,
    snapshot_asset_lane_custody_state_v2,
)
from .asset_lane_state_v2 import AssetLaneContextV2, _snapshot_asset_lane_context_v2
from .asset_transfer_module_v2 import transition_asset_transfer_v2
from .asset_transfer_types_v2 import (
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferRejectedV2,
    AssetTransferStateV2,
)
from .global_economic_proof_v2 import LaneModuleTransitionJournalV2, _snapshot_module_journal_v2
from .global_settlement_resource_limits_v2 import StateResourceLimitExceededV2
from .global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    _require_root_v2,
    hash_global_v2,
)
from .managed_asset_lifecycle_module_v2 import transition_managed_asset_lifecycle_v2
from .managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleRejectedV2,
)

_LeafAccepted: TypeAlias = AssetTransferAcceptedV2 | ManagedAssetLifecycleAcceptedV2
_ACCEPTED = object()


def _receipt_root(
    route: AssetLaneRouteV2,
    source_leaf_journal_root: str,
    source_leaf_receipt_root: str,
    journal: LaneModuleTransitionJournalV2,
) -> str:
    return hash_global_v2(
        "asset-lane-custody-coordinator-receipt-v2",
        {
            "route": route,
            "source_leaf_journal_root": source_leaf_journal_root,
            "source_leaf_receipt_root": source_leaf_receipt_root,
            "pre_lane_root": journal.pre_lane_root,
            "post_lane_root": journal.post_lane_root,
            "effect_plan_root": journal.effect_plan_root,
            "private_port_root": journal.private_port_root,
            "terminal_obligations_root": journal.terminal_obligations_root,
            "oracle_occurrence_plan_root": journal.oracle_occurrence_plan_root,
        },
    )


@dataclass(frozen=True, slots=True, init=False)
class AssetLaneCustodyAcceptedV2:
    route: AssetLaneRouteV2
    source_leaf_journal_root: str
    source_leaf_receipt_root: str
    _post_state: AssetLaneCustodyStateV2
    _effects: GlobalEconomicEffectPlanV2
    _module_journal: LaneModuleTransitionJournalV2

    def __init__(
        self,
        token: object,
        route: AssetLaneRouteV2,
        source_leaf_journal_root: str,
        source_leaf_receipt_root: str,
        post_state: AssetLaneCustodyStateV2,
        effects: GlobalEconomicEffectPlanV2,
        module_journal: LaneModuleTransitionJournalV2,
    ) -> None:
        if token is not _ACCEPTED:
            raise TypeError("custody acceptance is checker-constructed")
        if type(route) is not AssetLaneRouteV2 or route is AssetLaneRouteV2.COORDINATOR:
            raise TypeError("custody acceptance must name a leaf")
        _require_root_v2(source_leaf_journal_root, name="custody source leaf journal")
        _require_root_v2(source_leaf_receipt_root, name="custody source leaf receipt")
        object.__setattr__(self, "route", route)
        object.__setattr__(self, "source_leaf_journal_root", source_leaf_journal_root)
        object.__setattr__(self, "source_leaf_receipt_root", source_leaf_receipt_root)
        object.__setattr__(self, "_post_state", snapshot_asset_lane_custody_state_v2(post_state))
        object.__setattr__(self, "_effects", _snapshot_effects_v2(effects))
        object.__setattr__(self, "_module_journal", _snapshot_module_journal_v2(module_journal))
        journal, plan, state = self._module_journal, self._effects, self._post_state
        if not (
            journal.lane_id is LaneIdV2.ASSET_TRANSFER
            and journal.module_release_id == state.transfer_state.module_release_id
            and journal.post_lane_root == state.state_root
            and journal.effect_plan_root == plan.effect_plan_root
            and plan.lane_writes
            == (LaneWriteV2(LaneIdV2.ASSET_TRANSFER, journal.pre_lane_root, state.state_root),)
            and plan.occurrence_consumptions == (journal.command_occurrence_id,)
            and not plan.external_outbox_enqueue
            and journal.private_port_root == ZERO_ROOT_V2
            and journal.terminal_obligations_root == ZERO_ROOT_V2
            and journal.oracle_occurrence_plan_root == ZERO_ROOT_V2
            and journal.receipt_root
            == _receipt_root(route, source_leaf_journal_root, source_leaf_receipt_root, journal)
            and custody_policy_origins_hold_v2(state)
        ):
            raise ValueError("custody acceptance bindings differ")

    @property
    def post_state(self) -> AssetLaneCustodyStateV2:
        return snapshot_asset_lane_custody_state_v2(self._post_state)

    @property
    def effects(self) -> GlobalEconomicEffectPlanV2:
        return _snapshot_effects_v2(self._effects)

    @property
    def module_journal(self) -> LaneModuleTransitionJournalV2:
        return _snapshot_module_journal_v2(self._module_journal)

    @property
    def receipt_root(self) -> str:
        return self._module_journal.receipt_root

    @property
    def production_authority(self) -> str:
        return "NONE"

    @property
    def profile_authentication(self) -> str:
        return "SHADOW"


def snapshot_asset_lane_custody_accepted_v2(
    accepted: AssetLaneCustodyAcceptedV2,
) -> AssetLaneCustodyAcceptedV2:
    """Recheck the complete result binding when crossing a consumer boundary."""
    if type(accepted) is not AssetLaneCustodyAcceptedV2:
        raise TypeError("custody global refinement requires the exact successor result")
    return AssetLaneCustodyAcceptedV2(
        _ACCEPTED,
        accepted.route,
        accepted.source_leaf_journal_root,
        accepted.source_leaf_receipt_root,
        accepted.post_state,
        accepted.effects,
        accepted.module_journal,
    )


def _reject(
    state: AssetLaneCustodyStateV2, route: AssetLaneRouteV2, code: AssetLaneRejectCodeV2
) -> AssetLaneRejectedV2:
    return AssetLaneRejectedV2(
        route, code, state.state_root, state.state_root, GlobalEconomicEffectPlanV2.empty()
    )


def _source_holds(
    context: AssetLaneContextV2, state: AssetLaneCustodyStateV2, candidate: _LeafAccepted
) -> bool:
    occurrence = context.occurrence
    if occurrence is None:
        return False
    pre_leaf = (
        state.transfer_state
        if type(candidate) is AssetTransferAcceptedV2
        else state.managed_leaf_state()
    )
    journal, effects = candidate.module_journal, candidate.effects
    return (
        journal.lane_id is LaneIdV2.ASSET_TRANSFER
        and journal.chain_id == occurrence.chain_id
        and journal.deployment_root == occurrence.deployment_root
        and journal.profile_root == occurrence.profile_root
        and journal.writer_epoch == context.writer_epoch
        and context.module_release_id == state.transfer_state.module_release_id
        and journal.module_release_id == state.transfer_state.module_release_id
        and journal.command_occurrence_id == occurrence.occurrence_id
        and journal.pre_lane_root == pre_leaf.state_root
        and effects.occurrence_consumptions == (occurrence.occurrence_id,)
        and effects.lane_writes
        == (
            LaneWriteV2(
                LaneIdV2.ASSET_TRANSFER, pre_leaf.state_root, candidate.post_state.state_root
            ),
        )
        and journal.post_lane_root == candidate.post_state.state_root
        and journal.effect_plan_root == effects.effect_plan_root
        and not effects.external_outbox_enqueue
        and journal.private_port_root
        == journal.terminal_obligations_root
        == journal.oracle_occurrence_plan_root
        == ZERO_ROOT_V2
    )


def _account_projection_holds(
    pre: AssetLaneCustodyStateV2, command_asset: str, candidate: _LeafAccepted
) -> bool:
    rows = candidate.effects.asset_conservation
    if len(rows) != 1:
        return False
    row = rows[0]
    post = candidate.post_state
    if row.asset != command_asset or row.asset not in {p.asset for p in post.policies}:
        return False
    return (
        row.owned_and_custodied_pre_atoms == pre.account_atoms(row.asset)
        and row.owned_and_custodied_post_atoms
        == sum(r.amount_atoms for r in post.balances if r.asset == row.asset)
        and row.supply_pre_atoms == pre.transfer_state.supply_atoms(row.asset)
        and row.supply_post_atoms == post.supply_atoms(row.asset)
    )


def _post_state(pre: AssetLaneCustodyStateV2, candidate: _LeafAccepted) -> AssetLaneCustodyStateV2:
    transfer: AssetTransferStateV2
    if type(candidate) is AssetTransferAcceptedV2:
        transfer = candidate.post_state
    else:
        post = candidate.post_state
        managed = {p.asset for p in pre.managed_policies}
        old = pre.transfer_state
        balances = tuple(
            sorted(
                (*[r for r in old.balances if r.asset not in managed], *post.balances),
                key=lambda r: r.key,
            )
        )
        supplies = tuple(
            sorted(
                (*[r for r in old.supplies if r.asset not in managed], *post.supplies),
                key=lambda r: r.asset,
            )
        )
        transfer = AssetTransferStateV2(old.module_release_id, old.policies, balances, supplies)
    return AssetLaneCustodyStateV2(transfer, pre.origin_registry, pre.managed_policies, pre.custody)


def _complete(
    pre: AssetLaneCustodyStateV2,
    post: AssetLaneCustodyStateV2,
    route: AssetLaneRouteV2,
    candidate: _LeafAccepted,
) -> AssetLaneCustodyAcceptedV2:
    effects = replace(
        candidate.effects,
        asset_conservation=tuple(
            replace(
                row,
                owned_and_custodied_pre_atoms=pre.physical_atoms(row.asset),
                owned_and_custodied_post_atoms=post.physical_atoms(row.asset),
            )
            for row in candidate.effects.asset_conservation
        ),
        lane_writes=(LaneWriteV2(LaneIdV2.ASSET_TRANSFER, pre.state_root, post.state_root),),
    )
    source = candidate.module_journal
    journal = replace(
        source,
        pre_lane_root=pre.state_root,
        post_lane_root=post.state_root,
        effect_plan_root=effects.effect_plan_root,
    )
    journal = replace(
        journal,
        receipt_root=_receipt_root(route, source.journal_root, source.receipt_root, journal),
    )
    return AssetLaneCustodyAcceptedV2(
        _ACCEPTED, route, source.journal_root, source.receipt_root, post, effects, journal
    )


def transition_asset_lane_custody_v2(
    context: AssetLaneContextV2,
    pre_state: AssetLaneCustodyStateV2,
    command: AssetLaneCommandV2,
) -> AssetLaneCustodyAcceptedV2 | AssetLaneRejectedV2:
    """Preserve custody through transfer/issue/burn; return owned result or no-op."""

    context = _snapshot_asset_lane_context_v2(context)
    pre = snapshot_asset_lane_custody_state_v2(pre_state)
    route, command = _route_and_owned_command_v2(command)
    if not custody_policy_origins_hold_v2(pre):
        return _reject(
            pre,
            AssetLaneRouteV2.COORDINATOR,
            AssetLaneCoordinatorRejectCodeV2.REGISTRY_BINDING_MISMATCH,
        )
    candidate: _LeafAccepted | AssetTransferRejectedV2 | ManagedAssetLifecycleRejectedV2
    if type(command) is AssetTransferCommandV2:
        candidate = transition_asset_transfer_v2(
            context.transfer_context(), pre.transfer_state, command
        )
    elif type(command) is ManagedAssetLifecycleCommandV2:
        candidate = transition_managed_asset_lifecycle_v2(
            context.managed_context(), pre.managed_leaf_state(), command
        )
    else:
        raise TypeError("custody lane command must name a closed leaf")
    if type(candidate) in {AssetTransferRejectedV2, ManagedAssetLifecycleRejectedV2}:
        return _reject(
            pre,
            route,
            cast(AssetTransferRejectedV2 | ManagedAssetLifecycleRejectedV2, candidate).code,
        )
    if type(candidate) not in {AssetTransferAcceptedV2, ManagedAssetLifecycleAcceptedV2}:
        raise TypeError("custody leaf returned an unknown result")
    accepted = cast(_LeafAccepted, candidate)
    if not _source_holds(context, pre, accepted):
        return _reject(
            pre,
            AssetLaneRouteV2.COORDINATOR,
            AssetLaneCoordinatorRejectCodeV2.CANDIDATE_BINDING_MISMATCH,
        )
    if not _account_projection_holds(pre, command.asset, accepted):
        return _reject(
            pre, AssetLaneRouteV2.COORDINATOR, AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH
        )
    try:
        post = _post_state(pre, accepted)
    except StateResourceLimitExceededV2:
        return _reject(
            pre, AssetLaneRouteV2.COORDINATOR, AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT
        )
    projected = (
        post.transfer_state if route is AssetLaneRouteV2.TRANSFER else post.managed_leaf_state()
    )
    if (
        projected != accepted.post_state
        or post.transfer_state.policies != pre.transfer_state.policies
    ):
        return _reject(
            pre, AssetLaneRouteV2.COORDINATOR, AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH
        )
    return _complete(pre, post, route, accepted)
