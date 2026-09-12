"""Independent source-coordinate controls for the custody V2 coordinator.

The negative cases inject a coherently reconstructed but faulty internal leaf
result. Production exposes no leaf-result injection port. These controls do not
authenticate the leaf receipt root; receipt authenticity remains external.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Literal, TypeAlias

import pytest

import src.core.asset_lane_custody_coordinator_v2 as coordinator
from src.core.asset_lane_coordinator_values_v2 import (
    AssetLaneCommandV2,
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
)
from src.core.asset_lane_custody_coordinator_v2 import AssetLaneCustodyAcceptedV2
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.asset_transfer_types_v2 import AssetTransferAcceptedV2
from src.core.global_economic_proof_v2 import LaneModuleTransitionJournalV2
from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecycleAcceptedV2
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_command,
    _root,
    _transfer_command,
)
from tests.core.test_asset_lane_custody_v2 import custody_state

_LeafAccepted: TypeAlias = AssetTransferAcceptedV2 | ManagedAssetLifecycleAcceptedV2
_SourceField: TypeAlias = Literal["chain_id", "deployment_root", "profile_root"]


@dataclass(frozen=True)
class _Case:
    state: AssetLaneCustodyStateV2
    context: AssetLaneContextV2
    command: AssetLaneCommandV2
    leaf: _LeafAccepted
    leaf_attribute: str
    route: AssetLaneRouteV2


def _case(managed: bool) -> _Case:
    state = custody_state()
    if managed:
        managed_command = _managed_command(amount_atoms=7)
        managed_context = _context(managed_command)
        managed_leaf = coordinator.transition_managed_asset_lifecycle_v2(
            managed_context.managed_context(), state.managed_leaf_state(), managed_command
        )
        assert type(managed_leaf) is ManagedAssetLifecycleAcceptedV2
        return _Case(
            state,
            managed_context,
            managed_command,
            managed_leaf,
            "transition_managed_asset_lifecycle_v2",
            AssetLaneRouteV2.MANAGED_LIFECYCLE,
        )
    transfer_command = _transfer_command(amount_atoms=10)
    transfer_context = _context(transfer_command)
    transfer_leaf = coordinator.transition_asset_transfer_v2(
        transfer_context.transfer_context(), state.transfer_state, transfer_command
    )
    assert type(transfer_leaf) is AssetTransferAcceptedV2
    return _Case(
        state,
        transfer_context,
        transfer_command,
        transfer_leaf,
        "transition_asset_transfer_v2",
        AssetLaneRouteV2.TRANSFER,
    )


def _with_journal(
    leaf: _LeafAccepted, journal: LaneModuleTransitionJournalV2
) -> _LeafAccepted:
    if type(leaf) is AssetTransferAcceptedV2:
        return AssetTransferAcceptedV2(leaf.post_state, leaf.effects, journal)
    assert type(leaf) is ManagedAssetLifecycleAcceptedV2
    return ManagedAssetLifecycleAcceptedV2(leaf.post_state, leaf.effects, journal)


def _replace_source_coordinate(
    journal: LaneModuleTransitionJournalV2, field: _SourceField, value: str
) -> LaneModuleTransitionJournalV2:
    if field == "chain_id":
        return replace(journal, chain_id=value)
    if field == "deployment_root":
        return replace(journal, deployment_root=value)
    return replace(journal, profile_root=value)


def _source_coordinate(
    journal: LaneModuleTransitionJournalV2, field: _SourceField
) -> str:
    if field == "chain_id":
        return journal.chain_id
    if field == "deployment_root":
        return journal.deployment_root
    return journal.profile_root


@pytest.mark.parametrize("managed", (False, True), ids=("transfer", "managed-issue"))
def test_real_leaf_and_outer_positive_controls(managed: bool) -> None:
    case = _case(managed)
    assert coordinator._source_holds(case.context, case.state, case.leaf)
    result = coordinator.transition_asset_lane_custody_v2(
        case.context, case.state, case.command
    )
    assert type(result) is AssetLaneCustodyAcceptedV2
    assert result.route is case.route
    assert result.source_leaf_journal_root == case.leaf.module_journal.journal_root
    assert result.source_leaf_receipt_root == case.leaf.receipt_root


@pytest.mark.parametrize("field", ("chain_id", "deployment_root", "profile_root"))
@pytest.mark.parametrize("managed", (False, True), ids=("transfer", "managed-issue"))
def test_faulty_internal_leaf_source_coordinate_is_exact_noop(
    monkeypatch: pytest.MonkeyPatch, managed: bool, field: _SourceField
) -> None:
    case = _case(managed)
    before, before_root = case.state.to_canonical(), case.state.state_root
    foreign = "asset-lane-v2-foreign" if field == "chain_id" else _root(f"foreign-{field}")
    journal = _replace_source_coordinate(case.leaf.module_journal, field, foreign)
    faulty = _with_journal(case.leaf, journal)
    assert _source_coordinate(faulty.module_journal, field) == foreign
    assert faulty.module_journal == journal
    assert faulty.post_state == case.leaf.post_state
    assert faulty.effects == case.leaf.effects
    restored = _replace_source_coordinate(
        journal, field, _source_coordinate(case.leaf.module_journal, field)
    )
    assert restored == case.leaf.module_journal
    assert faulty.module_journal.journal_root != case.leaf.module_journal.journal_root
    monkeypatch.setattr(coordinator, case.leaf_attribute, lambda *_args: faulty)

    result = coordinator.transition_asset_lane_custody_v2(
        case.context, case.state, case.command
    )

    assert type(result) is AssetLaneRejectedV2
    assert result.route is AssetLaneRouteV2.COORDINATOR
    assert result.code is AssetLaneCoordinatorRejectCodeV2.CANDIDATE_BINDING_MISMATCH
    assert result.pre_state_root == result.post_state_root == before_root
    assert result.effects.rows == ()
    assert result.effects.asset_conservation == ()
    assert result.effects.fee_conservation == ()
    assert result.effects.lane_writes == ()
    assert result.effects.occurrence_consumptions == ()
    assert result.effects.external_outbox_enqueue == ()
    assert case.state.to_canonical() == before
    assert case.state.state_root == before_root
