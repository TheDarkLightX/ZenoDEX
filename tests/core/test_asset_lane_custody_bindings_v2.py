"""Semantic corruption must fail at the custody coordinator boundary."""

from dataclasses import replace

import pytest

import src.core.asset_lane_custody_coordinator_v2 as coordinator
from src.core.asset_lane_coordinator_values_v2 import (
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
)
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_transfer_types_v2 import AssetTransferAcceptedV2, AssetTransferStateV2
from src.core.global_settlement_types_v2 import (
    AssetConservationRowV2,
    AssetSupplyV2,
    EconomicAmountV2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    canonical_global_bytes_v2,
)
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_policy,
    _registry,
    _root,
    _transfer_command,
    _transfer_policy,
)
from tests.core.test_asset_lane_custody_v2 import custody_state


def _rebind(candidate, *, post=None, effects=None, journal=None):
    post = candidate.post_state if post is None else post
    effects = candidate.effects if effects is None else effects
    journal = candidate.module_journal if journal is None else journal
    effects = replace(
        effects,
        lane_writes=(LaneWriteV2(LaneIdV2.ASSET_TRANSFER, journal.pre_lane_root, post.state_root),),
    )
    journal = replace(
        journal, post_lane_root=post.state_root, effect_plan_root=effects.effect_plan_root
    )
    return AssetTransferAcceptedV2(post, effects, journal)


@pytest.mark.parametrize("field", ("accounts", "supplies", "writer", "release", "policies"))
def test_coherent_leaf_mutants_reject_without_custody_or_economic_change(monkeypatch, field):
    state = custody_state()
    command = _transfer_command(amount_atoms=10)
    context = _context(command)
    candidate = coordinator.transition_asset_transfer_v2(
        context.transfer_context(), state.transfer_state, command
    )
    assert type(candidate) is AssetTransferAcceptedV2
    row = candidate.effects.asset_conservation[0]
    if field in {"accounts", "supplies"}:
        changed = (
            replace(row, owned_and_custodied_pre_atoms=100, owned_and_custodied_post_atoms=100)
            if field == "accounts"
            else replace(row, supply_pre_atoms=101, supply_post_atoms=101)
        )
        candidate = _rebind(
            candidate,
            effects=replace(candidate.effects, asset_conservation=(changed,)),
        )
    elif field == "writer":
        candidate = _rebind(
            candidate,
            journal=replace(candidate.module_journal, writer_epoch=context.writer_epoch + 1),
        )
    elif field == "release":
        context = coordinator.AssetLaneContextV2(
            context.writer_epoch,
            _root("foreign-release"),
            context.global_pre_state_root,
            context.occurrence,
        )
    else:
        leaf = candidate.post_state
        post = AssetTransferStateV2(
            leaf.module_release_id,
            (replace(leaf.policies[0], fee_owner="mallory"),),
            leaf.balances,
            leaf.supplies,
        )
        candidate = _rebind(candidate, post=post)
    monkeypatch.setattr(coordinator, "transition_asset_transfer_v2", lambda *_: candidate)
    result = coordinator.transition_asset_lane_custody_v2(context, state, command)
    assert type(result) is AssetLaneRejectedV2
    assert result.code.value == (
        "CANDIDATE_BINDING_MISMATCH" if field in {"writer", "release"} else "PROJECTION_MISMATCH"
    )
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty


def _two_asset_custody_state() -> AssetLaneCustodyStateV2:
    transfers = (_transfer_policy(asset="EUR", fee_atoms=0), _transfer_policy(asset="USD"))
    managed = (_managed_policy(asset="EUR"), _managed_policy(asset="USD"))
    transfer_state = AssetTransferStateV2(
        _root("module-release"),
        transfers,
        (
            EconomicAmountV2("carol", "EUR", "accounts", 7),
            EconomicAmountV2("alice", "USD", "accounts", 80),
        ),
        (AssetSupplyV2("EUR", 7), AssetSupplyV2("USD", 100)),
    )
    return AssetLaneCustodyStateV2(
        transfer_state,
        _registry(transfers, managed),
        managed,
        (EconomicAmountV2("vault", "USD", "escrow", 20),),
    )


def test_conservation_must_name_command_asset_before_custody_completion(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A coherent unchanged EUR row cannot attest a USD transition."""

    state = _two_asset_custody_state()
    original = canonical_global_bytes_v2(state.to_canonical())
    original_root = state.state_root
    command = _transfer_command(amount_atoms=10)
    context = _context(command)
    genuine = coordinator.transition_asset_lane_custody_v2(context, state, command)
    assert type(genuine) is coordinator.AssetLaneCustodyAcceptedV2
    assert tuple(row.asset for row in genuine.effects.asset_conservation) == (command.asset,)
    assert genuine.post_state.transfer_state.balances != state.transfer_state.balances
    assert genuine.post_state.custody == state.custody

    leaf = coordinator.transition_asset_transfer_v2(
        context.transfer_context(), state.transfer_state, command,
    )
    assert type(leaf) is AssetTransferAcceptedV2
    effects = replace(
        leaf.effects,
        asset_conservation=(AssetConservationRowV2("EUR", 7, 7, 7, 7, 0, 0),),
    )
    journal = replace(leaf.module_journal, effect_plan_root=effects.effect_plan_root)
    faulty_leaf = AssetTransferAcceptedV2(leaf.post_state, effects, journal)
    assert coordinator._source_holds(context, state, faulty_leaf)
    assert any(row.asset == command.asset for row in faulty_leaf.effects.rows)
    monkeypatch.setattr(coordinator, "transition_asset_transfer_v2", lambda *_: faulty_leaf)

    result = coordinator.transition_asset_lane_custody_v2(context, state, command)
    assert type(result) is AssetLaneRejectedV2
    assert result.route is AssetLaneRouteV2.COORDINATOR
    assert result.code is AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH
    assert result.pre_state_root == result.post_state_root == original_root
    assert result.effects == GlobalEconomicEffectPlanV2.empty()
    assert canonical_global_bytes_v2(state.to_canonical()) == original
    assert state.state_root == original_root
