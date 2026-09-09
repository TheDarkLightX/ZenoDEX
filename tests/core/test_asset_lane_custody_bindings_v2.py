"""Semantic corruption must fail at the custody coordinator boundary."""

from dataclasses import replace

import pytest

import src.core.asset_lane_custody_coordinator_v2 as coordinator
from src.core.asset_transfer_types_v2 import AssetTransferAcceptedV2, AssetTransferStateV2
from src.core.global_settlement_types_v2 import LaneIdV2, LaneWriteV2
from tests.core.test_asset_lane_coordinator_v2 import _context, _root, _transfer_command
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
    row = candidate.effects.asset_conservation[0]
    if field in {"accounts", "supplies"}:
        changed = (
            {"owned_and_custodied_pre_atoms": 100, "owned_and_custodied_post_atoms": 100}
            if field == "accounts"
            else {"supply_pre_atoms": 101, "supply_post_atoms": 101}
        )
        candidate = _rebind(
            candidate,
            effects=replace(candidate.effects, asset_conservation=(replace(row, **changed),)),
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
    assert result.code.value == (
        "CANDIDATE_BINDING_MISMATCH" if field in {"writer", "release"} else "PROJECTION_MISMATCH"
    )
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty
