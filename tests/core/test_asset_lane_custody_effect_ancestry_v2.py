"""BDD regression for effect-principal ancestry at the global custody boundary.

The injected leaf is a constructor-valid internal result.  It demonstrates the
scope of the pure coordinator and the downstream global relation separately:
the coordinator can carry the candidate, while global refinement must reject a
balance delta whose principal no longer names the source owner.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

import src.core.asset_lane_custody_coordinator_v2 as coordinator
from src.core.asset_lane_custody_coordinator_v2 import AssetLaneCustodyAcceptedV2
from src.core.asset_lane_custody_global_v2 import derive_asset_lane_custody_global_post_v2
from src.core.asset_lane_custody_input_v2 import (
    prepare_asset_lane_custody_global_prover_input_v2,
)
from src.core.asset_transfer_types_v2 import AssetTransferAcceptedV2, AssetTransferStateV2
from src.core.global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    LaneIdV2,
    LaneWriteV2,
    canonical_global_bytes_v2,
    hash_global_v2,
)
from src.integration.custody_publication_record_v2 import replay_custody_publication_frame_v2
from tests.core.test_asset_lane_custody_statement_v2 import _case

_EXPECTED_TRANSFER_EFFECTS = (
    EconomicEffectRowV2(EconomicEffectKindV2.ACCOUNT_MOVEMENT, "alice", "USD", "accounts", -12),
    EconomicEffectRowV2(EconomicEffectKindV2.ACCOUNT_MOVEMENT, "bob", "USD", "accounts", 10),
    EconomicEffectRowV2(EconomicEffectKindV2.ACCOUNT_MOVEMENT, "treasury", "USD", "accounts", 2),
    EconomicEffectRowV2(EconomicEffectKindV2.FEE_ALLOCATION, "treasury", "USD", "accounts", 2),
)


def test_given_genuine_transfer_when_prepared_and_replayed_then_effect_ancestry_is_preserved():
    """A genuine frame reproduces the exact transfer rows through pure replay."""

    context, lane, command, genuine, global_pre, expected_global_post = _case()
    lane_pre_bytes = canonical_global_bytes_v2(lane.to_canonical())
    global_pre_bytes = canonical_global_bytes_v2(global_pre)

    assert type(genuine) is AssetLaneCustodyAcceptedV2
    assert genuine.effects.rows == _EXPECTED_TRANSFER_EFFECTS
    assert (
        derive_asset_lane_custody_global_post_v2(lane, genuine, global_pre, context.occurrence)
        == expected_global_post
    )

    frame = prepare_asset_lane_custody_global_prover_input_v2(context, lane, command, global_pre)
    assert type(frame) is bytes

    replay = replay_custody_publication_frame_v2(frame)
    assert replay.lane_pre == lane
    assert replay.global_pre == global_pre
    assert replay.global_post == expected_global_post

    replayed = coordinator.transition_asset_lane_custody_v2(
        replay.context, replay.lane_pre, replay.command
    )
    assert type(replayed) is AssetLaneCustodyAcceptedV2
    assert replayed.post_state == genuine.post_state
    assert replayed.effects.rows == _EXPECTED_TRANSFER_EFFECTS
    assert replayed.effects.rows == genuine.effects.rows
    assert all(row.principal != "mallory" for row in replayed.effects.rows)

    assert canonical_global_bytes_v2(lane.to_canonical()) == lane_pre_bytes
    assert canonical_global_bytes_v2(global_pre) == global_pre_bytes


def test_given_constructor_valid_misattributed_leaf_when_refined_then_global_row_delta_rejects_before_frame(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A principal substitution reaches refinement and yields no proving frame."""

    context, lane, command, genuine, global_pre, _ = _case()
    lane_pre_bytes = canonical_global_bytes_v2(lane.to_canonical())
    global_pre_bytes = canonical_global_bytes_v2(global_pre)

    leaf = coordinator.transition_asset_transfer_v2(
        context.transfer_context(), lane.transfer_state, command
    )
    assert type(leaf) is AssetTransferAcceptedV2
    forged_rows = tuple(
        sorted(
            (
                replace(row, principal="mallory")
                if row.kind is EconomicEffectKindV2.ACCOUNT_MOVEMENT
                and row.principal == command.sender
                else row
                for row in leaf.effects.rows
            ),
            key=lambda row: row.key,
        )
    )
    faulty_effects = replace(leaf.effects, rows=forged_rows)
    faulty_leaf = AssetTransferAcceptedV2(
        leaf.post_state,
        faulty_effects,
        replace(leaf.module_journal, effect_plan_root=faulty_effects.effect_plan_root),
    )

    assert coordinator._source_holds(context, lane, faulty_leaf)
    assert coordinator._account_projection_holds(lane, command.asset, faulty_leaf)
    assert faulty_leaf.effects.rows == tuple(
        sorted(
            (
                *_EXPECTED_TRANSFER_EFFECTS[1:],
                replace(_EXPECTED_TRANSFER_EFFECTS[0], principal="mallory"),
            ),
            key=lambda row: row.key,
        )
    )

    monkeypatch.setattr(coordinator, "transition_asset_transfer_v2", lambda *_: faulty_leaf)
    forged_accepted = coordinator.transition_asset_lane_custody_v2(context, lane, command)
    assert type(forged_accepted) is AssetLaneCustodyAcceptedV2
    assert forged_accepted.post_state == genuine.post_state
    assert forged_accepted.effects.rows == faulty_leaf.effects.rows
    assert any(row.principal == "mallory" for row in forged_accepted.effects.rows)

    with pytest.raises(ValueError) as refinement_error:
        derive_asset_lane_custody_global_post_v2(
            lane, forged_accepted, global_pre, context.occurrence
        )
    assert str(refinement_error.value) == "global refinement balances state/effect mismatch"

    with pytest.raises(ValueError) as preparation_error:
        prepare_asset_lane_custody_global_prover_input_v2(context, lane, command, global_pre)
    assert str(preparation_error.value) == str(refinement_error.value)

    assert canonical_global_bytes_v2(lane.to_canonical()) == lane_pre_bytes
    assert canonical_global_bytes_v2(global_pre) == global_pre_bytes


def test_coherent_recipient_reroute_is_rejected_by_independent_frame_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Matching state/effect forgery is caught by replaying the actual command."""

    context, lane, command, _, global_pre, expected_post = _case()
    original = canonical_global_bytes_v2(global_pre)
    genuine_frame = prepare_asset_lane_custody_global_prover_input_v2(
        context, lane, command, global_pre
    )
    assert replay_custody_publication_frame_v2(genuine_frame).global_post == expected_post
    leaf_context = context.transfer_context()
    leaf = coordinator.transition_asset_transfer_v2(leaf_context, lane.transfer_state, command)
    assert type(leaf) is AssetTransferAcceptedV2
    balances = tuple(
        sorted(
            (
                replace(row, owner="mallory")
                if row.asset == command.asset and row.owner == command.recipient
                else row
                for row in leaf.post_state.balances
            ),
            key=lambda row: row.key,
        )
    )
    post = AssetTransferStateV2(
        leaf.post_state.module_release_id,
        leaf.post_state.policies,
        balances,
        leaf.post_state.supplies,
    )
    rows = tuple(
        sorted(
            (
                replace(row, principal="mallory")
                if row.kind is EconomicEffectKindV2.ACCOUNT_MOVEMENT
                and row.principal == command.recipient
                else row
                for row in leaf.effects.rows
            ),
            key=lambda row: row.key,
        )
    )
    effects = replace(
        leaf.effects,
        rows=rows,
        lane_writes=(
            LaneWriteV2(
                LaneIdV2.ASSET_TRANSFER,
                lane.transfer_state.state_root,
                post.state_root,
            ),
        ),
    )
    receipt = hash_global_v2(
        "asset-transfer-receipt-v2",
        {
            "context": leaf_context,
            "command": command,
            "pre_state_root": lane.transfer_state.state_root,
            "post_state_root": post.state_root,
            "effect_plan_root": effects.effect_plan_root,
            "private_port_root": ZERO_ROOT_V2,
            "terminal_obligations_root": ZERO_ROOT_V2,
            "oracle_occurrence_plan_root": ZERO_ROOT_V2,
        },
    )
    faulty = AssetTransferAcceptedV2(
        post,
        effects,
        replace(
            leaf.module_journal,
            post_lane_root=post.state_root,
            effect_plan_root=effects.effect_plan_root,
            receipt_root=receipt,
        ),
    )
    assert coordinator._source_holds(context, lane, faulty)
    assert coordinator._account_projection_holds(lane, command.asset, faulty)
    assert post.balance_atoms(command.recipient, command.asset) == 0
    assert post.balance_atoms("mallory", command.asset) == command.amount_atoms

    with monkeypatch.context() as patcher:
        patcher.setattr(coordinator, "transition_asset_transfer_v2", lambda *_: faulty)
        accepted = coordinator.transition_asset_lane_custody_v2(context, lane, command)
        assert type(accepted) is AssetLaneCustodyAcceptedV2
        frame = prepare_asset_lane_custody_global_prover_input_v2(
            context,
            lane,
            command,
            global_pre,
        )
        assert type(frame) is bytes

    with pytest.raises(ValueError) as error:
        replay_custody_publication_frame_v2(frame)
    assert str(error.value) == "custody lane/global complete projection mismatch"
    assert canonical_global_bytes_v2(global_pre) == original
