"""Custody transfer must preserve claimants in the actual global refinement."""

from dataclasses import replace

import pytest

from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_global_v2 import refine_asset_lane_custody_global_v2
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.asset_transfer_types_v2 import AssetTransferStateV2
from src.core.global_economic_state_v2 import GlobalEconomicStateV2, LaneStateRootV2, ReplayStateV2
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    ZERO_ROOT_V2,
    EconomicAmountV2,
    LaneIdV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
)
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_command,
    _registry,
    _root,
    _transfer_command,
)
from tests.core.test_asset_lane_custody_v2 import custody_state


def global_case(lane=None, command=None):
    lane = custody_state() if lane is None else lane
    command = _transfer_command(amount_atoms=10) if command is None else command
    context = _context(command)
    occurrence = context.occurrence
    pre = GlobalEconomicStateV2(
        occurrence.chain_id,
        occurrence.deployment_root,
        context.writer_epoch,
        occurrence.height - 1,
        occurrence.profile_root,
        tuple(
            LaneStateRootV2(
                lane_id,
                lane.transfer_state.module_release_id
                if lane_id is LaneIdV2.ASSET_TRANSFER
                else _root(lane_id.value),
                lane_id is LaneIdV2.ASSET_TRANSFER,
                lane.state_root if lane_id is LaneIdV2.ASSET_TRANSFER else ZERO_ROOT_V2,
            )
            for lane_id in ALL_LANE_IDS_V2
        ),
        balances=lane.transfer_state.balances,
        supplies=tuple(row for row in lane.transfer_state.supplies if row.amount_atoms),
        custody=lane.custody,
        liabilities=(EconomicAmountV2("alice", "USD", "escrow", 20),) if lane.custody else (),
        terminal_obligations=(
            TerminalObligationV2(
                "alice-vault-claim",
                LaneIdV2.ASSET_TRANSFER,
                "alice",
                "USD",
                "escrow",
                20,
                TerminalObligationStatusV2.OPEN,
            ),
        )
        if lane.custody
        else (),
    )
    occurrence = replace(occurrence, pre_state_root=pre.state_root)
    context = AssetLaneContextV2(
        context.writer_epoch, context.module_release_id, pre.state_root, occurrence
    )
    accepted = transition_asset_lane_custody_v2(context, lane, command)
    assert isinstance(accepted, AssetLaneCustodyAcceptedV2)
    post = replace(
        pre,
        height=occurrence.height,
        balances=accepted.post_state.transfer_state.balances,
        supplies=tuple(r for r in accepted.post_state.transfer_state.supplies if r.amount_atoms),
        lane_roots=tuple(
            replace(row, state_root=accepted.post_state.state_root)
            if row.lane_id is LaneIdV2.ASSET_TRANSFER
            else row
            for row in pre.lane_roots
        ),
        replay_state=(ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id),),
    )
    return lane, accepted, pre, post, occurrence


def test_given_backed_claim_when_transfer_then_global_checker_accepts_complete_frame():
    lane, accepted, pre, post, occurrence = global_case()
    checked = refine_asset_lane_custody_global_v2(lane, accepted, pre, post, occurrence)
    assert checked.pre_state_root == pre.state_root
    assert checked.post_state_root == post.state_root
    assert checked.effect_plan_root == accepted.effects.effect_plan_root
    assert pre.liabilities == post.liabilities
    assert pre.custody == post.custody
    assert checked.production_authority == "NONE"


@pytest.mark.parametrize(
    "kind,accounts,vault,amount,supply",
    (
        ("managed_asset_issue", 80, 20, 7, 107),
        ("managed_asset_burn", 80, 20, 80, 20),
        ("managed_asset_issue", 0, 0, 1, 1),
        ("managed_asset_burn", 1, 0, 1, 0),
    ),
)
def test_managed_custody_and_dormant_states_reach_global_admission(
    kind, accounts, vault, amount, supply
):
    case = global_case(
        custody_state(accounts, vault), _managed_command(kind=kind, amount_atoms=amount)
    )
    lane, accepted, pre, post, occurrence = case
    checked = refine_asset_lane_custody_global_v2(*case)
    assert checked.post_state_root == post.state_root
    assert accepted.post_state.transfer_state.supply_atoms("USD") == supply
    assert accepted.post_state.custody == pre.custody == post.custody
    assert pre.liabilities == post.liabilities


def test_sender_fee_owner_retains_the_specified_global_fee_mirror_refusal():
    lane = custody_state()
    leaf = lane.transfer_state
    policies = (replace(leaf.policies[0], fee_owner="alice"),)
    lane = AssetLaneCustodyStateV2(
        AssetTransferStateV2(leaf.module_release_id, policies, leaf.balances, leaf.supplies),
        _registry(policies, lane.managed_policies),
        lane.managed_policies,
        lane.custody,
    )
    case = global_case(lane)
    assert isinstance(case[1], AssetLaneCustodyAcceptedV2)
    with pytest.raises(ValueError, match="fee allocation is not mirrored"):
        refine_asset_lane_custody_global_v2(*case)


@pytest.mark.parametrize(
    "changed",
    (
        "claimant",
        "custody_owner",
        "custody_domain",
        "omitted_custody",
        "wrong_lane_root",
        "missing_replay",
    ),
)
def test_semantic_mutants_cannot_pass_the_global_consumer(changed):
    lane, accepted, pre, post, occurrence = global_case()
    mutations = {
        "claimant": {"liabilities": (replace(post.liabilities[0], owner="mallory"),)},
        "custody_owner": {"custody": (replace(post.custody[0], owner="mallory"),)},
        "custody_domain": {"custody": (replace(post.custody[0], custody_domain="foreign"),)},
        "omitted_custody": {"custody": ()},
        "wrong_lane_root": {
            "lane_roots": tuple(
                replace(row, state_root=_root("wrong-lane"))
                if row.lane_id is LaneIdV2.ASSET_TRANSFER
                else row
                for row in post.lane_roots
            )
        },
        "missing_replay": {"replay_state": ()},
    }
    forged = replace(post, **mutations[changed])
    original_root = pre.state_root
    expected_error = {
        "claimant": "claimant or custody frame changed",
        "missing_replay": "replay post-state mismatch",
    }.get(changed, "complete projection mismatch")
    with pytest.raises(ValueError, match=expected_error):
        refine_asset_lane_custody_global_v2(lane, accepted, pre, forged, occurrence)
    assert pre.state_root == original_root


def test_wrong_writer_epoch_is_rejected_despite_conserved_totals():
    lane, accepted, pre, post, occurrence = global_case()
    object.__setattr__(
        accepted,
        "_module_journal",
        replace(accepted.module_journal, writer_epoch=pre.writer_epoch + 1),
    )
    with pytest.raises(ValueError, match="source journal binding"):
        refine_asset_lane_custody_global_v2(lane, accepted, pre, post, occurrence)


@pytest.mark.parametrize(
    "field", ("receipt_root", "source_leaf_journal_root", "source_leaf_receipt_root")
)
def test_global_consumer_revalidates_the_received_successor_receipt(field):
    lane, accepted, pre, post, occurrence = global_case()
    if field == "receipt_root":
        object.__setattr__(
            accepted,
            "_module_journal",
            replace(accepted.module_journal, receipt_root=_root("foreign-receipt")),
        )
    else:
        object.__setattr__(accepted, field, _root("foreign-source"))
    with pytest.raises(ValueError, match="custody acceptance bindings differ"):
        refine_asset_lane_custody_global_v2(lane, accepted, pre, post, occurrence)
