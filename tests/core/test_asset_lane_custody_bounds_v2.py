"""Aggregate resource rejection must preserve the complete custody pre-state."""

from dataclasses import replace
from typing import cast

import pytest

import src.core.asset_lane_custody_coordinator_v2 as coordinator
from src.core.asset_lane_coordinator_values_v2 import (
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
)
from src.core.asset_lane_custody_coordinator_v2 import AssetLaneCustodyAcceptedV2
from src.core.asset_lane_custody_state_v2 import (
    MAX_ASSET_LANE_CUSTODY_ROWS_V2,
    AssetLaneCustodyStateV2,
)
from src.core.asset_transfer_types_v2 import (
    MAX_ASSET_TRANSFER_BALANCE_ROWS_V2,
    AssetTransferStateV2,
)
from src.core.global_settlement_resource_limits_v2 import (
    MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
)
from src.core.global_settlement_types_v2 import (
    MAX_TOKEN_BYTES_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleStateV2,
)
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_command,
    _registry,
    _transfer_policy,
)
from tests.core.test_asset_lane_custody_v2 import custody_state


def _assert_exact_coordinator_noop(
    result: object,
    state: AssetLaneCustodyStateV2,
    code: AssetLaneCoordinatorRejectCodeV2,
) -> None:
    assert type(result) is AssetLaneRejectedV2
    rejected = cast(AssetLaneRejectedV2, result)
    assert rejected.route is AssetLaneRouteV2.COORDINATOR
    assert rejected.code is code
    assert rejected.pre_state_root == rejected.post_state_root == state.state_root
    assert rejected.effects.rows == ()
    assert rejected.effects.asset_conservation == ()
    assert rejected.effects.fee_conservation == ()
    assert rejected.effects.lane_writes == ()
    assert rejected.effects.occurrence_consumptions == ()
    assert rejected.effects.external_outbox_enqueue == ()


def test_aggregate_row_growth_is_noop_and_corrupt_projection_has_prior_rejection(monkeypatch):
    base = custody_state()
    policies = (_transfer_policy(asset="EUR"), *base.transfer_state.policies)
    balances = (
        *(EconomicAmountV2(f"owner-{i:04d}", "EUR", "accounts", 1) for i in range(4095)),
        *base.transfer_state.balances,
    )
    state = AssetLaneCustodyStateV2(
        AssetTransferStateV2(
            base.transfer_state.module_release_id,
            policies,
            balances,
            (AssetSupplyV2("EUR", 4095), *base.transfer_state.supplies),
        ),
        _registry(policies, base.managed_policies),
        base.managed_policies,
        base.custody,
    )
    original = state.to_canonical()
    command = _managed_command(owner="bob", amount_atoms=1)
    context = _context(command)
    leaf = coordinator.transition_managed_asset_lifecycle_v2(
        context.managed_context(), state.managed_leaf_state(), command
    )
    assert isinstance(leaf, ManagedAssetLifecycleAcceptedV2)
    assert len(leaf.post_state.balances) == 2
    result = coordinator.transition_asset_lane_custody_v2(context, state, command)
    _assert_exact_coordinator_noop(
        result,
        state,
        AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT,
    )

    row = leaf.effects.asset_conservation[0]
    effects = replace(
        leaf.effects,
        asset_conservation=(
            replace(row, owned_and_custodied_pre_atoms=100, owned_and_custodied_post_atoms=101),
        ),
    )
    corrupt = ManagedAssetLifecycleAcceptedV2(
        leaf.post_state,
        effects,
        replace(leaf.module_journal, effect_plan_root=effects.effect_plan_root),
    )
    monkeypatch.setattr(coordinator, "transition_managed_asset_lifecycle_v2", lambda *_: corrupt)
    result = coordinator.transition_asset_lane_custody_v2(context, state, command)
    _assert_exact_coordinator_noop(
        result,
        state,
        AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
    )
    assert state.to_canonical() == original


def test_complete_managed_projection_requires_exact_leaf_state_even_when_roots_match(
    monkeypatch,
):
    """Complete admission requires exact leaf equality, beyond equal roots."""

    state = custody_state()
    original = state.to_canonical()
    original_root = state.state_root
    command = _managed_command(owner="bob", amount_atoms=1)
    context = _context(command)
    collision = "0x" + "11" * 32
    monkeypatch.setattr(
        ManagedAssetLifecycleStateV2,
        "state_root",
        property(lambda _state: collision),
    )

    leaf = coordinator.transition_managed_asset_lifecycle_v2(
        context.managed_context(), state.managed_leaf_state(), command
    )
    assert type(leaf) is ManagedAssetLifecycleAcceptedV2
    genuine = coordinator.transition_asset_lane_custody_v2(context, state, command)
    assert type(genuine) is AssetLaneCustodyAcceptedV2
    assert genuine.post_state.managed_leaf_state() == leaf.post_state

    leaf_post = leaf.post_state
    forged_post = ManagedAssetLifecycleStateV2(
        leaf_post.module_release_id,
        (replace(leaf_post.policies[0], enabled=False),),
        leaf_post.balances,
        leaf_post.supplies,
    )
    assert forged_post != leaf_post
    assert forged_post.state_root == leaf_post.state_root == collision
    forged = ManagedAssetLifecycleAcceptedV2(
        forged_post,
        leaf.effects,
        leaf.module_journal,
    )
    assert forged.effects == leaf.effects
    assert forged.module_journal == leaf.module_journal
    monkeypatch.setattr(coordinator, "transition_managed_asset_lifecycle_v2", lambda *_: forged)

    result = coordinator.transition_asset_lane_custody_v2(context, state, command)

    _assert_exact_coordinator_noop(
        result,
        state,
        AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
    )
    assert state.to_canonical() == original
    assert state.state_root == original_root


@pytest.mark.parametrize(
    ("last_domain_bytes", "pre_headroom", "post_excess", "accepted"),
    ((53, 232, 0, True), (54, 231, 1, False)),
    ids=("exact-byte-ceiling", "one-byte-over"),
)
def test_complete_canonical_byte_boundary_after_finite_leaf_acceptance(
    last_domain_bytes: int,
    pre_headroom: int,
    post_excess: int,
    accepted: bool,
) -> None:
    """The complete-state byte bound owns the final one-byte decision."""

    base = custody_state()
    policies = (_transfer_policy(asset="EUR"), *base.transfer_state.policies)
    registry = _registry(policies, base.managed_policies)
    custody_row_count = 2_724
    custody = tuple(
        EconomicAmountV2(
            (prefix := f"v{index:04d}") + "x" * (MAX_TOKEN_BYTES_V2 - len(prefix)),
            "EUR",
            "e"
            * (MAX_TOKEN_BYTES_V2 if index < custody_row_count - 1 else last_domain_bytes),
            1,
        )
        for index in range(custody_row_count)
    )
    transfer = AssetTransferStateV2(
        base.transfer_state.module_release_id,
        policies,
        base.transfer_state.balances,
        (AssetSupplyV2("EUR", custody_row_count), *base.transfer_state.supplies),
    )
    state = AssetLaneCustodyStateV2(
        transfer,
        registry,
        base.managed_policies,
        (*custody, *base.custody),
    )
    original = state.to_canonical()
    original_root = state.state_root
    issue_owner = "i" * MAX_TOKEN_BYTES_V2
    command = _managed_command(owner=issue_owner, amount_atoms=1)
    context = _context(command)

    leaf = coordinator.transition_managed_asset_lifecycle_v2(
        context.managed_context(), state.managed_leaf_state(), command
    )
    assert type(leaf) is ManagedAssetLifecycleAcceptedV2
    assert (
        len(canonical_global_bytes_v2(leaf.post_state.to_canonical()))
        < MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
    )
    expected_transfer = AssetTransferStateV2(
        transfer.module_release_id,
        transfer.policies,
        leaf.post_state.balances,
        (transfer.supplies[0], *leaf.post_state.supplies),
    )
    expected_post = original | {"transfer_state": expected_transfer}
    assert len(state.custody) <= MAX_ASSET_LANE_CUSTODY_ROWS_V2
    assert len(expected_transfer.balances) <= MAX_ASSET_TRANSFER_BALANCE_ROWS_V2
    assert len(canonical_global_bytes_v2(original)) == (
        MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2 - pre_headroom
    )
    assert len(canonical_global_bytes_v2(expected_post)) == (
        MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2 + post_excess
    )

    result = coordinator.transition_asset_lane_custody_v2(context, state, command)

    if accepted:
        assert type(result) is AssetLaneCustodyAcceptedV2
        assert result.post_state.transfer_state == expected_transfer
        assert len(canonical_global_bytes_v2(result.post_state.to_canonical())) == (
            MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
        )
    else:
        _assert_exact_coordinator_noop(
            result,
            state,
            AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT,
        )
    assert state.to_canonical() == original
    assert state.state_root == original_root
