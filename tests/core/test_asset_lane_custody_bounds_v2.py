"""Aggregate resource rejection must preserve the complete custody pre-state."""

from dataclasses import replace

import src.core.asset_lane_custody_coordinator_v2 as coordinator
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_transfer_types_v2 import AssetTransferStateV2
from src.core.global_settlement_types_v2 import AssetSupplyV2, EconomicAmountV2
from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecycleAcceptedV2
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_command,
    _registry,
    _transfer_policy,
)
from tests.core.test_asset_lane_custody_v2 import custody_state


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
    assert result.code.value == "STATE_RESOURCE_LIMIT"
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty

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
    assert result.code.value == "PROJECTION_MISMATCH"
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty
    assert state.to_canonical() == original
