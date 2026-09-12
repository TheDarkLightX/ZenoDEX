"""Runtime witnesses for metadata erased by the custody Lean state model."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.asset_lane_coordinator_values_v2 import (
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
)
from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.asset_origin_registry_types_v2 import AssetOriginRegistryStateV2
from src.core.asset_origin_registry_v2 import (
    asset_transfer_policy_root_v2,
    managed_asset_policy_root_v2,
)
from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    AssetTransferPolicyV2,
    AssetTransferRejectCodeV2,
    AssetTransferRejectedV2,
    AssetTransferStateV2,
)
from src.core.global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    GlobalEconomicEffectPlanV2,
)
from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecyclePolicyV2
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_policy,
    _registry,
    _root,
    _transfer_command,
    _transfer_policy,
)


def _transfer_state(policy: AssetTransferPolicyV2) -> AssetTransferStateV2:
    return AssetTransferStateV2(
        _root("module-release"),
        (policy,),
        (EconomicAmountV2("alice", "USD", "accounts", 100),),
        (AssetSupplyV2("USD", 100),),
    )


def _erased_c_state(
    transfer: AssetTransferStateV2,
    registry: AssetOriginRegistryStateV2,
    managed: tuple[ManagedAssetLifecyclePolicyV2, ...],
) -> tuple[object, ...]:
    """Mirror fields retained by AssetLaneCustodyRefinementV2.State."""

    return (transfer, tuple(row.asset for row in registry.assets), managed, ())


def _structural_row_facts(
    transfer: AssetTransferStateV2,
    registry: AssetOriginRegistryStateV2,
    managed: tuple[ManagedAssetLifecyclePolicyV2, ...],
) -> tuple[object, ...]:
    return (
        tuple(policy.asset for policy in transfer.policies),
        tuple(row.asset for row in registry.assets),
        tuple(policy.asset for policy in managed),
        transfer.balances,
        transfer.supplies,
        (),
    )


def test_issue_policy_root_erasure_hides_constructor_invalid_managed_subset() -> None:
    transfer_policy, managed_policy = _transfer_policy(), _managed_policy()
    transfer = _transfer_state(transfer_policy)
    registry = _registry((transfer_policy,), (managed_policy,))
    valid = AssetLaneCustodyStateV2(transfer, registry, (managed_policy,), ())
    disabled_registry = AssetOriginRegistryStateV2(
        module_release_id=registry.module_release_id,
        policy=registry.policy,
        assets=(replace(registry.assets[0], issue_policy_root=ZERO_ROOT_V2),),
    )

    assert _erased_c_state(transfer, registry, (managed_policy,)) == _erased_c_state(
        transfer, disabled_registry, (managed_policy,)
    )
    assert valid.managed_policies == (managed_policy,)
    with pytest.raises(ValueError, match="custody lane managed policy coverage differs"):
        AssetLaneCustodyStateV2(transfer, disabled_registry, (managed_policy,), ())


def test_structural_row_facts_do_not_admit_transfer_managed_identity_drift() -> None:
    transfer_policy, managed_policy = _transfer_policy(), _managed_policy()
    transfer = _transfer_state(transfer_policy)
    registry = _registry((transfer_policy,), (managed_policy,))
    valid = AssetLaneCustodyStateV2(transfer, registry, (managed_policy,), ())
    drifted_managed = replace(managed_policy, asset_origin_root=_root("managed-origin-drift"))
    drifted_registry = _registry((transfer_policy,), (drifted_managed,))

    assert _structural_row_facts(
        valid.transfer_state, valid.origin_registry, valid.managed_policies
    ) == _structural_row_facts(transfer, drifted_registry, (drifted_managed,))
    with pytest.raises(ValueError, match="custody lane transfer and managed identities differ"):
        AssetLaneCustodyStateV2(transfer, drifted_registry, (drifted_managed,), ())


def test_joint_policy_root_drift_precedes_an_independent_leaf_rejection() -> None:
    transfer_policy, managed_policy = _transfer_policy(), _managed_policy()
    registry = _registry((transfer_policy,), (managed_policy,))
    original_state = AssetLaneCustodyStateV2(
        _transfer_state(transfer_policy), registry, (managed_policy,), ()
    )
    drifted_transfer = replace(transfer_policy, fee_owner="drifted-treasury")
    drifted_managed = replace(
        managed_policy, issue_authorization_root=_root("drifted-issue-authorization")
    )
    state = AssetLaneCustodyStateV2(
        _transfer_state(drifted_transfer), registry, (drifted_managed,), ()
    )
    record = registry.record_for("USD")
    assert record is not None
    assert record.transfer_policy_root != asset_transfer_policy_root_v2(drifted_transfer)
    assert record.issue_policy_root != managed_asset_policy_root_v2(drifted_managed)

    command = _transfer_command(amount_atoms=1)
    accepted = transition_asset_lane_custody_v2(_context(command), original_state, command)
    assert type(accepted) is AssetLaneCustodyAcceptedV2

    source_context = _context(command)
    context = AssetLaneContextV2(
        source_context.writer_epoch,
        source_context.module_release_id,
        source_context.global_pre_state_root,
        None,
    )
    original_root = original_state.state_root
    original_missing = transition_asset_lane_custody_v2(context, original_state, command)
    assert type(original_missing) is AssetLaneRejectedV2
    original_rejected = original_missing
    assert original_rejected.route is AssetLaneRouteV2.TRANSFER
    assert original_rejected.code is AssetTransferRejectCodeV2.MISSING_OCCURRENCE
    assert original_rejected.pre_state_root == original_rejected.post_state_root == original_root
    assert original_rejected.effects == GlobalEconomicEffectPlanV2.empty()

    leaf_result = transition_asset_transfer_v2(
        context.transfer_context(), state.transfer_state, command
    )
    assert type(leaf_result) is AssetTransferRejectedV2
    leaf_rejected = leaf_result
    assert leaf_rejected.code is AssetTransferRejectCodeV2.MISSING_OCCURRENCE

    before, before_root = state.to_canonical(), state.state_root
    result = transition_asset_lane_custody_v2(context, state, command)
    assert type(result) is AssetLaneRejectedV2
    rejected = result
    assert rejected.route is AssetLaneRouteV2.COORDINATOR
    assert rejected.code is AssetLaneCoordinatorRejectCodeV2.REGISTRY_BINDING_MISMATCH
    assert rejected.pre_state_root == rejected.post_state_root == before_root
    assert rejected.effects == GlobalEconomicEffectPlanV2.empty()
    assert state.to_canonical() == before
    assert state.state_root == before_root
