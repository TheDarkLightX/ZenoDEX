"""Ordered custody-coordinator outcomes for faulty internal leaf results."""

from dataclasses import replace

import pytest

import src.core.asset_lane_custody_coordinator_v2 as coordinator
from src.core.asset_lane_coordinator_values_v2 import (
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
)
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.asset_transfer_types_v2 import AssetTransferAcceptedV2, AssetTransferStateV2
from src.core.global_settlement_types_v2 import (
    AssetConservationRowV2,
    AssetSupplyV2,
    EconomicAmountV2,
    ExternalOutboxEnqueueV2,
    LaneIdV2,
    LaneWriteV2,
)
from src.core.managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleStateV2,
)
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_command,
    _registry,
    _root,
    _transfer_command,
    _transfer_policy,
)
from tests.core.test_asset_lane_custody_bindings_v2 import _two_asset_custody_state
from tests.core.test_asset_lane_custody_v2 import custody_state


def _assert_exact_coordinator_noop(
    result: object,
    state: AssetLaneCustodyStateV2,
    code: AssetLaneCoordinatorRejectCodeV2,
) -> None:
    assert type(result) is AssetLaneRejectedV2
    assert result.route is AssetLaneRouteV2.COORDINATOR
    assert result.code is code
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.rows == ()
    assert result.effects.asset_conservation == ()
    assert result.effects.fee_conservation == ()
    assert result.effects.lane_writes == ()
    assert result.effects.occurrence_consumptions == ()
    assert result.effects.external_outbox_enqueue == ()


def _resource_subject() -> tuple[
    AssetLaneContextV2,
    AssetLaneCustodyStateV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleAcceptedV2,
]:
    base = custody_state()
    policies = (_transfer_policy(asset="EUR"), *base.transfer_state.policies)
    balances = (
        *(EconomicAmountV2(f"owner-{index:04d}", "EUR", "accounts", 1) for index in range(4095)),
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
    command = _managed_command(owner="bob", amount_atoms=1)
    context = _context(command)
    leaf = coordinator.transition_managed_asset_lifecycle_v2(
        context.managed_context(), state.managed_leaf_state(), command
    )
    assert type(leaf) is ManagedAssetLifecycleAcceptedV2
    return context, state, command, leaf


def test_extra_conservation_row_is_an_exact_projection_noop(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A leaf cannot expand the coordinator-owned conservation asset set."""

    state = _two_asset_custody_state()
    original = state.to_canonical()
    command = replace(
        _transfer_command(
            sender="carol",
            recipient="dave",
            amount_atoms=1,
            max_fee_atoms=0,
        ),
        asset="EUR",
        asset_origin_root=_root("origin:EUR"),
    )
    context = _context(command)
    genuine = coordinator.transition_asset_lane_custody_v2(context, state, command)
    assert type(genuine) is coordinator.AssetLaneCustodyAcceptedV2

    leaf = coordinator.transition_asset_transfer_v2(
        context.transfer_context(), state.transfer_state, command
    )
    assert type(leaf) is AssetTransferAcceptedV2
    accepted = leaf
    effects = replace(
        accepted.effects,
        asset_conservation=(
            accepted.effects.asset_conservation[0],
            AssetConservationRowV2("USD", 100, 100, 100, 100, 0, 0),
        ),
    )
    faulty = AssetTransferAcceptedV2(
        accepted.post_state,
        effects,
        replace(accepted.module_journal, effect_plan_root=effects.effect_plan_root),
    )
    assert coordinator._source_holds(context, state, faulty)
    monkeypatch.setattr(coordinator, "transition_asset_transfer_v2", lambda *_: faulty)

    result = coordinator.transition_asset_lane_custody_v2(context, state, command)

    _assert_exact_coordinator_noop(
        result,
        state,
        AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
    )
    assert state.to_canonical() == original


def test_leaf_external_outbox_is_a_candidate_binding_noop(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A leaf cannot inject external work into this coordinator."""

    state = custody_state()
    original = state.to_canonical()
    command = _transfer_command(amount_atoms=10)
    context = _context(command)
    genuine = coordinator.transition_asset_lane_custody_v2(context, state, command)
    assert type(genuine) is coordinator.AssetLaneCustodyAcceptedV2

    leaf = coordinator.transition_asset_transfer_v2(
        context.transfer_context(), state.transfer_state, command
    )
    assert type(leaf) is AssetTransferAcceptedV2
    accepted = leaf
    effects = replace(
        accepted.effects,
        external_outbox_enqueue=(
            ExternalOutboxEnqueueV2(
                _root("outbox-effect"),
                "external:bridge",
                _root("outbox-payload"),
                _root("outbox-adapter"),
            ),
        ),
    )
    faulty = AssetTransferAcceptedV2(
        accepted.post_state,
        effects,
        replace(accepted.module_journal, effect_plan_root=effects.effect_plan_root),
    )
    monkeypatch.setattr(coordinator, "transition_asset_transfer_v2", lambda *_: faulty)

    result = coordinator.transition_asset_lane_custody_v2(context, state, command)

    _assert_exact_coordinator_noop(
        result,
        state,
        AssetLaneCoordinatorRejectCodeV2.CANDIDATE_BINDING_MISMATCH,
    )
    assert state.to_canonical() == original


def test_source_binding_precedes_projection_and_aggregate_resource_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    context, state, command, accepted = _resource_subject()
    original = state.to_canonical()
    control = coordinator.transition_asset_lane_custody_v2(context, state, command)
    _assert_exact_coordinator_noop(
        control,
        state,
        AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT,
    )
    row = accepted.effects.asset_conservation[0]
    effects = replace(
        accepted.effects,
        asset_conservation=(
            replace(
                row,
                owned_and_custodied_pre_atoms=row.owned_and_custodied_pre_atoms + 1,
                owned_and_custodied_post_atoms=row.owned_and_custodied_post_atoms + 1,
            ),
        ),
    )
    faulty = ManagedAssetLifecycleAcceptedV2(
        accepted.post_state,
        effects,
        replace(
            accepted.module_journal,
            chain_id="foreign-chain",
            effect_plan_root=effects.effect_plan_root,
        ),
    )
    monkeypatch.setattr(coordinator, "transition_managed_asset_lifecycle_v2", lambda *_: faulty)

    result = coordinator.transition_asset_lane_custody_v2(context, state, command)

    _assert_exact_coordinator_noop(
        result,
        state,
        AssetLaneCoordinatorRejectCodeV2.CANDIDATE_BINDING_MISMATCH,
    )
    assert state.to_canonical() == original


def test_aggregate_resource_failure_precedes_late_exact_reprojection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    context, state, command, accepted = _resource_subject()
    original = state.to_canonical()
    control = coordinator.transition_asset_lane_custody_v2(context, state, command)
    _assert_exact_coordinator_noop(
        control,
        state,
        AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT,
    )
    leaf_post = accepted.post_state
    changed_post = ManagedAssetLifecycleStateV2(
        leaf_post.module_release_id,
        (replace(leaf_post.policies[0], enabled=False),),
        leaf_post.balances,
        leaf_post.supplies,
    )
    assert changed_post.policies != leaf_post.policies
    effects = replace(
        accepted.effects,
        lane_writes=(
            LaneWriteV2(
                LaneIdV2.ASSET_TRANSFER,
                accepted.module_journal.pre_lane_root,
                changed_post.state_root,
            ),
        ),
    )
    faulty = ManagedAssetLifecycleAcceptedV2(
        changed_post,
        effects,
        replace(
            accepted.module_journal,
            post_lane_root=changed_post.state_root,
            effect_plan_root=effects.effect_plan_root,
        ),
    )
    assert coordinator._source_holds(context, state, faulty)
    monkeypatch.setattr(coordinator, "transition_managed_asset_lifecycle_v2", lambda *_: faulty)

    result = coordinator.transition_asset_lane_custody_v2(context, state, command)

    _assert_exact_coordinator_noop(
        result,
        state,
        AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT,
    )
    assert state.to_canonical() == original
