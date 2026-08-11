from __future__ import annotations

import hashlib
from dataclasses import replace

import pytest

from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneCompositionRejectedV1,
    AssetLaneCoordinatorContextV1,
    AssetLaneCoordinatorRejectCodeV1,
    AssetLaneModuleCompatibilityV1,
    AssetLanePrivatePortV1,
    AssetLaneStateProjectionV1,
    project_asset_transfer_state_v1,
    project_managed_asset_lifecycle_state_v1,
)
from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferStateV1,
)
from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    canonical_global_bytes_v1,
)
from src.core.managed_asset_lifecycle_module_v1 import (
    transition_managed_asset_lifecycle_v1,
)
from src.core.managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
    ManagedAssetClassV1,
    ManagedAssetLifecycleAcceptedV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleStateV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _transfer_fixture() -> tuple[
    AssetTransferContextV1,
    AssetTransferStateV1,
    AssetTransferAcceptedV1,
]:
    context = AssetTransferContextV1(
        chain_id="zeno-asset-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        module_release_id=_root(3),
        command_occurrence_id=_root(4),
        subject_id="alice",
        grant_root=_root(5),
    )
    state = AssetTransferStateV1(
        module_release_id=_root(3),
        policies=(AssetTransferPolicyV1("USD", "treasury", 2, True),),
        balances=(
            EconomicAmountV1("alice", "USD", "accounts", 100),
            EconomicAmountV1("bob", "USD", "accounts", 10),
            EconomicAmountV1("treasury", "USD", "accounts", 5),
        ),
        supplies=(AssetSupplyV1("USD", 115),),
    )
    command = AssetTransferCommandV1(
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "USD",
        "alice",
        "bob",
        30,
        2,
    )
    result = transition_asset_transfer_v1(context, state, command)
    assert isinstance(result, AssetTransferAcceptedV1)
    return context, state, result


def _lifecycle_fixture() -> tuple[
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecycleStateV1,
    ManagedAssetLifecycleAcceptedV1,
]:
    context = ManagedAssetLifecycleContextV1(
        chain_id="zeno-asset-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        module_release_id=_root(6),
        command_occurrence_id=_root(7),
        subject_id="issuer",
        grant_root=_root(8),
    )
    state = ManagedAssetLifecycleStateV1(
        module_release_id=_root(6),
        policies=(
            ManagedAssetLifecyclePolicyV1(
                asset="USD",
                asset_class=ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
                issue_authority_subject="issuer",
                issue_policy_root=_root(8),
                burn_policy_root=_root(9),
                enabled=True,
            ),
        ),
        balances=(EconomicAmountV1("alice", "USD", "accounts", 10),),
        supplies=(AssetSupplyV1("USD", 10),),
    )
    command = ManagedAssetLifecycleCommandV1(
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        "USD",
        "alice",
        7,
    )
    result = transition_managed_asset_lifecycle_v1(context, state, command)
    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)
    return context, state, result


def _coordinator_context(
    *,
    module_release_id: str = _root(3),
    module_schema: str = ASSET_TRANSFER_MODULE_SCHEMA_V1,
    occurrence_id: str = _root(4),
) -> AssetLaneCoordinatorContextV1:
    return AssetLaneCoordinatorContextV1(
        chain_id="zeno-asset-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        coordinator_release_id=_root(10),
        command_occurrence_id=occurrence_id,
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
        compatible_modules=(
            AssetLaneModuleCompatibilityV1(module_release_id, module_schema),
        ),
    )


def _transfer_port(
    state: AssetTransferStateV1,
    accepted: AssetTransferAcceptedV1,
    *,
    post_state: AssetLaneStateProjectionV1 | None = None,
    effects: GlobalEconomicEffectPlanV1 | None = None,
) -> AssetLanePrivatePortV1:
    selected_effects = accepted.effects if effects is None else effects
    return AssetLanePrivatePortV1(
        producer_module_schema=ASSET_TRANSFER_MODULE_SCHEMA_V1,
        module_release_id=state.module_release_id,
        command_occurrence_id=_root(4),
        pre_state=project_asset_transfer_state_v1(
            state,
            asset_policy_registry_root=_root(11),
            fee_policy_registry_root=_root(12),
        ),
        post_state=(
            project_asset_transfer_state_v1(
                accepted.post_state,
                asset_policy_registry_root=_root(11),
                fee_policy_registry_root=_root(12),
            )
            if post_state is None
            else post_state
        ),
        module_effect_plan_root=selected_effects.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
    )


def _bound_journal(
    accepted: AssetTransferAcceptedV1 | ManagedAssetLifecycleAcceptedV1,
    port: AssetLanePrivatePortV1,
    *,
    effects: GlobalEconomicEffectPlanV1 | None = None,
):
    selected_effects = accepted.effects if effects is None else effects
    return replace(
        accepted.module_journal,
        effect_plan_root=selected_effects.effect_plan_root,
        private_port_root=port.port_root,
        receipt_root=_root(30),
    )


def _assert_noop(
    result: object,
    pre_state: AssetLaneStateProjectionV1,
    code: AssetLaneCoordinatorRejectCodeV1,
) -> None:
    assert isinstance(result, AssetLaneCompositionRejectedV1)
    assert result.code is code
    assert result.pre_lane_root == pre_state.state_root
    assert result.post_lane_root == pre_state.state_root
    assert result.effects.is_empty


def test_module_specific_states_share_one_complete_lane_projection() -> None:
    _, transfer_state, _ = _transfer_fixture()
    lifecycle_state = ManagedAssetLifecycleStateV1(
        module_release_id=_root(6),
        policies=(
            ManagedAssetLifecyclePolicyV1(
                "USD",
                ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
                "issuer",
                _root(8),
                _root(9),
                True,
            ),
        ),
        balances=transfer_state.balances,
        supplies=transfer_state.supplies,
    )

    transfer_projection = project_asset_transfer_state_v1(
        transfer_state,
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
    )
    lifecycle_projection = project_managed_asset_lifecycle_state_v1(
        lifecycle_state,
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
    )

    assert transfer_projection == lifecycle_projection
    assert transfer_projection.state_root == lifecycle_projection.state_root


def test_current_zero_private_port_receipt_is_a_composition_noop() -> None:
    _, state, accepted = _transfer_fixture()
    port = _transfer_port(state, accepted)
    result = compose_asset_lane_single_v1(
        _coordinator_context(),
        accepted.module_journal,
        port,
        accepted.effects,
    )

    _assert_noop(
        result,
        port.pre_state,
        AssetLaneCoordinatorRejectCodeV1.PRIVATE_PORT_UNBOUND,
    )


def test_bound_transfer_port_normalizes_the_common_lane_write() -> None:
    _, state, accepted = _transfer_fixture()
    port = _transfer_port(state, accepted)
    result = compose_asset_lane_single_v1(
        _coordinator_context(),
        _bound_journal(accepted, port),
        port,
        accepted.effects,
    )

    assert isinstance(result, AssetLaneCompositionAcceptedV1)
    assert result.post_state == port.post_state
    assert result.effects.rows == accepted.effects.rows
    assert result.effects.lane_writes[0].lane_id is LaneIdV1.ASSET_TRANSFER
    assert result.effects.lane_writes[0].pre_root == port.pre_state.state_root
    assert result.effects.lane_writes[0].post_root == port.post_state.state_root
    assert result.lane_journal.pre_lane_root == port.pre_state.state_root
    assert result.lane_journal.post_lane_root == port.post_state.state_root
    assert result.lane_journal.effect_plan_root == result.effects.effect_plan_root


def test_bound_transfer_python_rust_canonical_vector_is_frozen() -> None:
    _, state, accepted = _transfer_fixture()
    port = _transfer_port(state, accepted)
    context = _coordinator_context()
    journal = _bound_journal(accepted, port)
    result = compose_asset_lane_single_v1(context, journal, port, accepted.effects)
    assert isinstance(result, AssetLaneCompositionAcceptedV1)

    assert tuple(
        hashlib.sha256(canonical_global_bytes_v1(value)).hexdigest()
        for value in (
            port.pre_state,
            port.post_state,
            port,
            context,
            journal,
            result.effects,
            result.lane_journal,
        )
    ) == (
        "e3d707bb1405aa0cdc1ce6873bc78c87c1b2527605c4c501655a09c5ae9adf2c",
        "be1346724e8ccd7d5e30dcc9feb4684ad4ac7640abc87d4e16a2bccb76d88d82",
        "bc41b6785d2d62544860f4d669c8ddaf7668df77c9b76a9cb7cc5ef34ad55120",
        "7a45cb769cc2dcd79593ba75fb059cef2bceeade7cceca8c3c90cb34ae8f3a21",
        "737322036412e7f7a4db7c4e4ba33ec61784a7186bcfef57be660734427d4af1",
        "3a57907a25d5b75e5fc15f86c15050011e22fdc7592b83b68d9d48f73667ca50",
        "2b1386422d0060876b2c0580db1676d45c73e2287395dba3ba63f905fa4e6251",
    )
    assert (
        port.pre_state.state_root,
        port.post_state.state_root,
        port.port_root,
        journal.journal_root,
        result.effects.effect_plan_root,
        result.lane_journal.journal_root,
    ) == (
        "0x9fe0b7f2c601e9628e368e60c494a0624393571c01389b87f1f0d3e827f9205f",
        "0xb67fa23250a7e61a5b181a55528413d2f992f7ce0b2ac141d92b0d785c4e8b80",
        "0x8bf6e49619c76a0c271d2b63cf5ca26cfb4b70114e9cfcaaf205aaf518984289",
        "0xfcf64b40761d25671159759b49f31314d8bc243a01cfffcb5509308bc88e0dc3",
        "0xd93b0a7c00f40c21bb12b9904ef6ce8d7609b441c4fe71d4c56c832259827ea3",
        "0xa4c9b98bfa0cd955b0fd74e34bb4b5c91508bc94e2fee229eacb5f3e4a13319d",
    )


def test_bound_issue_port_preserves_authorized_supply_change() -> None:
    _, state, accepted = _lifecycle_fixture()
    pre_state = project_managed_asset_lifecycle_state_v1(
        state,
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
    )
    post_state = project_managed_asset_lifecycle_state_v1(
        accepted.post_state,
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
    )
    port = AssetLanePrivatePortV1(
        MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
        _root(6),
        _root(7),
        pre_state,
        post_state,
        accepted.effects.effect_plan_root,
        ZERO_ROOT_V1,
    )
    result = compose_asset_lane_single_v1(
        _coordinator_context(
            module_release_id=_root(6),
            module_schema=MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
            occurrence_id=_root(7),
        ),
        _bound_journal(accepted, port),
        port,
        accepted.effects,
    )

    assert isinstance(result, AssetLaneCompositionAcceptedV1)
    assert result.post_state.supply_atoms("USD") == 17
    assert result.effects.asset_conservation[0].authorized_issue_atoms == 7


def test_projection_rejects_unnamed_supply_and_account_domain_aliases() -> None:
    with pytest.raises(ValueError, match="owned and custodied total must equal supply"):
        AssetLaneStateProjectionV1(
            _root(11),
            _root(12),
            (EconomicAmountV1("alice", "USD", "accounts", 9),),
            (),
            (AssetSupplyV1("USD", 10),),
        )
    with pytest.raises(ValueError, match="custody rows must not use accounts"):
        AssetLaneStateProjectionV1(
            _root(11),
            _root(12),
            (),
            (EconomicAmountV1("vault", "USD", "accounts", 10),),
            (AssetSupplyV1("USD", 10),),
        )
