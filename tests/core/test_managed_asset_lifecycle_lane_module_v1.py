from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1,
)
from src.core.global_settlement_types_v1 import ZERO_ROOT_V1, AssetSupplyV1, EconomicAmountV1
from src.core.managed_asset_lifecycle_lane_module_v1 import (
    ManagedAssetLifecycleLaneModuleAcceptedV1,
    ManagedAssetLifecycleLaneModuleInputV1,
    transition_managed_asset_lifecycle_lane_module_v1,
)
from src.core.managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
    ManagedAssetClassV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleRejectCodeV1,
    ManagedAssetLifecycleRejectedV1,
    ManagedAssetLifecycleStateV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _input(
    command_kind: str,
    *,
    other_location_atoms: int = 0,
) -> ManagedAssetLifecycleLaneModuleInputV1:
    is_issue = command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1
    context = ManagedAssetLifecycleContextV1(
        chain_id="zeno-asset-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        module_release_id=_root(3),
        command_occurrence_id=_root(4),
        subject_id="issuer" if is_issue else "alice",
        grant_root=_root(5 if is_issue else 6),
    )
    state = ManagedAssetLifecycleStateV1(
        module_release_id=_root(3),
        policies=(
            ManagedAssetLifecyclePolicyV1(
                asset="USD",
                asset_class=ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
                issue_authority_subject="issuer",
                issue_policy_root=_root(5),
                burn_policy_root=_root(6),
                enabled=True,
            ),
        ),
        balances=(EconomicAmountV1("alice", "USD", "accounts", 10),),
        supplies=(AssetSupplyV1("USD", 10 + other_location_atoms),),
    )
    command = ManagedAssetLifecycleCommandV1(
        command_kind=command_kind,
        asset="USD",
        account_owner="alice",
        amount_atoms=7 if is_issue else 4,
    )
    return ManagedAssetLifecycleLaneModuleInputV1(
        context=context,
        pre_state=state,
        command=command,
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
        custody=(
            (
                EconomicAmountV1(
                    "escrow",
                    "USD",
                    "strategy_escrow",
                    other_location_atoms,
                ),
            )
            if other_location_atoms
            else ()
        ),
    )


def _coordinator_context() -> AssetLaneCoordinatorContextV1:
    return AssetLaneCoordinatorContextV1(
        chain_id="zeno-asset-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        coordinator_release_id=_root(10),
        command_occurrence_id=_root(4),
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
        compatible_modules=(
            AssetLaneModuleCompatibilityV1(
                _root(3),
                MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
            ),
        ),
    )


@pytest.mark.parametrize(
    "command_kind",
    (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, MANAGED_ASSET_BURN_COMMAND_KIND_V1),
)
def test_issue_and_burn_outputs_own_ports_and_compose_without_fixture_rebinding(
    command_kind: str,
) -> None:
    module_input = _input(command_kind)

    result = transition_managed_asset_lifecycle_lane_module_v1(module_input)

    assert isinstance(result, ManagedAssetLifecycleLaneModuleAcceptedV1)
    assert result.module_journal.private_port_root == result.private_port.port_root
    assert result.module_journal.private_port_root != ZERO_ROOT_V1
    assert result.private_port.module_effect_plan_root == result.effects.effect_plan_root
    assert result.private_port.pre_state.balances == module_input.pre_state.balances
    assert result.private_port.post_state.balances == result.post_state.balances
    assert result.private_port.post_state.supplies == result.post_state.supplies
    composed = compose_asset_lane_single_v1(
        _coordinator_context(),
        result.module_journal,
        result.private_port,
        result.effects,
    )
    assert isinstance(composed, AssetLaneCompositionAcceptedV1)
    assert composed.post_state == result.private_port.post_state


def test_issue_with_other_accounting_location_composes_complete_conservation() -> None:
    # Arrange
    module_input = _input(
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        other_location_atoms=5,
    )

    # Act
    result = transition_managed_asset_lifecycle_lane_module_v1(module_input)

    # Assert
    assert isinstance(result, ManagedAssetLifecycleLaneModuleAcceptedV1)
    conservation = result.effects.asset_conservation[0]
    assert conservation.owned_and_custodied_pre_atoms == 15
    assert conservation.owned_and_custodied_post_atoms == 22
    composed = compose_asset_lane_single_v1(
        _coordinator_context(),
        result.module_journal,
        result.private_port,
        result.effects,
    )
    assert isinstance(composed, AssetLaneCompositionAcceptedV1)


def test_zero_issue_rejects_without_port_effects_or_state_change() -> None:
    module_input = _input(MANAGED_ASSET_ISSUE_COMMAND_KIND_V1)
    module_input = ManagedAssetLifecycleLaneModuleInputV1(
        context=module_input.context,
        pre_state=module_input.pre_state,
        command=ManagedAssetLifecycleCommandV1(
            command_kind=MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
            asset="USD",
            account_owner="alice",
            amount_atoms=0,
        ),
        asset_policy_registry_root=module_input.asset_policy_registry_root,
        fee_policy_registry_root=module_input.fee_policy_registry_root,
        custody=module_input.custody,
    )

    result = transition_managed_asset_lifecycle_lane_module_v1(module_input)

    assert isinstance(result, ManagedAssetLifecycleRejectedV1)
    assert result.code is ManagedAssetLifecycleRejectCodeV1.ZERO_AMOUNT
    assert result.pre_state_root == module_input.pre_state.state_root
    assert result.post_state_root == module_input.pre_state.state_root
    assert result.effects.is_empty


@pytest.mark.parametrize(
    ("command_kind", "expected"),
    (
        (
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
            {
                "statement_root": "0xed74cca83c0741c453e63bc08e78b3a86154ad149663bb08cb00e1e85dd3b480",
                "pre_projection_root": "0x66381e30c5c4d8edf53f39a1bf5e163cdfc9fd5054b96ce7259da4a2a36de3fe",
                "post_projection_root": "0x02c6aa0f8e3a1d5657c83b5841ea58b7b921b4db6856d6c5079de628f61f287c",
                "private_port_root": "0x755516a651edbe44851ab1123a59622f6a3742154a9522b3e4be3a15cef4d6d3",
                "receipt_root": "0x1e3e9fd97bf8133ee48d8f1b5e3a715820f0dc936e7250b91b18060c37985602",
                "module_journal_root": "0x0e616a7f30f6270fe549109acdccc81a97fbcfab60b9176b8874b563929d2ae3",
            },
        ),
        (
            MANAGED_ASSET_BURN_COMMAND_KIND_V1,
            {
                "statement_root": "0x92d8f7897877bedb7e24d5e5df09fbca6d28e7db2447e31a615f39b711e41072",
                "pre_projection_root": "0x66381e30c5c4d8edf53f39a1bf5e163cdfc9fd5054b96ce7259da4a2a36de3fe",
                "post_projection_root": "0x7290cb1923b417e0b9a9f8b8c05489e6f8928a2fe5753a6d1af924951441a3f5",
                "private_port_root": "0x734d22c6e56a8860fb564184163dbab501b6d533434f5050eb683b03acc01ebf",
                "receipt_root": "0xc6222f0a74796f6fc1006d3638844c38cdb6885cbd85f705cf53a53835feda9b",
                "module_journal_root": "0xa3ae2a5d391489ed88fbc2327a38b43f5aa5712f7948fc789cee1e5bc80bf123",
            },
        ),
    ),
)
def test_python_rust_issue_and_burn_bound_output_roots_match(
    command_kind: str,
    expected: dict[str, str],
) -> None:
    module_input = _input(command_kind)
    changed_policy = replace(module_input, fee_policy_registry_root=_root(13))

    result = transition_managed_asset_lifecycle_lane_module_v1(module_input)

    assert isinstance(result, ManagedAssetLifecycleLaneModuleAcceptedV1)
    assert module_input.statement_root != changed_policy.statement_root
    assert {
        "statement_root": module_input.statement_root,
        "pre_projection_root": result.private_port.pre_state.state_root,
        "post_projection_root": result.private_port.post_state.state_root,
        "private_port_root": result.private_port.port_root,
        "receipt_root": result.receipt_root,
        "module_journal_root": result.module_journal.journal_root,
    } == expected
