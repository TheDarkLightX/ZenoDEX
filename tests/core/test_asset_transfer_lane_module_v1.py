from __future__ import annotations

from dataclasses import replace

from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1,
)
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    transition_asset_transfer_lane_module_v1,
)
from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectCodeV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
)
from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    AssetSupplyV1,
    EconomicAmountV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _input(*, amount_atoms: int = 30) -> AssetTransferLaneModuleInputV1:
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
        amount_atoms,
        2,
    )
    return AssetTransferLaneModuleInputV1(
        context=context,
        pre_state=state,
        command=command,
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
        custody=(),
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
                ASSET_TRANSFER_MODULE_SCHEMA_V1,
            ),
        ),
    )


def test_accepted_module_output_owns_the_bound_private_port() -> None:
    module_input = _input()

    result = transition_asset_transfer_lane_module_v1(module_input)

    assert isinstance(result, AssetTransferLaneModuleAcceptedV1)
    assert result.private_port.module_release_id == module_input.context.module_release_id
    assert result.private_port.command_occurrence_id == module_input.context.command_occurrence_id
    assert result.module_journal.private_port_root == result.private_port.port_root
    assert result.module_journal.private_port_root != ZERO_ROOT_V1
    assert result.module_journal.effect_plan_root == result.effects.effect_plan_root
    assert result.private_port.module_effect_plan_root == result.effects.effect_plan_root
    assert result.private_port.pre_state.balances == module_input.pre_state.balances
    assert result.private_port.post_state.balances == result.post_state.balances

    composed = compose_asset_lane_single_v1(
        _coordinator_context(),
        result.module_journal,
        result.private_port,
        result.effects,
    )
    assert isinstance(composed, AssetLaneCompositionAcceptedV1)
    assert composed.post_state == result.private_port.post_state
    assert (
        composed.lane_journal.journal_root
        == "0xc89ddaaad74124731a00a5530d481c8360ba85613d3e4f887774754f2967da95"
    )


def test_rejected_module_output_has_no_private_port_or_effects() -> None:
    module_input = _input(amount_atoms=0)

    result = transition_asset_transfer_lane_module_v1(module_input)

    assert isinstance(result, AssetTransferRejectedV1)
    assert result.code is AssetTransferRejectCodeV1.ZERO_AMOUNT
    assert result.pre_state_root == module_input.pre_state.state_root
    assert result.post_state_root == module_input.pre_state.state_root
    assert result.effects.is_empty


def test_statement_and_bound_output_roots_are_canonical_and_policy_bound() -> None:
    module_input = _input()
    changed_policy = replace(module_input, fee_policy_registry_root=_root(13))

    result = transition_asset_transfer_lane_module_v1(module_input)

    assert isinstance(result, AssetTransferLaneModuleAcceptedV1)
    assert module_input.statement_root != changed_policy.statement_root
    assert {
        "statement_root": module_input.statement_root,
        "pre_projection_root": result.private_port.pre_state.state_root,
        "post_projection_root": result.private_port.post_state.state_root,
        "private_port_root": result.private_port.port_root,
        "receipt_root": result.receipt_root,
        "module_journal_root": result.module_journal.journal_root,
    } == {
        "statement_root": "0x9c9426e4c8c3f2047417815f76a91588a754fe4e692af165dcabbc9be8c8ab32",
        "pre_projection_root": "0x9fe0b7f2c601e9628e368e60c494a0624393571c01389b87f1f0d3e827f9205f",
        "post_projection_root": "0xb67fa23250a7e61a5b181a55528413d2f992f7ce0b2ac141d92b0d785c4e8b80",
        "private_port_root": "0x8bf6e49619c76a0c271d2b63cf5ca26cfb4b70114e9cfcaaf205aaf518984289",
        "receipt_root": "0x3f9e60c18c0293971123a3da2b703ba3da574ba58704696519dc24d4a97121f7",
        "module_journal_root": "0x709acd06e9bf22c0f4791b9eb7d8c48a01cc07bc8b66ea8df52dd964a72c2af8",
    }
