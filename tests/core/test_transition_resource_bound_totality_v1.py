from __future__ import annotations

from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectCodeV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
)
from src.core.global_settlement_types_v1 import (
    MAX_ASSET_BALANCE_ROWS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
)
from src.core.managed_asset_lifecycle_module_v1 import (
    transition_managed_asset_lifecycle_v1,
)
from src.core.managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    ManagedAssetClassV1,
    ManagedAssetLifecycleAcceptedV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleRejectCodeV1,
    ManagedAssetLifecycleRejectedV1,
    ManagedAssetLifecycleStateV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _asset_transfer_state(row_count: int) -> AssetTransferStateV1:
    return AssetTransferStateV1(
        module_release_id=_root(3),
        policies=(AssetTransferPolicyV1("USD", "acct-000000", 0, True),),
        balances=tuple(
            EconomicAmountV1(f"acct-{index:06d}", "USD", "accounts", 10)
            for index in range(row_count)
        ),
        supplies=(AssetSupplyV1("USD", 10 * row_count),),
    )


def _asset_transfer_context() -> AssetTransferContextV1:
    return AssetTransferContextV1(
        chain_id="resource-bound-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=1,
        module_release_id=_root(3),
        command_occurrence_id=_root(4),
        subject_id="acct-000001",
        grant_root=_root(5),
    )


def _asset_transfer_command() -> AssetTransferCommandV1:
    return AssetTransferCommandV1(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V1,
        asset="USD",
        sender="acct-000001",
        recipient="brand-new-owner",
        amount_atoms=1,
        max_fee_atoms=0,
    )


def _managed_asset_state(row_count: int) -> ManagedAssetLifecycleStateV1:
    return ManagedAssetLifecycleStateV1(
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
        balances=tuple(
            EconomicAmountV1(f"acct-{index:06d}", "USD", "accounts", 1)
            for index in range(row_count)
        ),
        supplies=(AssetSupplyV1("USD", row_count),),
    )


def _managed_asset_context() -> ManagedAssetLifecycleContextV1:
    return ManagedAssetLifecycleContextV1(
        chain_id="resource-bound-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=1,
        module_release_id=_root(3),
        command_occurrence_id=_root(4),
        subject_id="issuer",
        grant_root=_root(5),
    )


def _managed_asset_issue() -> ManagedAssetLifecycleCommandV1:
    return ManagedAssetLifecycleCommandV1(
        command_kind=MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        asset="USD",
        account_owner="brand-new-owner",
        amount_atoms=1,
    )


def test_asset_transfer_can_grow_to_exact_balance_row_ceiling() -> None:
    pre_state = _asset_transfer_state(MAX_ASSET_BALANCE_ROWS_V1 - 1)
    result = transition_asset_transfer_v1(
        _asset_transfer_context(), pre_state, _asset_transfer_command()
    )

    assert isinstance(result, AssetTransferAcceptedV1)
    assert len(result.post_state.balances) == MAX_ASSET_BALANCE_ROWS_V1


def test_asset_transfer_growth_past_ceiling_is_closed_typed_noop() -> None:
    pre_state = _asset_transfer_state(MAX_ASSET_BALANCE_ROWS_V1)
    result = transition_asset_transfer_v1(
        _asset_transfer_context(), pre_state, _asset_transfer_command()
    )

    assert isinstance(result, AssetTransferRejectedV1)
    assert result.code is AssetTransferRejectCodeV1.POST_STATE_RESOURCE_BOUND_EXCEEDED
    assert result.pre_state_root == pre_state.state_root
    assert result.post_state_root == pre_state.state_root
    assert result.effects.is_empty


def test_managed_asset_issue_can_grow_to_exact_balance_row_ceiling() -> None:
    pre_state = _managed_asset_state(MAX_ASSET_BALANCE_ROWS_V1 - 1)
    result = transition_managed_asset_lifecycle_v1(
        _managed_asset_context(), pre_state, _managed_asset_issue()
    )

    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)
    assert len(result.post_state.balances) == MAX_ASSET_BALANCE_ROWS_V1


def test_managed_asset_issue_growth_past_ceiling_is_closed_typed_noop() -> None:
    pre_state = _managed_asset_state(MAX_ASSET_BALANCE_ROWS_V1)
    result = transition_managed_asset_lifecycle_v1(
        _managed_asset_context(), pre_state, _managed_asset_issue()
    )

    assert isinstance(result, ManagedAssetLifecycleRejectedV1)
    assert (
        result.code
        is ManagedAssetLifecycleRejectCodeV1.POST_STATE_RESOURCE_BOUND_EXCEEDED
    )
    assert result.pre_state_root == pre_state.state_root
    assert result.post_state_root == pre_state.state_root
    assert result.effects.is_empty
