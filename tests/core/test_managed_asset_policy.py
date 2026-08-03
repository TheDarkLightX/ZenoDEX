from __future__ import annotations

import pytest

from src.core.managed_asset_policy import (
    ZUSD_MONETARY_AUTHORITY_V1,
    AssetOperationV1,
    ManagedAssetPolicyV1,
    ManagedAssetRejectCodeV1,
    build_zusd_managed_asset_policy,
    check_managed_asset_operation,
)

ZUSD_ASSET = "0x" + "ab" * 32
FOREIGN_ASSET = "0x" + "cd" * 32


def test_zusd_policy_allows_transfer() -> None:
    policy = build_zusd_managed_asset_policy(ZUSD_ASSET)

    assert (
        check_managed_asset_operation(
            policy=policy,
            asset_id=ZUSD_ASSET,
            operation=AssetOperationV1.TRANSFER,
        )
        is None
    )


@pytest.mark.parametrize(
    "operation",
    [
        AssetOperationV1.GENERIC_MINT,
        AssetOperationV1.GENERIC_BURN,
        AssetOperationV1.FAUCET_MINT,
    ],
)
def test_zusd_policy_requires_protocol_authority_for_supply_changes(
    operation: AssetOperationV1,
) -> None:
    policy = build_zusd_managed_asset_policy(ZUSD_ASSET)

    reject = check_managed_asset_operation(
        policy=policy,
        asset_id=ZUSD_ASSET,
        operation=operation,
    )

    assert reject is not None
    assert reject.code is ManagedAssetRejectCodeV1.PROTOCOL_AUTHORITY_REQUIRED
    assert reject.required_authority_id == ZUSD_MONETARY_AUTHORITY_V1
    assert reject.message() == (
        f"managed asset operation {operation.value} requires authority {ZUSD_MONETARY_AUTHORITY_V1}"
    )


def test_zusd_policy_does_not_claim_authority_over_foreign_asset() -> None:
    policy = build_zusd_managed_asset_policy(ZUSD_ASSET)

    assert (
        check_managed_asset_operation(
            policy=policy,
            asset_id=FOREIGN_ASSET,
            operation=AssetOperationV1.GENERIC_MINT,
        )
        is None
    )


def test_policy_rejects_duplicate_or_noncanonical_operation_order() -> None:
    with pytest.raises(ValueError, match="canonical order"):
        ManagedAssetPolicyV1(
            asset_id=ZUSD_ASSET,
            authority_id=ZUSD_MONETARY_AUTHORITY_V1,
            allowed_operations=(AssetOperationV1.TRANSFER, AssetOperationV1.TRANSFER),
        )

    with pytest.raises(ValueError, match="canonical order"):
        ManagedAssetPolicyV1(
            asset_id=ZUSD_ASSET,
            authority_id=ZUSD_MONETARY_AUTHORITY_V1,
            allowed_operations=(AssetOperationV1.GENERIC_BURN, AssetOperationV1.TRANSFER),
        )


def test_policy_rejects_noncanonical_asset_or_string_operation_alias() -> None:
    with pytest.raises(ValueError, match="canonical"):
        build_zusd_managed_asset_policy("AB" * 32)

    policy = build_zusd_managed_asset_policy(ZUSD_ASSET)
    with pytest.raises(TypeError, match="AssetOperationV1"):
        check_managed_asset_operation(
            policy=policy,
            asset_id=ZUSD_ASSET,
            operation="generic_mint",  # type: ignore[arg-type]
        )
