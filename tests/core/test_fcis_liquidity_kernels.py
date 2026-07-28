from __future__ import annotations

import pytest

from src.core.fcis_liquidity_kernels import (
    AddLiquidityKernelInputV1,
    RemoveLiquidityKernelInputV1,
    add_liquidity_for_committed_pool_v1,
    remove_liquidity_for_committed_pool_v1,
)
from src.core.liquidity import add_liquidity, remove_liquidity
from src.state.pools import (
    CURVE_TAG_CPMM,
    PoolState,
    PoolStatus,
    compute_pool_id,
    normalize_curve_config,
)
from src.state.state_snapshots import snapshot_pool

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _pool(*, status: PoolStatus = PoolStatus.ACTIVE) -> PoolState:
    tag, params = normalize_curve_config(curve_tag=CURVE_TAG_CPMM, curve_params=None)
    return PoolState(
        pool_id=compute_pool_id(
            ASSET0,
            ASSET1,
            30,
            curve_tag=tag,
            curve_params=params,
        ),
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=2_000_000,
        reserve1=3_000_000,
        fee_bps=30,
        lp_supply=2_400_000,
        status=status,
        created_at=7,
        curve_tag=tag,
        curve_params=params,
    )


@pytest.mark.parametrize(
    "inputs",
    (
        AddLiquidityKernelInputV1(20_000, 40_000, 0, 0),
        AddLiquidityKernelInputV1(40_000, 20_000, 0, 0),
        AddLiquidityKernelInputV1(2, 3, 0, 0),
    ),
)
def test_exact_add_liquidity_matches_legacy(
    inputs: AddLiquidityKernelInputV1,
) -> None:
    legacy = _pool()
    assert add_liquidity_for_committed_pool_v1(
        snapshot_pool(legacy),
        inputs,
    ) == add_liquidity(
        legacy,
        inputs.amount0_desired,
        inputs.amount1_desired,
        inputs.amount0_min,
        inputs.amount1_min,
    )


@pytest.mark.parametrize(
    "inputs",
    (
        RemoveLiquidityKernelInputV1(1, 0, 0),
        RemoveLiquidityKernelInputV1(1_000, 0, 0),
        RemoveLiquidityKernelInputV1(2_400_000, 0, 0),
    ),
)
def test_exact_remove_liquidity_matches_legacy(
    inputs: RemoveLiquidityKernelInputV1,
) -> None:
    legacy = _pool()
    assert remove_liquidity_for_committed_pool_v1(
        snapshot_pool(legacy),
        inputs,
    ) == remove_liquidity(
        legacy,
        inputs.lp_amount,
        inputs.amount0_min,
        inputs.amount1_min,
    )


@pytest.mark.parametrize("status", (PoolStatus.FROZEN, PoolStatus.DISABLED))
def test_exact_liquidity_preserves_inactive_status_error(status: PoolStatus) -> None:
    legacy = _pool(status=status)
    exact = snapshot_pool(legacy)
    add_inputs = AddLiquidityKernelInputV1(20_000, 40_000, 0, 0)
    remove_inputs = RemoveLiquidityKernelInputV1(1_000, 0, 0)

    with pytest.raises(ValueError) as legacy_add:
        add_liquidity(
            legacy,
            add_inputs.amount0_desired,
            add_inputs.amount1_desired,
            add_inputs.amount0_min,
            add_inputs.amount1_min,
        )
    with pytest.raises(ValueError) as exact_add:
        add_liquidity_for_committed_pool_v1(exact, add_inputs)
    with pytest.raises(ValueError) as legacy_remove:
        remove_liquidity(
            legacy,
            remove_inputs.lp_amount,
            remove_inputs.amount0_min,
            remove_inputs.amount1_min,
        )
    with pytest.raises(ValueError) as exact_remove:
        remove_liquidity_for_committed_pool_v1(exact, remove_inputs)

    assert str(exact_add.value) == str(legacy_add.value)
    assert str(exact_remove.value) == str(legacy_remove.value)


def test_exact_add_rejects_minimum_above_ratio_result() -> None:
    exact = snapshot_pool(_pool())
    with pytest.raises(ValueError, match="amount1_used"):
        add_liquidity_for_committed_pool_v1(
            exact,
            AddLiquidityKernelInputV1(20_000, 40_000, 0, 30_001),
        )


def test_exact_remove_rejects_burn_above_supply() -> None:
    exact = snapshot_pool(_pool())
    with pytest.raises(ValueError, match="Cannot burn more LP than supply"):
        remove_liquidity_for_committed_pool_v1(
            exact,
            RemoveLiquidityKernelInputV1(exact.lp_supply + 1, 0, 0),
        )


def test_exact_liquidity_revalidates_hostile_nested_pool_mutation() -> None:
    exact = snapshot_pool(_pool())
    object.__setattr__(exact, "reserve0", 3_000_000_001)
    with pytest.raises((TypeError, ValueError)):
        add_liquidity_for_committed_pool_v1(
            exact,
            AddLiquidityKernelInputV1(20_000, 40_000, 0, 0),
        )


@pytest.mark.parametrize(
    "factory",
    (
        lambda: AddLiquidityKernelInputV1(True, 1, 0, 0),
        lambda: AddLiquidityKernelInputV1(1, 1, -1, 0),
        lambda: RemoveLiquidityKernelInputV1(True, 0, 0),
        lambda: RemoveLiquidityKernelInputV1(1, -1, 0),
    ),
)
def test_exact_liquidity_inputs_reject_bool_and_negative_values(factory: object) -> None:
    assert callable(factory)
    with pytest.raises((TypeError, ValueError)):
        factory()
