from __future__ import annotations

import pytest

from src.core.amm_dispatch import (
    swap_exact_in_for_committed_pool_v1,
    swap_exact_in_for_pool,
    swap_exact_out_for_committed_pool_v1,
    swap_exact_out_for_pool,
)
from src.core.liquidity import (
    AddLiquidityKernelInputV1,
    RemoveLiquidityKernelInputV1,
    add_liquidity,
    add_liquidity_for_committed_pool_v1,
    remove_liquidity,
    remove_liquidity_for_committed_pool_v1,
)
from src.core.quote_receipts import (
    pool_state_fingerprint,
    pool_state_fingerprint_committed_v1,
)
from src.state.pools import (
    CURVE_TAG_CPMM,
    CURVE_TAG_CUBIC_SUM_V1,
    CURVE_TAG_QUARTIC_BLEND_V1,
    CURVE_TAG_QUINTIC_BLEND_V1,
    CURVE_TAG_SUM_BOOST_V1,
    PoolState,
    PoolStatus,
    compute_pool_id,
    normalize_curve_config,
)
from src.state.state_snapshots import snapshot_pool

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _pool(
    curve_tag: str,
    curve_params: object,
    *,
    status: PoolStatus = PoolStatus.ACTIVE,
) -> PoolState:
    normalized_tag, normalized_params = normalize_curve_config(
        curve_tag=curve_tag,
        curve_params=curve_params,
    )
    return PoolState(
        pool_id=compute_pool_id(
            ASSET0,
            ASSET1,
            30,
            curve_tag=normalized_tag,
            curve_params=normalized_params,
        ),
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=2_000_000,
        reserve1=3_000_000,
        fee_bps=30,
        lp_supply=2_400_000,
        status=status,
        created_at=7,
        curve_tag=normalized_tag,
        curve_params=normalized_params,
    )


CURVE_CASES = (
    (CURVE_TAG_CPMM, None),
    (CURVE_TAG_CUBIC_SUM_V1, {"p": 1, "q": 1}),
    (CURVE_TAG_SUM_BOOST_V1, {"mu_num": 200, "mu_den": 10_000}),
    (CURVE_TAG_QUARTIC_BLEND_V1, {"c_num": 1, "c_den": 10}),
    (CURVE_TAG_QUINTIC_BLEND_V1, {"c_num": 1, "c_den": 10}),
)


@pytest.mark.parametrize(("curve_tag", "curve_params"), CURVE_CASES)
def test_exact_pool_swap_dispatch_matches_legacy_for_every_registered_curve(
    curve_tag: str,
    curve_params: object,
) -> None:
    legacy = _pool(curve_tag, curve_params)
    committed = snapshot_pool(legacy)

    assert swap_exact_in_for_committed_pool_v1(
        committed,
        reserve_in=legacy.reserve0,
        reserve_out=legacy.reserve1,
        amount_in=1_000,
    ) == swap_exact_in_for_pool(
        legacy,
        reserve_in=legacy.reserve0,
        reserve_out=legacy.reserve1,
        amount_in=1_000,
    )
    assert swap_exact_out_for_committed_pool_v1(
        committed,
        reserve_in=legacy.reserve0,
        reserve_out=legacy.reserve1,
        amount_out=500,
    ) == swap_exact_out_for_pool(
        legacy,
        reserve_in=legacy.reserve0,
        reserve_out=legacy.reserve1,
        amount_out=500,
    )


def test_exact_pool_liquidity_kernels_match_legacy() -> None:
    legacy = _pool(CURVE_TAG_CPMM, None)
    committed = snapshot_pool(legacy)

    assert add_liquidity_for_committed_pool_v1(
        committed,
        AddLiquidityKernelInputV1(20_000, 40_000, 0, 0),
    ) == add_liquidity(legacy, 20_000, 40_000, 0, 0)
    assert remove_liquidity_for_committed_pool_v1(
        committed,
        RemoveLiquidityKernelInputV1(1_000, 0, 0),
    ) == remove_liquidity(legacy, 1_000, 0, 0)


@pytest.mark.parametrize("status", (PoolStatus.FROZEN, PoolStatus.DISABLED))
def test_exact_pool_liquidity_rejects_inactive_status_like_legacy(
    status: PoolStatus,
) -> None:
    legacy = _pool(CURVE_TAG_CPMM, None, status=status)
    committed = snapshot_pool(legacy)

    with pytest.raises(ValueError) as legacy_add_error:
        add_liquidity(legacy, 20_000, 40_000, 0, 0)
    with pytest.raises(ValueError) as exact_add_error:
        add_liquidity_for_committed_pool_v1(
            committed,
            AddLiquidityKernelInputV1(20_000, 40_000, 0, 0),
        )
    with pytest.raises(ValueError) as legacy_remove_error:
        remove_liquidity(legacy, 1_000, 0, 0)
    with pytest.raises(ValueError) as exact_remove_error:
        remove_liquidity_for_committed_pool_v1(
            committed,
            RemoveLiquidityKernelInputV1(1_000, 0, 0),
        )

    assert str(exact_add_error.value) == str(legacy_add_error.value)
    assert str(exact_remove_error.value) == str(legacy_remove_error.value)


@pytest.mark.parametrize("status", tuple(PoolStatus))
def test_exact_pool_fingerprint_matches_legacy_for_every_status(
    status: PoolStatus,
) -> None:
    legacy = _pool(CURVE_TAG_CPMM, None, status=status)

    assert pool_state_fingerprint_committed_v1(snapshot_pool(legacy)) == pool_state_fingerprint(
        legacy
    )


def test_exact_pool_wrappers_reject_legacy_objects() -> None:
    legacy = _pool(CURVE_TAG_CPMM, None)

    with pytest.raises(TypeError, match="exact committed pool"):
        swap_exact_in_for_committed_pool_v1(  # type: ignore[arg-type]
            legacy,
            reserve_in=legacy.reserve0,
            reserve_out=legacy.reserve1,
            amount_in=1_000,
        )
    with pytest.raises(TypeError, match="exact committed pool"):
        swap_exact_out_for_committed_pool_v1(  # type: ignore[arg-type]
            legacy,
            reserve_in=legacy.reserve0,
            reserve_out=legacy.reserve1,
            amount_out=500,
        )
    with pytest.raises(TypeError, match="exact committed pool"):
        add_liquidity_for_committed_pool_v1(  # type: ignore[arg-type]
            legacy,
            AddLiquidityKernelInputV1(20_000, 40_000, 0, 0),
        )
    with pytest.raises(TypeError, match="exact committed pool"):
        remove_liquidity_for_committed_pool_v1(  # type: ignore[arg-type]
            legacy,
            RemoveLiquidityKernelInputV1(1_000, 0, 0),
        )
    with pytest.raises(TypeError, match="exact committed pool"):
        pool_state_fingerprint_committed_v1(legacy)  # type: ignore[arg-type]
