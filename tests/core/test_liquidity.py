from __future__ import annotations

import pytest

from src.core.cpmm import MIN_LP_LOCK
from src.core.liquidity import add_liquidity, create_pool, remove_liquidity
from src.state.pools import PoolStatus

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
CREATOR = "0x" + "11" * 48


def test_create_pool_returns_active_pool_and_locked_supply() -> None:
    pool_id, pool, lp_minted = create_pool(ASSET0, ASSET1, 4_000, 9_000, 30, CREATOR, created_at=12)

    assert pool.pool_id == pool_id
    assert pool.status is PoolStatus.ACTIVE
    assert lp_minted > 0
    assert pool.lp_supply == lp_minted + MIN_LP_LOCK
    assert pool.reserve0 == 4_000
    assert pool.reserve1 == 9_000


def test_create_pool_requires_canonical_asset_order() -> None:
    with pytest.raises(ValueError, match="canonical order"):
        create_pool(ASSET1, ASSET0, 4_000, 9_000, 30, CREATOR)


def test_add_and_remove_liquidity_use_pool_ratio_and_minimums() -> None:
    _pool_id, pool, lp_minted = create_pool(ASSET0, ASSET1, 4_000, 9_000, 30, CREATOR)

    amount0_used, amount1_used, newly_minted = add_liquidity(
        pool,
        amount0_desired=2_000,
        amount1_desired=10_000,
        amount0_min=1,
        amount1_min=1,
    )

    assert amount0_used > 0
    assert amount1_used > 0
    assert amount0_used * pool.reserve1 == amount1_used * pool.reserve0
    assert newly_minted > 0

    amount0_out, amount1_out = remove_liquidity(
        pool,
        lp_amount=max(1, lp_minted // 3),
        amount0_min=0,
        amount1_min=0,
    )

    assert amount0_out > 0
    assert amount1_out > 0


def test_add_liquidity_enforces_minimums() -> None:
    _pool_id, pool, _lp_minted = create_pool(ASSET0, ASSET1, 4_000, 9_000, 30, CREATOR)

    with pytest.raises(ValueError, match="amount1_used"):
        add_liquidity(
            pool,
            amount0_desired=2_000,
            amount1_desired=10_000,
            amount0_min=1,
            amount1_min=10_000,
        )
