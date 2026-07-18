from __future__ import annotations

import pytest

from src.core.cpmm import MIN_LP_LOCK
from src.core.liquidity import add_liquidity, create_pool, remove_liquidity
from src.state.pools import PoolState, PoolStatus, compute_pool_id


def _make_pool(
    *,
    reserve0: int = 100,
    reserve1: int = 200,
    fee_bps: int = 30,
    lp_supply: int = 1_000,
    status: PoolStatus = PoolStatus.ACTIVE,
) -> PoolState:
    return PoolState(
        pool_id="0xpool",
        asset0="A",
        asset1="B",
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=lp_supply,
        status=status,
        created_at=0,
    )


def test_create_pool_rejects_non_string_assets() -> None:
    with pytest.raises(TypeError, match="asset ids must be strings"):
        create_pool(
            asset0=1,  # type: ignore[arg-type]
            asset1="B",
            amount0=2_000,
            amount1=2_000,
            fee_bps=30,
            creator_pubkey="creator",
        )


def test_create_pool_rejects_noncanonical_asset_order() -> None:
    with pytest.raises(ValueError, match="canonical order"):
        create_pool(
            asset0="B",
            asset1="A",
            amount0=2_000,
            amount1=2_000,
            fee_bps=30,
            creator_pubkey="creator",
        )


def test_create_pool_normalizes_curve_configuration() -> None:
    pool_id, pool_state, lp_minted = create_pool(
        asset0="A",
        asset1="B",
        amount0=5_000,
        amount1=7_000,
        fee_bps=30,
        creator_pubkey="creator",
        curve_tag=" sum_boost_v1 ",
        curve_params={"mu_num": 200, "mu_den": 10_000},
    )

    assert pool_state.curve_tag == "SUM_BOOST_V1"
    assert pool_state.curve_params == '{"mu_den":10000,"mu_num":200}'
    assert pool_id == compute_pool_id(
        "A",
        "B",
        30,
        curve_tag="SUM_BOOST_V1",
        curve_params='{"mu_den":10000,"mu_num":200}',
    )
    assert lp_minted == pool_state.lp_supply - MIN_LP_LOCK


def test_add_liquidity_rejects_inactive_pool() -> None:
    with pytest.raises(ValueError, match="not active"):
        add_liquidity(
            _make_pool(status=PoolStatus.FROZEN),
            amount0_desired=10,
            amount1_desired=20,
            amount0_min=0,
            amount1_min=0,
        )


def test_add_liquidity_rejects_empty_pool() -> None:
    with pytest.raises(ValueError, match="empty pool"):
        add_liquidity(
            _make_pool(reserve0=0),
            amount0_desired=10,
            amount1_desired=20,
            amount0_min=0,
            amount1_min=0,
        )


def test_add_liquidity_rejects_orphaned_reserves_with_zero_supply() -> None:
    orphaned = _make_pool(
        reserve0=1_000_000,
        reserve1=1_000_000,
        lp_supply=0,
    )

    with pytest.raises(ValueError, match="nonempty pool with zero LP supply"):
        add_liquidity(
            orphaned,
            amount0_desired=1_000_000,
            amount1_desired=1_000_000,
            amount0_min=0,
            amount1_min=0,
        )

    assert orphaned.reserve0 == 1_000_000
    assert orphaned.reserve1 == 1_000_000
    assert orphaned.lp_supply == 0


def test_add_liquidity_enforces_minimums() -> None:
    pool = _make_pool()

    with pytest.raises(ValueError, match="amount0_used"):
        add_liquidity(
            pool,
            amount0_desired=100,
            amount1_desired=10,
            amount0_min=6,
            amount1_min=10,
        )

    with pytest.raises(ValueError, match="amount1_used"):
        add_liquidity(
            pool,
            amount0_desired=10,
            amount1_desired=100,
            amount0_min=10,
            amount1_min=21,
        )


def test_add_liquidity_returns_ratio_matched_amounts_and_lp() -> None:
    amount0_used, amount1_used, lp_minted = add_liquidity(
        _make_pool(),
        amount0_desired=10,
        amount1_desired=100,
        amount0_min=0,
        amount1_min=0,
    )

    assert (amount0_used, amount1_used, lp_minted) == (10, 20, 100)


def test_remove_liquidity_rejects_inactive_pool() -> None:
    with pytest.raises(ValueError, match="not active"):
        remove_liquidity(
            _make_pool(status=PoolStatus.DISABLED),
            lp_amount=10,
            amount0_min=0,
            amount1_min=0,
        )


def test_remove_liquidity_rejects_burn_above_supply() -> None:
    with pytest.raises(ValueError, match="Cannot burn more LP than supply"):
        remove_liquidity(
            _make_pool(lp_supply=10),
            lp_amount=11,
            amount0_min=0,
            amount1_min=0,
        )


def test_remove_liquidity_enforces_minimums() -> None:
    pool = _make_pool()

    with pytest.raises(ValueError, match="amount0_out"):
        remove_liquidity(
            pool,
            lp_amount=10,
            amount0_min=2,
            amount1_min=0,
        )

    with pytest.raises(ValueError, match="amount1_out"):
        remove_liquidity(
            pool,
            lp_amount=10,
            amount0_min=0,
            amount1_min=3,
        )


def test_remove_liquidity_returns_proportional_outputs() -> None:
    amount0_out, amount1_out = remove_liquidity(
        _make_pool(),
        lp_amount=25,
        amount0_min=0,
        amount1_min=0,
    )

    assert (amount0_out, amount1_out) == (2, 5)
