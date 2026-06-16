from __future__ import annotations

import pytest

from src.core.liquidity import create_pool
from src.state.pools import PoolState, PoolStatus, compute_pool_id


def _hex_asset(byte: str, *, upper: bool = False) -> str:
    body = byte * 32
    asset = "0x" + body
    return asset.upper().replace("X", "x") if upper else asset.lower()


def test_create_pool_stores_same_asset_text_that_pool_id_hashes() -> None:
    upper_a = _hex_asset("0A", upper=True)
    upper_b = _hex_asset("0B", upper=True)
    lower_a = upper_a.lower()
    lower_b = upper_b.lower()

    upper_pool_id, upper_pool, _ = create_pool(upper_a, upper_b, 2_000, 2_000, 30, "creator")
    lower_pool_id, lower_pool, _ = create_pool(lower_a, lower_b, 2_000, 2_000, 30, "creator")

    assert upper_pool_id == lower_pool_id
    assert (upper_pool.asset0, upper_pool.asset1) == (lower_a, lower_b)
    assert (upper_pool.asset0, upper_pool.asset1) == (lower_pool.asset0, lower_pool.asset1)


def test_pool_state_canonicalizes_hex_assets_before_state_root_observes_them() -> None:
    upper_a = _hex_asset("0A", upper=True)
    upper_b = _hex_asset("0B", upper=True)

    pool = PoolState(
        pool_id=compute_pool_id(upper_a, upper_b, 30),
        asset0=upper_a,
        asset1=upper_b,
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=30,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    assert pool.asset0 == upper_a.lower()
    assert pool.asset1 == upper_b.lower()


def test_create_pool_rejects_hex_assets_out_of_canonical_order_after_normalization() -> None:
    raw_asset0 = _hex_asset("0B", upper=True)
    raw_asset1 = _hex_asset("0a")

    with pytest.raises(ValueError, match="Assets must be in canonical order"):
        create_pool(raw_asset0, raw_asset1, 2_000, 2_000, 30, "creator")
