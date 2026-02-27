from __future__ import annotations

from src.core.amm_dispatch import (
    CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
    swap_exact_out_for_pool,
)
from src.state.pools import PoolState, PoolStatus


def _cpmm_pool(pid: str, reserve0: int, reserve1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0="A",
        asset1="B",
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def test_cpmm_exact_out_dispatch_blocks_known_high_gap_witness() -> None:
    # Known overdelivery witness in raw CPMM exact-out arithmetic:
    # reserve_in=1, reserve_out=4, amount_out=1, fee=0 has gap_bps=10_000.
    pool = _cpmm_pool("p", reserve0=1, reserve1=4, fee_bps=0)
    try:
        _ = swap_exact_out_for_pool(pool, reserve_in=1, reserve_out=4, amount_out=1)
    except ValueError as exc:
        assert "overdelivery gap exceeds bps policy" in str(exc)
    else:
        assert False, "expected dispatch exact-out policy guard to reject known witness"


def test_cpmm_exact_out_dispatch_allows_standard_quotes() -> None:
    # Typical reserve regime should remain quotable under the default guard.
    pool = _cpmm_pool("p", reserve0=10_000, reserve1=10_000, fee_bps=30)
    amount_in, (new_r_in, new_r_out) = swap_exact_out_for_pool(
        pool,
        reserve_in=10_000,
        reserve_out=10_000,
        amount_out=250,
    )
    assert amount_in > 0
    assert new_r_in > 10_000
    assert new_r_out == 10_000 - 250
    assert CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT == 200
