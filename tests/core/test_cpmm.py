# [TESTER] v1

from __future__ import annotations

from types import SimpleNamespace

import pytest

import src.core.cpmm as cpmm_mod
from src.core.cpmm import (
    MIN_LP_LOCK,
    compute_fee_total,
    compute_lp_burn,
    compute_lp_mint,
    swap_exact_in,
    swap_exact_out,
)
from src.core.domain_limits import DEX_POOL_RESERVE_MAX


def test_compute_lp_mint_uses_integer_isqrt() -> None:
    # Stay at the edge of the verified LP kernel domain and ensure exact-square
    # minting still behaves deterministically.
    n = 1_000_000_000
    lp = compute_lp_mint(reserve0=0, reserve1=0, amount0=n, amount1=n, lp_supply=0)
    assert lp == n - MIN_LP_LOCK


def test_compute_lp_mint_initial_liquidity_boundary_matches_min_lock() -> None:
    # Boundary: floor(sqrt(amount0*amount1)) == MIN_LP_LOCK must reject.
    try:
        compute_lp_mint(
            reserve0=0,
            reserve1=0,
            amount0=MIN_LP_LOCK,
            amount1=MIN_LP_LOCK,
            lp_supply=0,
        )
    except ValueError:
        pass
    else:
        assert False, "expected insufficient initial liquidity rejection at sqrt == MIN_LP_LOCK"

    # Just above boundary should mint at least 1 LP.
    lp = compute_lp_mint(
        reserve0=0,
        reserve1=0,
        amount0=MIN_LP_LOCK + 1,
        amount1=MIN_LP_LOCK + 1,
        lp_supply=0,
    )
    assert lp == 1


def test_swap_exact_out_updates_reserves_for_requested_amount_out() -> None:
    # There exist states where the minimal `amount_in` would yield *more* than the requested
    # `amount_out` under exact-in floor rounding. Exact-out semantics must still update reserves
    # for the requested `amount_out` (not the over-delivering quote).
    reserve_in = 1
    reserve_out = 4
    fee_bps = 0
    amount_out = 1

    amount_in, (new_reserve_in, new_reserve_out) = swap_exact_out(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
    )

    assert new_reserve_in == reserve_in + amount_in
    assert new_reserve_out == reserve_out - amount_out

    # Safety check: the paid input must be sufficient to output at least amount_out.
    amount_out_check, _ = swap_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )
    assert amount_out_check >= amount_out


def test_swap_exact_out_exposes_overdelivery_gap_for_monitoring() -> None:
    # Same witness as above: exact-out request is 1, but exact-in with the quoted input
    # would output more due to integer lattice effects.
    from src.kernels.python.cpmm_swap_v8 import swap_exact_out as swap_exact_out_v8

    r = swap_exact_out_v8(
        reserve_in=1,
        reserve_out=4,
        amount_out=1,
        fee_bps=0,
    )
    assert r.amount_out == 1
    assert r.amount_out_quote >= r.amount_out
    assert r.overdelivery_gap == r.amount_out_quote - r.amount_out
    assert r.overdelivery_gap > 0


def test_swap_exact_out_overdelivery_gap_absolute_guard() -> None:
    # Witness has overdelivery gap=1; abs guard=0 should reject.
    try:
        swap_exact_out(
            reserve_in=1,
            reserve_out=4,
            amount_out=1,
            fee_bps=0,
            max_overdelivery_gap_abs=0,
        )
    except ValueError as exc:
        assert "overdelivery gap exceeds absolute policy" in str(exc)
    else:
        assert False, "expected overdelivery absolute guard to reject witness"

    # Allowing gap=1 should pass for this witness.
    amount_in, _ = swap_exact_out(
        reserve_in=1,
        reserve_out=4,
        amount_out=1,
        fee_bps=0,
        max_overdelivery_gap_abs=1,
    )
    assert amount_in == 1


def test_swap_exact_out_overdelivery_gap_bps_guard() -> None:
    # Witness has amount_out=1 and gap=1 => 10_000 bps.
    try:
        swap_exact_out(
            reserve_in=1,
            reserve_out=4,
            amount_out=1,
            fee_bps=0,
            max_overdelivery_gap_bps=9_999,
        )
    except ValueError as exc:
        assert "overdelivery gap exceeds bps policy" in str(exc)
    else:
        assert False, "expected overdelivery bps guard to reject witness"

    amount_in, _ = swap_exact_out(
        reserve_in=1,
        reserve_out=4,
        amount_out=1,
        fee_bps=0,
        max_overdelivery_gap_bps=10_000,
    )
    assert amount_in == 1
