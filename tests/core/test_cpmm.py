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
    swap_exact_in_with_protocol_fee,
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


def test_compute_lp_mint_rejects_campaign3_one_unit_first_mint_attack() -> None:
    with pytest.raises(ValueError, match="insufficient initial liquidity"):
        compute_lp_mint(
            reserve0=0,
            reserve1=0,
            amount0=1,
            amount1=1,
            lp_supply=0,
        )


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


def test_compute_fee_total_enforces_domains() -> None:
    assert compute_fee_total(1, 0) == 0
    assert compute_fee_total(10_000, 10_000) == 10_000

    with pytest.raises(ValueError):
        compute_fee_total(-1, 0)

    with pytest.raises(ValueError):
        compute_fee_total(1, 10_001)


def test_swap_exact_in_rejects_reserve_overflow() -> None:
    with pytest.raises(ValueError, match="reserve_in domain max"):
        swap_exact_in(
            reserve_in=DEX_POOL_RESERVE_MAX,
            reserve_out=1,
            amount_in=1,
            fee_bps=0,
        )


def test_swap_exact_in_rejects_kernel_invariant_violation(monkeypatch: pytest.MonkeyPatch) -> None:
    def fake_swap_exact_in_v8(**_: int) -> SimpleNamespace:
        return SimpleNamespace(
            amount_out=1,
            new_reserve_in=2,
            new_reserve_out=1,
            k_before=10,
            k_after=9,
        )

    monkeypatch.setattr(cpmm_mod, "_kernel_swap_exact_in_v8", fake_swap_exact_in_v8)

    with pytest.raises(ValueError, match="Invariant violation"):
        swap_exact_in(
            reserve_in=1,
            reserve_out=2,
            amount_in=1,
            fee_bps=0,
        )


def test_swap_exact_in_with_protocol_fee_exposes_fee_split_and_reserve_capture() -> None:
    reserve_in = 1_000_000
    reserve_out = 1_000_000
    amount_in = 10_000
    fee_bps = 100
    protocol_share_bps = 5_000

    res = swap_exact_in_with_protocol_fee(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_share_bps,
    )
    zero_share_out, (zero_share_rin, zero_share_rout) = swap_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )

    assert res.fee_total == 100
    assert res.protocol_fee == 50
    assert res.lp_fee == 50
    assert res.net_in == amount_in - res.fee_total
    assert res.new_reserve_in == reserve_in + amount_in - res.protocol_fee
    assert res.new_reserve_out == reserve_out - res.amount_out
    assert res.amount_out == zero_share_out
    assert res.new_reserve_in == zero_share_rin - res.protocol_fee
    assert res.new_reserve_out == zero_share_rout
    assert res.k_after >= res.k_before


def test_swap_exact_in_with_protocol_fee_floor_boundary_keeps_dust_in_lp_fee() -> None:
    dust_res = swap_exact_in_with_protocol_fee(
        reserve_in=10_000,
        reserve_out=10_000,
        amount_in=1_000,
        fee_bps=1,
        protocol_fee_share_bps=9_999,
    )
    full_share_res = swap_exact_in_with_protocol_fee(
        reserve_in=10_000,
        reserve_out=10_000,
        amount_in=1_000,
        fee_bps=1,
        protocol_fee_share_bps=10_000,
    )

    assert dust_res.fee_total == 1
    assert dust_res.protocol_fee == 0
    assert dust_res.lp_fee == 1
    assert full_share_res.protocol_fee == 1
    assert full_share_res.lp_fee == 0
    assert full_share_res.new_reserve_in == dust_res.new_reserve_in - 1


def test_swap_exact_in_with_protocol_fee_rejects_bad_share_domain() -> None:
    with pytest.raises(ValueError):
        swap_exact_in_with_protocol_fee(
            reserve_in=1_000,
            reserve_out=1_000,
            amount_in=100,
            fee_bps=30,
            protocol_fee_share_bps=10_001,
        )

    with pytest.raises(TypeError):
        swap_exact_in_with_protocol_fee(
            reserve_in=1_000,
            reserve_out=1_000,
            amount_in=100,
            fee_bps=30,
            protocol_fee_share_bps=True,
        )


def test_swap_exact_out_rejects_full_reserve_drain() -> None:
    with pytest.raises(ValueError, match="Cannot drain full reserve"):
        swap_exact_out(
            reserve_in=10,
            reserve_out=10,
            amount_out=10,
            fee_bps=0,
        )


def test_swap_exact_out_rejects_kernel_invariant_violation(monkeypatch: pytest.MonkeyPatch) -> None:
    def fake_swap_exact_out_v8(**_: int) -> SimpleNamespace:
        return SimpleNamespace(
            amount_in=1,
            new_reserve_in=2,
            new_reserve_out=1,
            amount_out_quote=1,
            amount_out=1,
            overdelivery_gap=0,
            k_before=10,
            k_after=9,
        )

    monkeypatch.setattr(cpmm_mod, "_kernel_swap_exact_out_v8", fake_swap_exact_out_v8)

    with pytest.raises(ValueError, match="Invariant violation"):
        swap_exact_out(
            reserve_in=1,
            reserve_out=2,
            amount_out=1,
            fee_bps=0,
        )


def test_compute_lp_mint_rejects_add_to_empty_pool() -> None:
    with pytest.raises(ValueError, match="empty pool"):
        compute_lp_mint(
            reserve0=0,
            reserve1=10,
            amount0=1,
            amount1=1,
            lp_supply=1,
        )


def test_compute_lp_mint_rejects_reserve_domain_overflow() -> None:
    with pytest.raises(ValueError, match="reserve0 domain max"):
        compute_lp_mint(
            reserve0=DEX_POOL_RESERVE_MAX,
            reserve1=10,
            amount0=1,
            amount1=1,
            lp_supply=1,
        )

    with pytest.raises(ValueError, match="reserve1 domain max"):
        compute_lp_mint(
            reserve0=10,
            reserve1=DEX_POOL_RESERVE_MAX,
            amount0=1,
            amount1=1,
            lp_supply=1,
        )


def test_compute_lp_mint_subsequent_deposit_uses_minimum_side() -> None:
    lp = compute_lp_mint(
        reserve0=100,
        reserve1=200,
        amount0=10,
        amount1=40,
        lp_supply=1000,
    )
    assert lp == 100


def test_compute_lp_mint_rejects_zero_result() -> None:
    with pytest.raises(ValueError, match="non-positive"):
        compute_lp_mint(
            reserve0=1000,
            reserve1=1000,
            amount0=1,
            amount1=1,
            lp_supply=1,
        )


def test_compute_lp_mint_rejects_campaign3_donation_zero_share_witness() -> None:
    # Campaign 3 witness shape:
    # total LP supply is 1 while reserves have been inflated to 1_000_001.
    # A 1_000_000 deposit would floor to 0 LP shares, so the runtime must
    # reject before any balance or reserve delta can be accepted.
    with pytest.raises(ValueError, match="non-positive"):
        compute_lp_mint(
            reserve0=1_000_001,
            reserve1=1_000_001,
            amount0=1_000_000,
            amount1=1_000_000,
            lp_supply=1,
        )


def test_compute_lp_burn_rejects_lp_amount_above_supply() -> None:
    with pytest.raises(ValueError, match="Cannot burn more LP than supply"):
        compute_lp_burn(
            lp_amount=11,
            reserve0=100,
            reserve1=200,
            lp_supply=10,
        )


def test_compute_lp_burn_returns_proportional_amounts() -> None:
    amount0_out, amount1_out = compute_lp_burn(
        lp_amount=25,
        reserve0=400,
        reserve1=1000,
        lp_supply=100,
    )
    assert amount0_out == 100
    assert amount1_out == 250
