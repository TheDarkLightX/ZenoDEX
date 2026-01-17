# [TESTER] v1

from __future__ import annotations

from src.core.cpmm import MIN_LP_LOCK, compute_lp_mint
from src.core.cpmm import swap_exact_in, swap_exact_out


def test_compute_lp_mint_uses_integer_isqrt() -> None:
    # Pick values where float sqrt would be wrong due to precision loss.
    n = (1 << 70) + 12345
    lp = compute_lp_mint(reserve0=0, reserve1=0, amount0=n, amount1=n, lp_supply=0)
    assert lp == n - MIN_LP_LOCK


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
