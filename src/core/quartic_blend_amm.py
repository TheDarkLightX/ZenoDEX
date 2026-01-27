"""
Quartic-blend AMM (new curve family):

  K(x,y) = x*y*(x^2 + y^2 + c*x*y)

with c = c_num/c_den (rational, c>=0).

This wraps `src/kernels/python/quartic_blend_swap_v1.py` in the functional core API.
"""

from __future__ import annotations

from typing import Tuple

from ..kernels.python.quartic_blend_swap_v1 import swap_exact_in as _kernel_swap_exact_in_v1
from ..kernels.python.quartic_blend_swap_v1 import swap_exact_out as _kernel_swap_exact_out_v1
from ..state.balances import Amount


def swap_exact_in_quartic_blend(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_in: Amount,
    *,
    c_num: int = 8,
    c_den: int = 1,
    fee_bps: int = 0,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError(f"Reserves must be non-negative: ({reserve_in}, {reserve_out})")
    if amount_in <= 0:
        raise ValueError(f"amount_in must be positive: {amount_in}")
    if c_num < 0 or c_den <= 0:
        raise ValueError("c_num must be non-negative, c_den must be positive")
    if not (0 <= fee_bps <= 10000):
        raise ValueError("fee_bps must be in [0, 10000]")

    res = _kernel_swap_exact_in_v1(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        amount_in=int(amount_in),
        c_num=int(c_num),
        c_den=int(c_den),
        fee_bps=int(fee_bps),
    )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")
    return int(res.amount_out), (int(res.new_reserve_in), int(res.new_reserve_out))


def swap_exact_out_quartic_blend(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
    *,
    c_num: int = 8,
    c_den: int = 1,
    fee_bps: int = 0,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError(f"Reserves must be non-negative: ({reserve_in}, {reserve_out})")
    if amount_out <= 0:
        raise ValueError(f"amount_out must be positive: {amount_out}")
    if amount_out >= reserve_out:
        raise ValueError("cannot drain full reserve_out")
    if c_num < 0 or c_den <= 0:
        raise ValueError("c_num must be non-negative, c_den must be positive")
    if not (0 <= fee_bps <= 10000):
        raise ValueError("fee_bps must be in [0, 10000]")

    res = _kernel_swap_exact_out_v1(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        amount_out=int(amount_out),
        c_num=int(c_num),
        c_den=int(c_den),
        fee_bps=int(fee_bps),
    )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")
    return int(res.amount_in), (int(res.new_reserve_in), int(res.new_reserve_out))
