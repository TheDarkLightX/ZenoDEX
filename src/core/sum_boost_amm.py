"""
Sum-boost AMM (new curve family): K = x*y*(x+y) * (1 + μ*(x+y)).

This wraps `src/kernels/python/sum_boost_swap_v1.py` in the functional core API.
"""

from __future__ import annotations

from typing import Tuple

from ..kernels.python.sum_boost_swap_v1 import swap_exact_in as _kernel_swap_exact_in_v1
from ..kernels.python.sum_boost_swap_v1 import swap_exact_out as _kernel_swap_exact_out_v1
from ..state.balances import Amount


def swap_exact_in_sum_boost(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_in: Amount,
    *,
    mu_num: int = 200,
    mu_den: int = 10_000,
    fee_bps: int = 0,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError(f"Reserves must be non-negative: ({reserve_in}, {reserve_out})")
    if amount_in <= 0:
        raise ValueError(f"amount_in must be positive: {amount_in}")
    if mu_num < 0 or mu_den <= 0:
        raise ValueError("mu_num must be non-negative, mu_den must be positive")
    if not (0 <= fee_bps <= 10000):
        raise ValueError("fee_bps must be in [0, 10000]")

    res = _kernel_swap_exact_in_v1(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        amount_in=int(amount_in),
        mu_num=int(mu_num),
        mu_den=int(mu_den),
        fee_bps=int(fee_bps),
    )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")
    return int(res.amount_out), (int(res.new_reserve_in), int(res.new_reserve_out))


def swap_exact_out_sum_boost(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
    *,
    mu_num: int = 200,
    mu_den: int = 10_000,
    fee_bps: int = 0,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError(f"Reserves must be non-negative: ({reserve_in}, {reserve_out})")
    if amount_out <= 0:
        raise ValueError(f"amount_out must be positive: {amount_out}")
    if amount_out >= reserve_out:
        raise ValueError("cannot drain full reserve_out")
    if mu_num < 0 or mu_den <= 0:
        raise ValueError("mu_num must be non-negative, mu_den must be positive")
    if not (0 <= fee_bps <= 10000):
        raise ValueError("fee_bps must be in [0, 10000]")

    res = _kernel_swap_exact_out_v1(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        amount_out=int(amount_out),
        mu_num=int(mu_num),
        mu_den=int(mu_den),
        fee_bps=int(fee_bps),
    )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")
    return int(res.amount_in), (int(res.new_reserve_in), int(res.new_reserve_out))

