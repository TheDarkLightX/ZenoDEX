"""
Cubic-sum AMM (new curve family): K(x,y) = x*y*(p*x + q*y).

Baseline (p=q=1):
  K(x,y) = x*y*(x+y)

This module provides consensus-critical exact-in and exact-out quoting/execution
with deterministic integer rounding.

Exact-in semantics (given reserves x,y and dx>0):
  Let K0 = K(x,y).
  Let x' = x + dx.
  Let y' be the *minimal* integer such that K(x', y') >= K0.
  Output dy = y - y' and post-state reserves are (x', y').

Exact-out semantics (given reserves x,y and desired dy with 0<dy<y):
  Return the *minimal* dx such that executing exact-in with dx yields output >= dy.

  Post-state reserves are the exact-out execution state:
    (x + dx, y - dy)

  Note: due to integer rounding, executing exact-in with the quoted dx may output
  MORE than dy. This is the "overdelivery gap" phenomenon.
"""

from __future__ import annotations

from typing import Tuple

from ..state.balances import Amount
from ..kernels.python.cubic_sum_swap_v1 import swap_exact_in as _kernel_swap_exact_in_v1
from ..kernels.python.cubic_sum_swap_v1 import swap_exact_out as _kernel_swap_exact_out_v1


def swap_exact_in_cubic_sum(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_in: Amount,
    *,
    p: int = 1,
    q: int = 1,
    fee_bps: int = 0,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """
    Exact-in swap under the cubic-sum invariant K(x,y)=x*y*(p*x + q*y).

    Determinism + minimality:
    - Uses integer-only rounding.
    - Guarantees the returned post-swap reserve_out y' is the *minimal* integer
      satisfying K(x+dx, y') >= K(x,y) (monotone invariant, no K decrease).
    """
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError(f"Reserves must be non-negative: ({reserve_in}, {reserve_out})")
    if amount_in <= 0:
        raise ValueError(f"amount_in must be positive: {amount_in}")
    if p <= 0 or q <= 0:
        raise ValueError("p and q must be positive")
    if not (0 <= fee_bps <= 10000):
        raise ValueError("fee_bps must be in [0, 10000]")

    res = _kernel_swap_exact_in_v1(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        amount_in=int(amount_in),
        p=int(p),
        q=int(q),
        fee_bps=int(fee_bps),
    )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")
    return int(res.amount_out), (int(res.new_reserve_in), int(res.new_reserve_out))


def swap_exact_out_cubic_sum(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
    *,
    p: int = 1,
    q: int = 1,
    fee_bps: int = 0,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """
    Exact-out quote + post-state.

    Returns the *minimal* amount_in such that executing exact-in with amount_in yields
    output >= amount_out. The returned post-state is (x+amount_in, y-amount_out).
    """
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError(f"Reserves must be non-negative: ({reserve_in}, {reserve_out})")
    if amount_out <= 0:
        raise ValueError(f"amount_out must be positive: {amount_out}")
    if amount_out >= reserve_out:
        raise ValueError("cannot drain full reserve_out")
    if p <= 0 or q <= 0:
        raise ValueError("p and q must be positive")
    if not (0 <= fee_bps <= 10000):
        raise ValueError("fee_bps must be in [0, 10000]")

    res = _kernel_swap_exact_out_v1(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        amount_out=int(amount_out),
        p=int(p),
        q=int(q),
        fee_bps=int(fee_bps),
    )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")
    return int(res.amount_in), (int(res.new_reserve_in), int(res.new_reserve_out))
