"""
Power-Product CPMM (research curve): invariant K = x^m * y^n.

This is a generalization of:
- CPMM (fee=0): m=1, n=1
- Quadratic CPMM: m=2, n=1  (see `src/core/quadratic_cpmm.py`)

Why this exists (salvage of an earlier ideation pass):
- Weighted geometric-mean AMMs require fractional exponents / roots on-chain.
- A representation shift replaces fractional powers with *integer* powers + *integer* roots,
  enabling deterministic integer-only swap math for rational-weight-like curves.

This module is intentionally conservative:
- fee_bps is currently restricted to 0 (keeps invariant semantics crisp).
- exponents m,n are bounded to small integers to avoid pathological big-int costs.
- rounding is chosen to keep K' >= K (monotone non-decreasing invariant).
"""

from __future__ import annotations

import math
from typing import Tuple

from ..state.balances import Amount


MAX_EXPONENT = 16


def _ceil_div(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError("b must be positive")
    if a < 0:
        raise ValueError("a must be non-negative")
    return (a + b - 1) // b


def _ceil_iroot(n: int, k: int) -> int:
    """Smallest integer r such that r^k >= n (k>=1, n>=0)."""
    if n < 0:
        raise ValueError("n must be non-negative")
    if k <= 0:
        raise ValueError("k must be positive")
    if k == 1:
        return int(n)
    if n <= 1:
        return int(n)
    if k == 2:
        r = math.isqrt(n)
        return r if r * r == n else r + 1

    # Exponential search for an upper bound, then binary search.
    lo = 0
    hi = 1
    while pow(hi, k) < n:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if pow(mid, k) >= n:
            hi = mid
        else:
            lo = mid
    return hi


def power_product_k(x: Amount, y: Amount, *, exp_x: int, exp_y: int) -> int:
    if x < 0 or y < 0:
        raise ValueError("reserves must be non-negative")
    _validate_exponents(exp_x=exp_x, exp_y=exp_y)
    return pow(int(x), int(exp_x)) * pow(int(y), int(exp_y))


def _validate_exponents(*, exp_x: int, exp_y: int) -> None:
    for name, v in (("exp_x", exp_x), ("exp_y", exp_y)):
        if not isinstance(v, int) or isinstance(v, bool):
            raise TypeError(f"{name} must be an int")
        if v <= 0:
            raise ValueError(f"{name} must be positive")
        if v > MAX_EXPONENT:
            raise ValueError(f"{name} must be <= {MAX_EXPONENT}")


def swap_exact_in_power_product(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_in: Amount,
    *,
    exp_in: int = 1,
    exp_out: int = 1,
    fee_bps: int = 0,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """
    Exact-in swap under K = x^m * y^n.

    Conservative rounding:
      x' = x + dx
      need = ceil(K / x'^m)
      y' = ceil_root_n(need)
      out = y - y'

    Ensures:
      x'^m * y'^n >= K  => K' >= K (monotone invariant)
    """
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError("reserves must be non-negative")
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if fee_bps != 0:
        raise ValueError("power_product_cpmm: fee_bps must be 0 in this reference implementation")
    _validate_exponents(exp_x=exp_in, exp_y=exp_out)

    x = int(reserve_in)
    y = int(reserve_out)
    dx = int(amount_in)

    if x == 0 or y == 0:
        raise ValueError("power_product_cpmm: reserves must be positive")

    k0 = pow(x, exp_in) * pow(y, exp_out)
    x1 = x + dx
    denom = pow(x1, exp_in)
    need = _ceil_div(k0, denom)
    y1 = _ceil_iroot(need, exp_out)
    if y1 > y:
        raise ValueError("swap would require increasing reserve_out (invalid)")
    out = y - y1
    if out <= 0:
        raise ValueError("amount_out is non-positive")

    k1 = pow(x1, exp_in) * pow(y1, exp_out)
    if k1 < k0:
        raise ValueError("invariant violation: K decreased")

    return out, (x1, y1)


def swap_exact_out_power_product(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
    *,
    exp_in: int = 1,
    exp_out: int = 1,
    fee_bps: int = 0,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """
    Exact-out swap under K = x^m * y^n.

    For desired dy:
      y' = y - dy
      Need minimal x' such that x'^m * y'^n >= K
      => x' >= ceil_root_m( ceil(K / y'^n) )

    We then recompute using the exact-in rule to ensure consistent rounding,
    increasing dx until the delivered out >= dy.
    """
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError("reserves must be non-negative")
    if amount_out <= 0:
        raise ValueError("amount_out must be positive")
    if amount_out >= reserve_out:
        raise ValueError("cannot drain full reserve_out")
    if fee_bps != 0:
        raise ValueError("power_product_cpmm: fee_bps must be 0 in this reference implementation")
    _validate_exponents(exp_x=exp_in, exp_y=exp_out)

    x = int(reserve_in)
    y = int(reserve_out)
    dy = int(amount_out)
    if x == 0 or y == 0:
        raise ValueError("power_product_cpmm: reserves must be positive")

    y1 = y - dy
    if y1 <= 0:
        raise ValueError("cannot drain full reserve_out")

    k0 = pow(x, exp_in) * pow(y, exp_out)
    denom = pow(y1, exp_out)
    need = _ceil_div(k0, denom)
    x1 = _ceil_iroot(need, exp_in)
    if x1 < x:
        x1 = x
    dx = x1 - x
    if dx <= 0:
        dx = 1

    out_check, (x2, y2) = swap_exact_in_power_product(
        x,
        y,
        dx,
        exp_in=exp_in,
        exp_out=exp_out,
        fee_bps=0,
    )
    # Monotone in dx, so a linear bump is safe for small regimes (research posture).
    while out_check < dy:
        dx += 1
        out_check, (x2, y2) = swap_exact_in_power_product(
            x,
            y,
            dx,
            exp_in=exp_in,
            exp_out=exp_out,
            fee_bps=0,
        )

    return dx, (x2, y2)
