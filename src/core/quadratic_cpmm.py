"""
Quadratic CPMM (research curve): invariant K = x^2 * y.

This is a *new curve design* that keeps integer-only math (no fractional exponents),
yet yields a meaningfully different price curve than constant product.

Motivation:
- DEX curves are invariants over reserves; CPMM uses K = x*y.
- By changing invariant families, we change price impact and liquidity profile.
- For consensus-critical math we want deterministic rounding and simple proofs.

This module is intentionally self-contained and conservative:
- fee_bps is currently restricted to 0 (to keep the invariant semantics crisp).
- rounding is chosen to keep K' >= K (monotone non-decreasing invariant).
"""

from __future__ import annotations

import math
from typing import Tuple

from ..state.balances import Amount


def _ceil_div(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError("b must be positive")
    if a < 0:
        raise ValueError("a must be non-negative")
    return (a + b - 1) // b


def _ceil_isqrt(n: int) -> int:
    if n < 0:
        raise ValueError("n must be non-negative")
    r = math.isqrt(n)
    return r if r * r == n else r + 1


def quadratic_k(x: Amount, y: Amount) -> int:
    if x < 0 or y < 0:
        raise ValueError("reserves must be non-negative")
    return int(x) * int(x) * int(y)


def swap_exact_in_quadratic(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_in: Amount,
    *,
    fee_bps: int = 0,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """
    Exact-in swap under K = x^2 * y.

    Conservative rounding:
      y' = ceil(K / (x + dx)^2)
      amount_out = y - y'
    This ensures:
      (x+dx)^2 * y' >= K  => K' >= K  (monotone invariant)
    """
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError("reserves must be non-negative")
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if fee_bps != 0:
        raise ValueError("quadratic_cpmm: fee_bps must be 0 in this reference implementation")

    x = int(reserve_in)
    y = int(reserve_out)
    dx = int(amount_in)

    k0 = x * x * y
    x1 = x + dx
    denom = x1 * x1
    y1 = _ceil_div(k0, denom)
    if y1 > y:
        raise ValueError("swap would require increasing reserve_out (invalid)")
    out = y - y1
    if out <= 0:
        raise ValueError("amount_out is non-positive")

    k1 = x1 * x1 * y1
    if k1 < k0:
        raise ValueError("invariant violation: K decreased")

    return out, (x1, y1)


def swap_exact_out_quadratic(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
    *,
    fee_bps: int = 0,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """
    Exact-out swap under K = x^2 * y.

    For desired dy:
      y' = y - dy
      Need minimal x' such that x'^2 * y' >= K
      => x' >= ceil_sqrt( ceil(K / y') )
      dx = x' - x
    """
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError("reserves must be non-negative")
    if amount_out <= 0:
        raise ValueError("amount_out must be positive")
    if amount_out >= reserve_out:
        raise ValueError("cannot drain full reserve_out")
    if fee_bps != 0:
        raise ValueError("quadratic_cpmm: fee_bps must be 0 in this reference implementation")

    x = int(reserve_in)
    y = int(reserve_out)
    dy = int(amount_out)
    y1 = y - dy
    k0 = x * x * y

    need = _ceil_div(k0, y1)
    x1 = _ceil_isqrt(need)
    if x1 < x:
        x1 = x
    dx = x1 - x
    if dx <= 0:
        dx = 1  # ensure progress; conservative
        x1 = x + dx
        y1 = _ceil_div(k0, x1 * x1)

    # Recompute using exact-in rule with dx to ensure consistent rounding.
    out_check, (x2, y2) = swap_exact_in_quadratic(x, y, dx, fee_bps=0)
    if out_check < dy:
        # Increase dx until it satisfies dy (bounded by monotonicity)
        while out_check < dy:
            dx += 1
            out_check, (x2, y2) = swap_exact_in_quadratic(x, y, dx, fee_bps=0)

    return dx, (x2, y2)

