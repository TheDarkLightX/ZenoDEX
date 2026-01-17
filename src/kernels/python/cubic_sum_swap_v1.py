"""
Cubic-sum AMM swap kernel (v1 semantics).

Invariant family:
  K(x,y) := x * y * (p*x + q*y)
Baseline: p=q=1 => K(x,y) = x*y*(x+y)

This kernel implements deterministic integer-only exact-in and exact-out quoting/execution:
- Exact-in chooses the minimal post-swap reserve_out y' such that K(x+dx, y') >= K(x,y).
- Exact-out chooses the minimal dx such that executing exact-in with dx yields output >= desired_out.

Rounding:
- Uses integer ceil division and integer ceil square root.
- Normalizes the computed ceil-root down to the minimal satisfying integer with a bounded loop.
"""

from __future__ import annotations

import math
from dataclasses import dataclass


def _require_int(name: str, value: int) -> None:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")


def _compute_fee_total(*, gross_in: int, fee_bps: int) -> int:
    """
    Deterministic fee computation (ceil rounding), matching the repo's CPMM fee rule:
        fee_total = ceil(gross_in * fee_bps / 10_000)
    """
    if fee_bps < 0 or fee_bps > 10000:
        raise ValueError("fee_bps must be in [0, 10000]")
    if gross_in < 0:
        raise ValueError("gross_in must be non-negative")
    if gross_in == 0 or fee_bps == 0:
        return 0
    return _ceil_div_nonneg(gross_in * fee_bps, 10_000)


def _net_in_after_fee(*, gross_in: int, fee_bps: int) -> tuple[int, int]:
    fee_total = _compute_fee_total(gross_in=gross_in, fee_bps=fee_bps)
    net = int(gross_in) - int(fee_total)
    return net, fee_total


def _min_gross_for_net(*, target_net: int, fee_bps: int) -> tuple[int, int, int]:
    """
    Compute the minimal gross amount such that net(gross, fee_bps) >= target_net.
    Returns (gross, net, fee_total).
    """
    if target_net <= 0:
        raise ValueError("target_net must be positive")
    if fee_bps < 0 or fee_bps > 10000:
        raise ValueError("fee_bps must be in [0, 10000]")
    if fee_bps == 0:
        return int(target_net), int(target_net), 0
    denom = 10_000 - int(fee_bps)
    if denom <= 0:
        raise ValueError("fee_bps too large (no net input possible)")

    # Lower bound under the linearized relation net ≈ gross * denom / 10_000.
    gross = _ceil_div_nonneg(int(target_net) * 10_000, denom)

    # Tighten to the true minimal solution under ceil fee rounding.
    for _ in range(64):
        net, fee_total = _net_in_after_fee(gross_in=int(gross), fee_bps=int(fee_bps))
        if net >= int(target_net):
            break
        gross += 1
    else:
        raise RuntimeError("failed to reach target net within bound (unexpected)")

    for _ in range(64):
        if gross <= 1:
            break
        net_prev, _ = _net_in_after_fee(gross_in=int(gross) - 1, fee_bps=int(fee_bps))
        if net_prev >= int(target_net):
            gross -= 1
            continue
        break
    net, fee_total = _net_in_after_fee(gross_in=int(gross), fee_bps=int(fee_bps))
    return int(gross), int(net), int(fee_total)


def _ceil_div_nonneg(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    if numerator < 0:
        raise ValueError("numerator must be non-negative")
    return (numerator + denominator - 1) // denominator


def _ceil_isqrt(n: int) -> int:
    if n < 0:
        raise ValueError("n must be non-negative")
    r = math.isqrt(n)
    return r if r * r == n else r + 1


def _cubic_sum_k(*, x: int, y: int, p: int, q: int) -> int:
    if x < 0 or y < 0:
        raise ValueError("reserves must be non-negative")
    if p <= 0 or q <= 0:
        raise ValueError("p and q must be positive")
    return int(x) * int(y) * (int(p) * int(x) + int(q) * int(y))


_MAX_NORMALIZE_STEPS = 8


def _normalize_min_satisfying_root(*, candidate: int, a: int, b: int, k0: int) -> int:
    """
    Given a candidate y that satisfies: a*y^2 + b*y - k0 >= 0, normalize it down to
    the minimal satisfying integer by checking y-1.
    """
    if candidate < 0:
        raise ValueError("candidate must be non-negative")
    if a <= 0:
        raise ValueError("a must be positive")
    if b < 0:
        raise ValueError("b must be non-negative")
    if k0 < 0:
        raise ValueError("k0 must be non-negative")

    y = int(candidate)
    for _ in range(_MAX_NORMALIZE_STEPS):
        if y <= 0:
            return 0
        y_prev = y - 1
        lhs_prev = a * y_prev * y_prev + b * y_prev
        if lhs_prev >= k0:
            y = y_prev
            continue
        return y
    raise RuntimeError("normalize loop exceeded bound (unexpected)")


@dataclass(frozen=True)
class SwapExactInResult:
    amount_out: int
    amount_in: int
    amount_in_net: int
    fee_total: int
    new_reserve_in: int
    new_reserve_out: int
    k_before: int
    k_after: int


@dataclass(frozen=True)
class SwapExactOutResult:
    amount_in: int
    amount_out: int
    amount_out_quote: int
    amount_in_net: int
    fee_total: int
    new_reserve_in: int
    new_reserve_out: int
    k_before: int
    k_after: int


def swap_exact_in(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    p: int = 1,
    q: int = 1,
    fee_bps: int = 0,
) -> SwapExactInResult:
    """
    Exact-in swap under K(x,y)=x*y*(p*x + q*y), with deterministic rounding.

    Semantics:
      x' = x + dx
      y' = min integer y' such that K(x', y') >= K(x, y)
      amount_out = y - y'
      post-state reserves are (x', y')
    """
    for name, v in (
        ("reserve_in", reserve_in),
        ("reserve_out", reserve_out),
        ("amount_in", amount_in),
        ("p", p),
        ("q", q),
        ("fee_bps", fee_bps),
    ):
        _require_int(name, v)

    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError("cannot swap against an empty reserve")
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if p <= 0 or q <= 0:
        raise ValueError("p and q must be positive")
    if fee_bps < 0 or fee_bps > 10000:
        raise ValueError("fee_bps must be in [0, 10000]")

    x0 = int(reserve_in)
    y0 = int(reserve_out)
    dx_gross = int(amount_in)
    dx_net, fee_total = _net_in_after_fee(gross_in=dx_gross, fee_bps=int(fee_bps))
    if dx_net <= 0:
        raise ValueError("amount_in too small after fee")

    k0 = _cubic_sum_k(x=x0, y=y0, p=p, q=q)
    x_effective = x0 + dx_net
    if x_effective <= 0:
        raise ValueError("invalid post-swap reserve_in")

    # Solve for minimal y1 such that:
    #   K(x1, y1) = p*x1^2*y1 + q*x1*y1^2 >= k0
    # Quadratic in y1: (q*x1)*y1^2 + (p*x1^2)*y1 - k0 >= 0
    a = q * x_effective
    b = p * x_effective * x_effective
    D = b * b + 4 * a * k0
    s = _ceil_isqrt(D)
    y_cand = _ceil_div_nonneg(max(0, s - b), 2 * a)
    y1 = _normalize_min_satisfying_root(candidate=y_cand, a=a, b=b, k0=k0)

    if y1 > y0:
        raise ValueError("swap would require increasing reserve_out (invalid)")
    out = y0 - y1
    if out <= 0:
        raise ValueError("amount_out is zero (trade too small)")

    x_after = x0 + dx_gross
    k1 = _cubic_sum_k(x=x_after, y=y1, p=p, q=q)
    if k1 < k0:
        raise ValueError("invariant violation: K decreased")

    return SwapExactInResult(
        amount_out=int(out),
        amount_in=int(dx_gross),
        amount_in_net=int(dx_net),
        fee_total=int(fee_total),
        new_reserve_in=int(x_after),
        new_reserve_out=int(y1),
        k_before=int(k0),
        k_after=int(k1),
    )


def swap_exact_out(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    p: int = 1,
    q: int = 1,
    fee_bps: int = 0,
) -> SwapExactOutResult:
    """
    Exact-out quote + post-state.

    Semantics:
      Given desired_out = dy (0 < dy < y),
      return the minimal dx such that exact-in with dx yields output >= dy.

    Post-state:
      new_reserve_in = x + dx
      new_reserve_out = y - dy

    Note: If you were to execute exact-in with this dx instead, you may receive MORE
    than dy due to rounding. That difference is the "overdelivery gap" phenomenon.
    """
    for name, v in (
        ("reserve_in", reserve_in),
        ("reserve_out", reserve_out),
        ("amount_out", amount_out),
        ("p", p),
        ("q", q),
        ("fee_bps", fee_bps),
    ):
        _require_int(name, v)

    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError("cannot swap against an empty reserve")
    if amount_out <= 0:
        raise ValueError("amount_out must be positive")
    if amount_out >= reserve_out:
        raise ValueError("cannot drain full reserve_out")
    if p <= 0 or q <= 0:
        raise ValueError("p and q must be positive")
    if fee_bps < 0 or fee_bps > 10000:
        raise ValueError("fee_bps must be in [0, 10000]")

    x0 = int(reserve_in)
    y0 = int(reserve_out)
    dy = int(amount_out)
    y_target = y0 - dy
    if y_target <= 0:
        raise ValueError("invalid post-swap reserve_out target")

    k0 = _cubic_sum_k(x=x0, y=y0, p=p, q=q)

    # Solve for minimal x1 such that:
    #   K(x1, y_target) = p*y_target*x1^2 + q*y_target^2*x1 >= k0
    # Quadratic in x1: (p*y_target)*x1^2 + (q*y_target^2)*x1 - k0 >= 0
    a = p * y_target
    b = q * y_target * y_target
    D = b * b + 4 * a * k0
    s = _ceil_isqrt(D)
    x_cand = _ceil_div_nonneg(max(0, s - b), 2 * a)
    x1 = _normalize_min_satisfying_root(candidate=x_cand, a=a, b=b, k0=k0)
    if x1 <= x0:
        x1 = x0 + 1

    dx_net_required = x1 - x0
    if dx_net_required <= 0:
        raise ValueError("failed to compute positive amount_in")

    dx_gross, dx_net, fee_total = _min_gross_for_net(target_net=int(dx_net_required), fee_bps=int(fee_bps))
    if dx_gross <= 0 or dx_net <= 0:
        raise ValueError("failed to compute positive amount_in")

    # Safety check: feeding the gross dx into exact-in must output at least dy.
    out_quote = int(
        swap_exact_in(reserve_in=x0, reserve_out=y0, amount_in=dx_gross, p=p, q=q, fee_bps=int(fee_bps)).amount_out
    )
    if out_quote < dy:
        raise ValueError("computed amount_in insufficient for desired amount_out")

    # Minimality check: dx-1 must fail to reach dy (if dx>1).
    if dx_gross > 1:
        try:
            r_prev = swap_exact_in(reserve_in=x0, reserve_out=y0, amount_in=dx_gross - 1, p=p, q=q, fee_bps=int(fee_bps))
            if int(r_prev.amount_out) >= dy:
                raise ValueError("non-minimal amount_in: dx-1 still reaches desired output")
        except ValueError:
            pass

    x_after = x0 + dx_gross
    y_after = y_target
    k1 = _cubic_sum_k(x=x_after, y=y_after, p=p, q=q)
    if k1 < k0:
        raise ValueError("invariant violation: K decreased")

    return SwapExactOutResult(
        amount_in=int(dx_gross),
        amount_out=int(dy),
        amount_out_quote=int(out_quote),
        amount_in_net=int(dx_net),
        fee_total=int(fee_total),
        new_reserve_in=int(x_after),
        new_reserve_out=int(y_after),
        k_before=int(k0),
        k_after=int(k1),
    )
