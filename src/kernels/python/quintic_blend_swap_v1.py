"""
Quintic-blend AMM swap kernel (v1 semantics).

Invariant family (symmetric, K(x,0)=0):

  K(x,y) := x*y*(x+y) * (x^2 + y^2 + c*x*y)

For integer arithmetic with c = c_num/c_den (c>=0):

  K_scaled(x,y) := x*y*(x+y) * (c_den*(x^2 + y^2) + c_num*x*y)

This kernel implements deterministic integer-only exact-in and exact-out quoting/execution:
- Fee is charged on gross input with ceil rounding (Uniswap-v2 style).
- Pricing uses `net_in = gross_in - fee_total`.
- Exact-in chooses the minimal y' such that K(x+net_in, y') >= K(x, y).
- Exact-out chooses the minimal gross_in such that exact-in outputs >= desired_out.
"""

from __future__ import annotations

from dataclasses import dataclass


def _require_int(name: str, value: int) -> None:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")


def _ceil_div_nonneg(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    if numerator < 0:
        raise ValueError("numerator must be non-negative")
    return (numerator + denominator - 1) // denominator


def _compute_fee_total(*, gross_in: int, fee_bps: int) -> int:
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


def _quintic_blend_k(*, x: int, y: int, c_num: int, c_den: int) -> int:
    if x < 0 or y < 0:
        raise ValueError("reserves must be non-negative")
    if c_num < 0 or c_den <= 0:
        raise ValueError("c_num must be non-negative, c_den must be positive")
    xi = int(x)
    yi = int(y)
    s = xi + yi
    quad_scaled = int(c_den) * (xi * xi + yi * yi) + int(c_num) * xi * yi
    return xi * yi * s * quad_scaled


def _min_y_satisfying_k(*, x1: int, y_max: int, k0: int, c_num: int, c_den: int) -> int:
    if x1 <= 0:
        raise ValueError("x1 must be positive")
    if y_max < 0:
        raise ValueError("y_max must be non-negative")
    if k0 < 0:
        raise ValueError("k0 must be non-negative")
    if c_num < 0 or c_den <= 0:
        raise ValueError("c_num must be non-negative, c_den must be positive")

    lo = 0
    hi = int(y_max)
    steps = max(1, (hi + 1).bit_length() + 1)
    for _ in range(steps):
        if lo >= hi:
            break
        mid = (lo + hi) // 2
        if _quintic_blend_k(x=x1, y=mid, c_num=c_num, c_den=c_den) >= k0:
            hi = mid
        else:
            lo = mid + 1
    return hi


def _min_x_satisfying_k(*, x0: int, y1: int, k0: int, c_num: int, c_den: int) -> int:
    if x0 <= 0:
        raise ValueError("x0 must be positive")
    if y1 <= 0:
        raise ValueError("y1 must be positive")
    if k0 < 0:
        raise ValueError("k0 must be non-negative")
    if c_num < 0 or c_den <= 0:
        raise ValueError("c_num must be non-negative, c_den must be positive")

    if _quintic_blend_k(x=x0, y=y1, c_num=c_num, c_den=c_den) >= k0:
        return int(x0)

    lo = int(x0) + 1
    hi = lo
    for _ in range(128):
        if _quintic_blend_k(x=hi, y=y1, c_num=c_num, c_den=c_den) >= k0:
            break
        hi = int(x0) + (hi - int(x0)) * 2
    else:
        raise ValueError("failed to bracket solution for x (unexpected)")

    steps = max(1, (hi - lo + 1).bit_length() + 1)
    for _ in range(steps):
        if lo >= hi:
            break
        mid = (lo + hi) // 2
        if _quintic_blend_k(x=mid, y=y1, c_num=c_num, c_den=c_den) >= k0:
            hi = mid
        else:
            lo = mid + 1
    return hi


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
    c_num: int,
    c_den: int,
    fee_bps: int = 0,
) -> SwapExactInResult:
    for name, v in (
        ("reserve_in", reserve_in),
        ("reserve_out", reserve_out),
        ("amount_in", amount_in),
        ("c_num", c_num),
        ("c_den", c_den),
        ("fee_bps", fee_bps),
    ):
        _require_int(name, v)

    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError("cannot swap against an empty reserve")
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if c_num < 0 or c_den <= 0:
        raise ValueError("c_num must be non-negative, c_den must be positive")
    if fee_bps < 0 or fee_bps > 10000:
        raise ValueError("fee_bps must be in [0, 10000]")

    x0 = int(reserve_in)
    y0 = int(reserve_out)
    dx_gross = int(amount_in)
    dx_net, fee_total = _net_in_after_fee(gross_in=dx_gross, fee_bps=int(fee_bps))
    if dx_net <= 0:
        raise ValueError("amount_in too small after fee")

    k0 = _quintic_blend_k(x=x0, y=y0, c_num=int(c_num), c_den=int(c_den))
    x_effective = x0 + dx_net
    if x_effective <= 0:
        raise ValueError("invalid post-swap reserve_in")

    y1 = _min_y_satisfying_k(
        x1=x_effective, y_max=y0, k0=k0, c_num=int(c_num), c_den=int(c_den)
    )

    if y1 > y0:
        raise ValueError("swap would require increasing reserve_out (invalid)")
    out = y0 - y1
    if out <= 0:
        raise ValueError("amount_out is zero (trade too small)")

    x_after = x0 + dx_gross
    k1 = _quintic_blend_k(x=x_after, y=y1, c_num=int(c_num), c_den=int(c_den))
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
    c_num: int,
    c_den: int,
    fee_bps: int = 0,
) -> SwapExactOutResult:
    for name, v in (
        ("reserve_in", reserve_in),
        ("reserve_out", reserve_out),
        ("amount_out", amount_out),
        ("c_num", c_num),
        ("c_den", c_den),
        ("fee_bps", fee_bps),
    ):
        _require_int(name, v)

    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError("cannot swap against an empty reserve")
    if amount_out <= 0:
        raise ValueError("amount_out must be positive")
    if amount_out >= reserve_out:
        raise ValueError("cannot drain full reserve_out")
    if c_num < 0 or c_den <= 0:
        raise ValueError("c_num must be non-negative, c_den must be positive")
    if fee_bps < 0 or fee_bps > 10000:
        raise ValueError("fee_bps must be in [0, 10000]")

    x0 = int(reserve_in)
    y0 = int(reserve_out)
    dy = int(amount_out)
    y_target = y0 - dy
    if y_target <= 0:
        raise ValueError("invalid post-swap reserve_out target")

    k0 = _quintic_blend_k(x=x0, y=y0, c_num=int(c_num), c_den=int(c_den))

    x_eff = _min_x_satisfying_k(
        x0=x0, y1=y_target, k0=k0, c_num=int(c_num), c_den=int(c_den)
    )
    if x_eff <= x0:
        x_eff = x0 + 1

    dx_net_required = x_eff - x0
    if dx_net_required <= 0:
        raise ValueError("failed to compute positive amount_in")

    dx_gross, dx_net, fee_total = _min_gross_for_net(target_net=int(dx_net_required), fee_bps=int(fee_bps))
    if dx_gross <= 0 or dx_net <= 0:
        raise ValueError("failed to compute positive amount_in")

    out_quote = int(
        swap_exact_in(
            reserve_in=x0,
            reserve_out=y0,
            amount_in=dx_gross,
            c_num=int(c_num),
            c_den=int(c_den),
            fee_bps=int(fee_bps),
        ).amount_out
    )
    if out_quote < dy:
        raise ValueError("computed amount_in insufficient for desired amount_out")

    if dx_gross > 1:
        try:
            r_prev = swap_exact_in(
                reserve_in=x0,
                reserve_out=y0,
                amount_in=dx_gross - 1,
                c_num=int(c_num),
                c_den=int(c_den),
                fee_bps=int(fee_bps),
            )
            if int(r_prev.amount_out) >= dy:
                raise ValueError("non-minimal amount_in: dx-1 still reaches desired output")
        except ValueError:
            pass

    x_after = x0 + dx_gross
    y_after = y_target
    k1 = _quintic_blend_k(x=x_after, y=y_after, c_num=int(c_num), c_den=int(c_den))
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

