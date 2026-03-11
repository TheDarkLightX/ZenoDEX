"""u256 overflow analysis for CPMM arithmetic (analysis/testing only).

This module is useful when:
- Translating kernels to fixed-width environments (EVM-like, or bv-based solvers).
- Detecting representation intractability (where proofs over bvW diverge from bigint).

It provides:
- Overflow flags for naive u256 checked arithmetic.
- A provably equivalent, overflow-safer fee computation via quotient/remainder.
"""

from __future__ import annotations

from dataclasses import dataclass
import math

from .fixed_width import U256_BITS, U256_MAX, will_add_overflow, will_mul_overflow


def fee_total_ceil_bigint(gross_in: int, fee_bps: int) -> int:
    """Reference: ceil(gross_in * fee_bps / 10_000) in bigint math."""
    if gross_in < 0:
        raise ValueError("gross_in must be non-negative")
    if not (0 <= fee_bps <= 10_000):
        raise ValueError("fee_bps out of range")
    return (int(gross_in) * int(fee_bps) + 10_000 - 1) // 10_000


def fee_total_ceil_decomposed(gross_in: int, fee_bps: int) -> int:
    """Equivalent fee computation that reduces overflow risk in fixed-width code.

    Let gross_in = 10_000*q + r with 0 <= r < 10_000.
    Then:
      ceil(gross_in * fee / 10_000)
        = q*fee + ceil(r*fee/10_000)
    """
    if gross_in < 0:
        raise ValueError("gross_in must be non-negative")
    if not (0 <= fee_bps <= 10_000):
        raise ValueError("fee_bps out of range")
    q, r = divmod(int(gross_in), 10_000)
    # q*fee_bps is the dominant term but q is smaller by 10_000.
    return int(q) * int(fee_bps) + (int(r) * int(fee_bps) + 10_000 - 1) // 10_000


def mul_div_floor_gcd_reduced_u256(*, a: int, b: int, c: int) -> int | None:
    """Try to compute floor(a*b/c) exactly under u256 constraints, using gcd reduction.

    Returns:
      - int result if intermediate products can be kept within u256.
      - None if a u256 overflow would still be required (intractable without a 512-bit mulDiv).
    """
    if a < 0 or b < 0 or c <= 0:
        raise ValueError("a,b must be non-negative and c must be positive")
    if a > U256_MAX or b > U256_MAX or c > U256_MAX:
        raise ValueError("inputs must fit in u256")

    # Cancel common factors before multiplying to reduce overflow risk.
    g1 = math.gcd(int(a), int(c))
    a1 = int(a) // int(g1)
    c1 = int(c) // int(g1)

    g2 = math.gcd(int(b), int(c1))
    b1 = int(b) // int(g2)
    c2 = int(c1) // int(g2)

    # Now compute floor(a1*b1/c2) if a1*b1 fits in u256.
    if will_mul_overflow(U256_BITS, int(a1), int(b1)):
        return None
    return (int(a1) * int(b1)) // int(c2)


@dataclass(frozen=True)
class CpmmExactInU256OverflowReport:
    reserve_in: int
    reserve_out: int
    amount_in: int
    fee_bps: int

    fee_mul_overflow_naive: bool
    fee_mul_overflow_decomposed: bool
    denom_add_overflow: bool
    numerator_mul_overflow: bool

    fee_total: int
    net_in: int


def analyze_cpmm_exact_in_u256_overflows(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
) -> CpmmExactInU256OverflowReport:
    """Return u256 overflow flags for naive CPMM exact-in arithmetic.

    We treat all values as u256 inputs (0 <= x <= 2^256-1). Any negative inputs
    raise ValueError.
    """
    for name, v in (
        ("reserve_in", reserve_in),
        ("reserve_out", reserve_out),
        ("amount_in", amount_in),
        ("fee_bps", fee_bps),
    ):
        if not isinstance(v, int) or isinstance(v, bool):
            raise TypeError(f"{name} must be an int")
        if v < 0:
            raise ValueError(f"{name} must be non-negative")
    if reserve_in > U256_MAX or reserve_out > U256_MAX or amount_in > U256_MAX:
        raise ValueError("inputs must fit in u256")
    if fee_bps > 10_000:
        raise ValueError("fee_bps out of range")

    fee_mul_overflow_naive = will_mul_overflow(U256_BITS, int(amount_in), int(fee_bps))

    # Decomposed fee overflow posture:
    q, r = divmod(int(amount_in), 10_000)
    fee_mul_overflow_decomposed = will_mul_overflow(U256_BITS, int(q), int(fee_bps)) or will_mul_overflow(
        U256_BITS, int(r), int(fee_bps)
    )

    fee_total = fee_total_ceil_decomposed(int(amount_in), int(fee_bps))
    net_in = int(amount_in) - int(fee_total)

    denom_add_overflow = will_add_overflow(U256_BITS, int(reserve_in), int(net_in))
    numerator_mul_overflow = will_mul_overflow(U256_BITS, int(reserve_out), int(net_in))

    return CpmmExactInU256OverflowReport(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        amount_in=int(amount_in),
        fee_bps=int(fee_bps),
        fee_mul_overflow_naive=bool(fee_mul_overflow_naive),
        fee_mul_overflow_decomposed=bool(fee_mul_overflow_decomposed),
        denom_add_overflow=bool(denom_add_overflow),
        numerator_mul_overflow=bool(numerator_mul_overflow),
        fee_total=int(fee_total),
        net_in=int(net_in),
    )
