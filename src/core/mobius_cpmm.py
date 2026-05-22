"""
Möbius (fractional-linear) representation utilities for CPMM.

This module is **analysis/UX tooling**, not consensus-critical math:
- It represents the *continuous* CPMM swap formula as a Möbius transform (2x2 matrix).
- It is useful for cheap composition, upper bounds, and heuristic seeds.

Important:
- The strong claim "sequential integer floor-per-hop swaps == floor(collapsed expression)"
  is false in general. Treat Möbius evaluation as an optimistic *upper bound* / seed and
  refine using the exact integer swap kernels for any promoted result.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class Mobius:
    """
    Fractional-linear transform:
        z ↦ (a*z + b) / (c*z + d)

    Composition corresponds to 2x2 matrix multiplication:
        (M2 ∘ M1)(z) == (M2 @ M1)(z)
    """

    a: int
    b: int
    c: int
    d: int

    def __matmul__(self, other: "Mobius") -> "Mobius":
        # Matrix multiplication:
        #   [[a,b],[c,d]] * [[a',b'],[c',d']] =
        #     [[a*a' + b*c', a*b' + b*d'],
        #      [c*a' + d*c', c*b' + d*d']]
        return Mobius(
            a=(self.a * other.a) + (self.b * other.c),
            b=(self.a * other.b) + (self.b * other.d),
            c=(self.c * other.a) + (self.d * other.c),
            d=(self.c * other.b) + (self.d * other.d),
        )

    def eval_fraction(self, z: Fraction) -> Fraction:
        num = (Fraction(self.a) * z) + Fraction(self.b)
        den = (Fraction(self.c) * z) + Fraction(self.d)
        if den == 0:
            raise ZeroDivisionError("Mobius denominator is zero")
        # Avoid `/` in core to prevent accidental float semantics leaking in.
        return num * Fraction(int(den.denominator), int(den.numerator))

    def eval_floor_int(self, z: int) -> int:
        """
        Evaluate the transform at integer z and take math.floor of the result.

        For non-negative coefficients + z >= 0, this reduces to:
            floor(num/den) == num // den
        """
        if not isinstance(z, int) or isinstance(z, bool):
            raise TypeError("z must be an int")
        num = (self.a * z) + self.b
        den = (self.c * z) + self.d
        if den == 0:
            raise ZeroDivisionError("Mobius denominator is zero")
        # Python's // is mathematical floor division, including for negative values.
        return num // den


def cpmm_pool_mobius(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_mul_num: int = 1,
    fee_mul_den: int = 1,
) -> Mobius:
    """
    Continuous CPMM output under an input multiplier:

      net = dx * fee_mul_num / fee_mul_den
      out = reserve_out * net / (reserve_in + net)
          = (reserve_out * fee_mul_num * dx) / (fee_mul_num * dx + reserve_in * fee_mul_den)

    This equals the Mobius transform:
      [[reserve_out * fee_mul_num, 0],
       [fee_mul_num, reserve_in * fee_mul_den]]

    Notes:
    - fee_mul is a *continuous* multiplier; the discrete kernel uses ceil/floor rounding.
    - For fee=0, use fee_mul_num=fee_mul_den=1.
    """
    for name, v in (
        ("reserve_in", reserve_in),
        ("reserve_out", reserve_out),
        ("fee_mul_num", fee_mul_num),
        ("fee_mul_den", fee_mul_den),
    ):
        if not isinstance(v, int) or isinstance(v, bool):
            raise TypeError(f"{name} must be an int")
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError("reserves must be non-negative")
    if fee_mul_num <= 0 or fee_mul_den <= 0:
        raise ValueError("fee_mul_* must be positive")
    return Mobius(
        a=reserve_out * fee_mul_num,
        b=0,
        c=fee_mul_num,
        d=reserve_in * fee_mul_den,
    )


def cpmm_two_hop_collapsed_floor_fee0(
    *,
    x1: int,
    y1: int,
    x2: int,
    y2: int,
    dx: int,
) -> int:
    """
    Closed-form, *continuous-composed then floored* 2-hop CPMM output (fee=0):

      floor( (y1*y2*dx) / ((y1 + x2)*dx + x1*x2) )

    This is an optimistic upper bound on sequential per-hop integer-floor outputs.
    """
    for name, v in (("x1", x1), ("y1", y1), ("x2", x2), ("y2", y2), ("dx", dx)):
        if not isinstance(v, int) or isinstance(v, bool):
            raise TypeError(f"{name} must be an int")
    if x1 <= 0 or y1 <= 0 or x2 <= 0 or y2 <= 0 or dx <= 0:
        raise ValueError("x1,y1,x2,y2,dx must be positive")
    num = y1 * y2 * dx
    den = ((y1 + x2) * dx) + (x1 * x2)
    return num // den
