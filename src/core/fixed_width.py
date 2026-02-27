"""Fixed-width arithmetic helpers (analysis/testing only).

This module is intended for:
- Representation intractability detection (overflow/underflow regimes).
- Differential testing of algorithms under bigint vs fixed-width assumptions.

It must not be used for consensus-critical decisions unless the surrounding
protocol explicitly commits to the same fixed-width semantics and guards.
"""

from __future__ import annotations

from dataclasses import dataclass


def uN_max(bits: int) -> int:
    if bits <= 0:
        raise ValueError("bits must be positive")
    return (1 << int(bits)) - 1


def uN_mod(bits: int) -> int:
    if bits <= 0:
        raise ValueError("bits must be positive")
    return 1 << int(bits)


def _check_uN(bits: int, x: int) -> None:
    if not isinstance(x, int) or isinstance(x, bool):
        raise TypeError("value must be an int")
    if x < 0:
        raise ValueError("value must be non-negative")
    if x > uN_max(bits):
        raise ValueError(f"value out of range for u{bits}")


def will_add_overflow(bits: int, a: int, b: int) -> bool:
    _check_uN(bits, a)
    _check_uN(bits, b)
    return int(a) + int(b) > uN_max(bits)


def will_mul_overflow(bits: int, a: int, b: int) -> bool:
    _check_uN(bits, a)
    _check_uN(bits, b)
    if a == 0 or b == 0:
        return False
    return int(a) * int(b) > uN_max(bits)


def add_checked(bits: int, a: int, b: int) -> int:
    if will_add_overflow(bits, a, b):
        raise OverflowError(f"u{bits} add overflow")
    return int(a) + int(b)


def mul_checked(bits: int, a: int, b: int) -> int:
    if will_mul_overflow(bits, a, b):
        raise OverflowError(f"u{bits} mul overflow")
    return int(a) * int(b)


def add_wrap(bits: int, a: int, b: int) -> int:
    _check_uN(bits, a)
    _check_uN(bits, b)
    return (int(a) + int(b)) % uN_mod(bits)


def mul_wrap(bits: int, a: int, b: int) -> int:
    _check_uN(bits, a)
    _check_uN(bits, b)
    return (int(a) * int(b)) % uN_mod(bits)


U256_BITS = 256
U256_MAX = uN_max(U256_BITS)


@dataclass(frozen=True)
class OverflowTriplet:
    """Convenience holder for (a,b) with an overflow verdict."""

    a: int
    b: int
    overflows: bool

