"""
Perpetuals rounding helpers (deterministic, integer-only).

This module captures a consensus-critical fact recorded in PopperPad:

- Per-account Euclidean division of PnL can violate conservation even when net exposure is zero.
- Under net-zero exposure, conservation can be restored deterministically by a "largest remainder" dust allocator.

See: `internal/popperpad_mcp/bootstrap_zenodex_pad.py`:
- H_perp_rounding_leak_exists_under_euclidean_div
- H_perp_rounding_fix_largest_remainder_net_zero
"""

from __future__ import annotations

from typing import Iterable, List, Sequence


def euclid_div_rem(x: int, d: int) -> tuple[int, int]:
    """
    Euclidean division for integers with positive divisor.

    Returns (q, r) such that:
    - x = q*d + r
    - 0 <= r < d
    """
    if not isinstance(x, int) or isinstance(x, bool):
        raise TypeError("x must be an int")
    if not isinstance(d, int) or isinstance(d, bool):
        raise TypeError("d must be an int")
    if d <= 0:
        raise ValueError("d must be positive")

    q = x // d
    r = x - q * d
    if not (0 <= r < d):
        raise AssertionError("internal error: remainder out of range")
    return q, r


def largest_remainder_adjust_net_zero(*, xs: Sequence[int], keys: Sequence[str], d: int) -> List[int]:
    """
    Deterministic dust allocator that restores conservation under net-zero sums.

    Preconditions:
    - d > 0
    - len(xs) == len(keys) >= 1
    - sum(xs) == 0

    Let q_i := xs_i div d (Euclidean, i.e. floor for positive d) and r_i the Euclidean remainder.
    With sum(xs)=0, sum(q_i) <= 0. Define need := -sum(q_i).

    This returns q'_i where:
    - q'_i is either q_i or q_i + 1
    - sum(q'_i) == 0
    - the +1 adjustments go to the indices with the largest remainders r_i,
      tie-broken lexicographically by keys[i] (deterministic).
    """
    if not isinstance(d, int) or isinstance(d, bool):
        raise TypeError("d must be an int")
    if d <= 0:
        raise ValueError("d must be positive")

    if not isinstance(xs, Sequence):
        raise TypeError("xs must be a sequence")
    if not isinstance(keys, Sequence):
        raise TypeError("keys must be a sequence")
    if len(xs) != len(keys):
        raise ValueError("xs and keys must have the same length")
    if not xs:
        raise ValueError("xs must be non-empty")

    qs: list[int] = []
    rs: list[int] = []
    for i, x in enumerate(xs):
        if not isinstance(x, int) or isinstance(x, bool):
            raise TypeError(f"xs[{i}] must be an int")
        key = keys[i]
        if not isinstance(key, str) or not key:
            raise TypeError(f"keys[{i}] must be a non-empty string")
        q, r = euclid_div_rem(x, d)
        qs.append(q)
        rs.append(r)

    if sum(xs) != 0:
        raise ValueError("sum(xs) must be 0 (net-zero precondition)")

    need = -sum(qs)
    if need < 0:
        raise AssertionError("internal error: expected sum(qs) <= 0 under sum(xs)=0")
    if need == 0:
        return list(qs)

    order = sorted(range(len(xs)), key=lambda i: (-rs[i], keys[i]))
    out = list(qs)
    for i in order[:need]:
        out[i] += 1

    if sum(out) != 0:
        raise AssertionError("internal error: dust allocation failed to restore conservation")
    return out


def mul_sum(xs: Iterable[int]) -> int:
    """
    Small helper: sum of a sequence of ints (guards out bool).
    """
    total = 0
    for x in xs:
        if not isinstance(x, int) or isinstance(x, bool):
            raise TypeError("mul_sum expects ints")
        total += x
    return total

