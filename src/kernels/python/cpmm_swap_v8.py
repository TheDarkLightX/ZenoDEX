"""
CPMM swap kernel (v8 semantics).

This implements the semantics described in `src/kernels/dex/cpmm_swap_v8.yaml`:
- Fee is charged on the *gross* input amount using ceil rounding.
- Pricing uses `net_in = gross_in - fee_total` (Uniswap-v2 style).
- LP fee stays in the pool; an optional protocol fee share may be removed.

This kernel is intended as a small, auditable, integer-only implementation that
can be used in the Python functional core today and swapped for a Rust kernel
later if desired.
"""

from __future__ import annotations

from dataclasses import dataclass


BPS_DENOM = 10_000


def _require_int(name: str, value: int) -> None:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")


def _ceil_div_nonneg(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    if numerator < 0:
        raise ValueError("numerator must be non-negative")
    return (numerator + denominator - 1) // denominator


@dataclass(frozen=True)
class SwapExactInResult:
    amount_out: int
    fee_total: int
    protocol_fee: int
    lp_fee: int
    net_in: int
    gross_in: int
    new_reserve_in: int
    new_reserve_out: int
    k_before: int
    k_after: int


@dataclass(frozen=True)
class SwapExactOutResult:
    amount_in: int
    amount_out: int
    fee_total: int
    protocol_fee: int
    lp_fee: int
    net_in: int
    gross_in: int
    new_reserve_in: int
    new_reserve_out: int
    k_before: int
    k_after: int


def compute_fee_total(*, gross_in: int, fee_bps: int) -> int:
    """
    Compute `fee_total = ceil(gross_in * fee_bps / 10_000)`.
    """
    _require_int("gross_in", gross_in)
    _require_int("fee_bps", fee_bps)
    if gross_in < 0:
        raise ValueError("gross_in must be non-negative")
    if not (0 <= fee_bps <= BPS_DENOM):
        raise ValueError(f"fee_bps must be in [0, {BPS_DENOM}]")
    return _ceil_div_nonneg(gross_in * fee_bps, BPS_DENOM)


def compute_protocol_fee(*, fee_total: int, protocol_fee_share_bps: int) -> int:
    """
    Compute `protocol_fee = floor(fee_total * protocol_fee_share_bps / 10_000)`.
    """
    _require_int("fee_total", fee_total)
    _require_int("protocol_fee_share_bps", protocol_fee_share_bps)
    if fee_total < 0:
        raise ValueError("fee_total must be non-negative")
    if not (0 <= protocol_fee_share_bps <= BPS_DENOM):
        raise ValueError(f"protocol_fee_share_bps must be in [0, {BPS_DENOM}]")
    return (fee_total * protocol_fee_share_bps) // BPS_DENOM


def swap_exact_in(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    protocol_fee_share_bps: int = 0,
) -> SwapExactInResult:
    """
    Exact-in swap quote + post-state.

    Raises ValueError on invalid inputs or if the swap would produce a zero output.
    """
    for name, v in (
        ("reserve_in", reserve_in),
        ("reserve_out", reserve_out),
        ("amount_in", amount_in),
        ("fee_bps", fee_bps),
        ("protocol_fee_share_bps", protocol_fee_share_bps),
    ):
        _require_int(name, v)

    if reserve_in < 0 or reserve_out < 0:
        raise ValueError("reserves must be non-negative")
    if reserve_in == 0 or reserve_out == 0:
        raise ValueError("cannot swap against an empty reserve")
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if not (0 <= fee_bps <= BPS_DENOM):
        raise ValueError(f"fee_bps must be in [0, {BPS_DENOM}]")
    if not (0 <= protocol_fee_share_bps <= BPS_DENOM):
        raise ValueError(f"protocol_fee_share_bps must be in [0, {BPS_DENOM}]")

    k_before = reserve_in * reserve_out

    fee_total = compute_fee_total(gross_in=amount_in, fee_bps=fee_bps)
    if fee_total > amount_in:
        raise ValueError("fee_total exceeds amount_in")
    net_in = amount_in - fee_total
    if net_in <= 0:
        raise ValueError("net_in must be positive after fees")

    protocol_fee = compute_protocol_fee(fee_total=fee_total, protocol_fee_share_bps=protocol_fee_share_bps)
    if protocol_fee > fee_total:
        raise ValueError("protocol_fee exceeds fee_total")
    lp_fee = fee_total - protocol_fee

    denominator = reserve_in + net_in
    if denominator <= 0:
        raise ValueError("invalid denominator")
    amount_out = (reserve_out * net_in) // denominator

    if amount_out <= 0:
        raise ValueError("amount_out is zero (trade too small)")
    if amount_out > reserve_out:
        raise ValueError("amount_out exceeds reserve_out")

    new_reserve_in = reserve_in + amount_in - protocol_fee
    new_reserve_out = reserve_out - amount_out
    if new_reserve_in < 0 or new_reserve_out < 0:
        raise ValueError("post-swap reserves must be non-negative")

    k_after = new_reserve_in * new_reserve_out

    return SwapExactInResult(
        amount_out=amount_out,
        fee_total=fee_total,
        protocol_fee=protocol_fee,
        lp_fee=lp_fee,
        net_in=net_in,
        gross_in=amount_in,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
        k_before=k_before,
        k_after=k_after,
    )


def swap_exact_out(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
) -> SwapExactOutResult:
    """Exact-out swap quote + post-state (protocol fee share fixed at 0 for now)."""
    for name, v in (
        ("reserve_in", reserve_in),
        ("reserve_out", reserve_out),
        ("amount_out", amount_out),
        ("fee_bps", fee_bps),
    ):
        _require_int(name, v)

    if reserve_in < 0 or reserve_out < 0:
        raise ValueError("reserves must be non-negative")
    if reserve_in == 0 or reserve_out == 0:
        raise ValueError("cannot swap against an empty reserve")
    if amount_out <= 0:
        raise ValueError("amount_out must be positive")
    if amount_out >= reserve_out:
        raise ValueError("cannot drain full reserve_out")
    if not (0 <= fee_bps <= BPS_DENOM):
        raise ValueError(f"fee_bps must be in [0, {BPS_DENOM}]")
    if fee_bps == BPS_DENOM:
        raise ValueError("cannot compute with 100% fee")

    # net_in = ceil(reserve_in * amount_out / (reserve_out - amount_out))
    numerator = reserve_in * amount_out
    denominator = reserve_out - amount_out
    net_in = _ceil_div_nonneg(numerator, denominator)
    if net_in <= 0:
        raise ValueError("net_in must be positive")

    # amount_in = ceil(net_in / (1 - fee_bps/10_000))
    fee_denominator = BPS_DENOM - fee_bps
    amount_in = _ceil_div_nonneg(net_in * BPS_DENOM, fee_denominator)
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")

    k_before = reserve_in * reserve_out
    # Note: With `fee_total = ceil(amount_in * fee_bps / 10_000)`, the net input is:
    #   net_in = amount_in - fee_total = floor(amount_in * (10_000 - fee_bps) / 10_000)
    # This makes `amount_in = ceil(net_in * 10_000 / (10_000 - fee_bps))` sufficient to ensure
    # net_in_actual >= net_in_required.
    fee_total = compute_fee_total(gross_in=amount_in, fee_bps=fee_bps)
    if fee_total > amount_in:
        raise ValueError("fee_total exceeds amount_in")
    net_in_actual = amount_in - fee_total
    if net_in_actual <= 0:
        raise ValueError("net_in must be positive after fees")

    denom_price = reserve_in + net_in_actual
    if denom_price <= 0:
        raise ValueError("invalid denominator")
    amount_out_quote = (reserve_out * net_in_actual) // denom_price
    if amount_out_quote < amount_out:
        raise ValueError("computed amount_in insufficient for desired amount_out")

    new_reserve_in = reserve_in + amount_in
    new_reserve_out = reserve_out - amount_out
    if new_reserve_out < 0:
        raise ValueError("amount_out exceeds reserve_out")
    k_after = new_reserve_in * new_reserve_out

    return SwapExactOutResult(
        amount_in=amount_in,
        amount_out=amount_out,
        fee_total=fee_total,
        protocol_fee=0,
        lp_fee=fee_total,
        net_in=net_in_actual,
        gross_in=amount_in,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
        k_before=k_before,
        k_after=k_after,
    )
