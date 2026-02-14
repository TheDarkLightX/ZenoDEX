"""
CPMM swap kernel (v9 semantics).

This variant is identical to v8 except for the protocol-fee rounding rule:

- v8: protocol_fee = floor(fee_total * protocol_fee_share_bps / 10_000)
- v9: protocol_fee = ceil (fee_total * protocol_fee_share_bps / 10_000)

Rationale:
  Floor rounding can create discrete security thresholds when `fee_total` is small
  (e.g. fee_total=1, share=9999 -> protocol_fee=0). Allocating rounding to the
  protocol (ceil) removes the "free protocol fee" corner, at the cost of slightly
  reducing LP fees in those edge cases.
"""

from __future__ import annotations

from . import cpmm_swap_v8 as v8


def compute_protocol_fee(*, fee_total: int, protocol_fee_share_bps: int) -> int:
    """
    Compute `protocol_fee = ceil(fee_total * protocol_fee_share_bps / 10_000)`.
    """
    v8._require_int("fee_total", fee_total)
    v8._require_int("protocol_fee_share_bps", protocol_fee_share_bps)
    if fee_total < 0:
        raise ValueError("fee_total must be non-negative")
    if not (0 <= protocol_fee_share_bps <= v8.BPS_DENOM):
        raise ValueError(f"protocol_fee_share_bps must be in [0, {v8.BPS_DENOM}]")
    return v8._ceil_div_nonneg(fee_total * protocol_fee_share_bps, v8.BPS_DENOM)


def swap_exact_in(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    protocol_fee_share_bps: int = 0,
) -> v8.SwapExactInResult:
    """
    Exact-in swap quote + post-state.

    v9 differs from v8 only in the protocol-fee rounding rule.
    """
    for name, v in (
        ("reserve_in", reserve_in),
        ("reserve_out", reserve_out),
        ("amount_in", amount_in),
        ("fee_bps", fee_bps),
        ("protocol_fee_share_bps", protocol_fee_share_bps),
    ):
        v8._require_int(name, v)

    if reserve_in < 0 or reserve_out < 0:
        raise ValueError("reserves must be non-negative")
    if reserve_in == 0 or reserve_out == 0:
        raise ValueError("cannot swap against an empty reserve")
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if not (0 <= fee_bps <= v8.BPS_DENOM):
        raise ValueError(f"fee_bps must be in [0, {v8.BPS_DENOM}]")
    if not (0 <= protocol_fee_share_bps <= v8.BPS_DENOM):
        raise ValueError(f"protocol_fee_share_bps must be in [0, {v8.BPS_DENOM}]")

    k_before = reserve_in * reserve_out

    fee_total = v8.compute_fee_total(gross_in=amount_in, fee_bps=fee_bps)
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

    return v8.SwapExactInResult(
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
) -> v8.SwapExactOutResult:
    # v8 exact-out already uses protocol_fee=0, so v9 is identical.
    return v8.swap_exact_out(reserve_in=reserve_in, reserve_out=reserve_out, amount_out=amount_out, fee_bps=fee_bps)

