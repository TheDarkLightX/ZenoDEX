"""Production-safe CPMM settlement swap helpers.

These helpers mirror the semantics pinned down by the bounded settlement
witness kernels:

- ``src/kernels/dex/settlement_swap_apply_witness_v1.yaml``
- ``src/kernels/dex/settlement_swap_exact_out_apply_witness_v1.yaml``

Unlike the native shell adapters for those witnesses, this module is intended
for runtime use in the functional core, so it uses the full consensus domain
bounds rather than the tiny verifier-friendly state ranges.
"""

from __future__ import annotations

from dataclasses import dataclass

from .cpmm_swap_v8 import swap_exact_in as _kernel_swap_exact_in_v8
from .cpmm_swap_v8 import swap_exact_out as _kernel_swap_exact_out_v8

BPS_DENOM = 10_000
# Keep these aligned with ``src/core/domain_limits.py`` and the authoritative
# kernel domains. This module stays self-contained to avoid a circular import
# through ``src.core.__init__``.
DEX_POOL_RESERVE_MAX = 3_000_000_000
DEX_SWAP_AMOUNT_MAX = 3_000_000_000
CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT = 200


@dataclass(frozen=True)
class SettlementSwapExactInQuote:
    amount_in: int
    amount_out: int
    fee_paid: int
    protocol_fee_paid: int
    lp_fee_paid: int
    net_in: int
    reserve_in_before: int
    reserve_out_before: int
    reserve_in_after: int
    reserve_out_after: int
    k_before: int
    k_after: int


@dataclass(frozen=True)
class SettlementSwapExactOutQuote:
    amount_in: int
    amount_out: int
    amount_out_quote: int
    overdelivery_gap: int
    gap_bps: int
    fee_paid: int
    protocol_fee_paid: int
    lp_fee_paid: int
    net_in_actual: int
    reserve_in_before: int
    reserve_out_before: int
    reserve_in_after: int
    reserve_out_after: int
    k_before: int
    k_after: int


def _gap_bps(*, overdelivery_gap: int, amount_out: int) -> int:
    return ((overdelivery_gap * BPS_DENOM) + amount_out - 1) // amount_out


def _require_int_range(
    name: str,
    value: object,
    *,
    minimum: int | None = None,
    maximum: int | None = None,
) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    value_int = value
    if minimum is not None and value_int < minimum:
        raise ValueError(f"{name} must be >= {minimum}: {value_int}")
    if maximum is not None and value_int > maximum:
        raise ValueError(f"{name} exceeds kernel domain max {maximum}: {value_int}")
    return value_int


def _validate_swap_post_reserves(*, new_reserve_in: object, new_reserve_out: object) -> None:
    if type(new_reserve_in) is not int:
        raise TypeError("new_reserve_in must be an int")
    if new_reserve_in > DEX_POOL_RESERVE_MAX:
        raise ValueError(
            f"swap would exceed reserve_in domain max {DEX_POOL_RESERVE_MAX}: "
            f"post-state {new_reserve_in}"
        )
    _require_int_range(
        "new_reserve_in",
        new_reserve_in,
        minimum=1,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    _require_int_range(
        "new_reserve_out",
        new_reserve_out,
        minimum=1,
        maximum=DEX_POOL_RESERVE_MAX,
    )


def quote_cpmm_swap_exact_in(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    protocol_fee_share_bps: int = 0,
) -> SettlementSwapExactInQuote:
    """Return a kernel-backed exact-in settlement quote plus post-state."""
    reserve_in = _require_int_range("reserve_in", reserve_in, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    reserve_out = _require_int_range("reserve_out", reserve_out, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    amount_in = _require_int_range("amount_in", amount_in, minimum=1, maximum=DEX_SWAP_AMOUNT_MAX)
    fee_bps = _require_int_range("fee_bps", fee_bps, minimum=0, maximum=BPS_DENOM)
    protocol_fee_share_bps = _require_int_range(
        "protocol_fee_share_bps",
        protocol_fee_share_bps,
        minimum=0,
        maximum=BPS_DENOM,
    )

    res = _kernel_swap_exact_in_v8(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_fee_share_bps,
    )
    _validate_swap_post_reserves(
        new_reserve_in=res.new_reserve_in,
        new_reserve_out=res.new_reserve_out,
    )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")

    return SettlementSwapExactInQuote(
        amount_in=int(amount_in),
        amount_out=int(res.amount_out),
        fee_paid=int(res.fee_total),
        protocol_fee_paid=int(res.protocol_fee),
        lp_fee_paid=int(res.lp_fee),
        net_in=int(res.net_in),
        reserve_in_before=int(reserve_in),
        reserve_out_before=int(reserve_out),
        reserve_in_after=int(res.new_reserve_in),
        reserve_out_after=int(res.new_reserve_out),
        k_before=int(res.k_before),
        k_after=int(res.k_after),
    )


def quote_cpmm_swap_exact_out(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_overdelivery_gap_bps: int = CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
    protocol_fee_share_bps: int = 0,
) -> SettlementSwapExactOutQuote:
    """Return a kernel-backed exact-out settlement quote plus post-state."""
    reserve_in = _require_int_range("reserve_in", reserve_in, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    reserve_out = _require_int_range("reserve_out", reserve_out, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    amount_out = _require_int_range("amount_out", amount_out, minimum=1, maximum=DEX_SWAP_AMOUNT_MAX)
    fee_bps = _require_int_range("fee_bps", fee_bps, minimum=0, maximum=BPS_DENOM)
    max_overdelivery_gap_bps = _require_int_range(
        "max_overdelivery_gap_bps",
        max_overdelivery_gap_bps,
        minimum=0,
        maximum=BPS_DENOM,
    )
    protocol_fee_share_bps = _require_int_range(
        "protocol_fee_share_bps",
        protocol_fee_share_bps,
        minimum=0,
        maximum=BPS_DENOM,
    )

    res = _kernel_swap_exact_out_v8(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_fee_share_bps,
    )
    _require_int_range(
        "amount_in",
        res.amount_in,
        minimum=1,
        maximum=DEX_SWAP_AMOUNT_MAX,
    )
    _validate_swap_post_reserves(
        new_reserve_in=res.new_reserve_in,
        new_reserve_out=res.new_reserve_out,
    )
    gap_bps = _gap_bps(overdelivery_gap=int(res.overdelivery_gap), amount_out=amount_out)
    if gap_bps > max_overdelivery_gap_bps:
        raise ValueError(
            f"overdelivery gap exceeds bps policy: gap_bps={gap_bps} > {max_overdelivery_gap_bps}"
        )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")

    return SettlementSwapExactOutQuote(
        amount_in=int(res.amount_in),
        amount_out=int(res.amount_out),
        amount_out_quote=int(res.amount_out_quote),
        overdelivery_gap=int(res.overdelivery_gap),
        gap_bps=int(gap_bps),
        fee_paid=int(res.fee_total),
        protocol_fee_paid=int(res.protocol_fee),
        lp_fee_paid=int(res.lp_fee),
        net_in_actual=int(res.net_in),
        reserve_in_before=int(reserve_in),
        reserve_out_before=int(reserve_out),
        reserve_in_after=int(res.new_reserve_in),
        reserve_out_after=int(res.new_reserve_out),
        k_before=int(res.k_before),
        k_after=int(res.k_after),
    )
