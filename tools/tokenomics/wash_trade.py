"""Wash-trade (roundtrip) cost models for tokenomics / mining design (internal tooling).

This module is intentionally deterministic and integer-first. It is used to
evaluate *attacker best responses* in bounded tokenomics searches.

Key ideas:
- We model a 2-leg wash trade on a CPMM (quote->base, then base->quote).
- We compute a usage score as protocol fees paid (converted to quote at p0).
- We compute attacker net cost under an LP-share model:
    - attacker_lp_share_bps=0    : attacker is not an LP (wallet-only loss)
    - attacker_lp_share_bps=10000: attacker owns 100% of LP (LP fees/slippage internal)

This is an analysis tool; it is not consensus-critical runtime code.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from src.kernels.python.cpmm_swap_v8 import swap_exact_in

E8 = 100_000_000
BPS_DENOM = 10_000


def _require_int(name: str, v: int) -> None:
    if not isinstance(v, int) or isinstance(v, bool):
        raise TypeError(f"{name} must be an int")


def _spot_price_e8(*, reserve_base: int, reserve_quote: int) -> int:
    if reserve_base <= 0 or reserve_quote <= 0:
        raise ValueError("empty reserves")
    # p0_e8 = floor(quote/base * 1e8)
    return (int(reserve_quote) * E8) // int(reserve_base)


@dataclass(frozen=True)
class WashTradeMetrics:
    # Inputs
    reserve_base_before: int
    reserve_quote_before: int
    trade_in_quote: int
    fee_bps: int
    protocol_fee_share_bps: int

    # Derived
    price0_e8: int

    # Leg 1 (quote -> base)
    base_out: int
    protocol_fee_leg1_quote: int
    lp_fee_leg1_quote: int
    reserve_base_after_leg1: int
    reserve_quote_after_leg1: int

    # Leg 2 (base -> quote)
    quote_back: int
    protocol_fee_leg2_base: int
    lp_fee_leg2_base: int
    reserve_base_after: int
    reserve_quote_after: int

    # Wallet-only roundtrip loss (quote units)
    roundtrip_cost_quote_non_lp: int

    # Protocol fee totals, converted into quote at p0 (integer floor)
    protocol_fee_leg2_quote_at_p0: int
    protocol_fee_total_quote_at_p0: int


def wash_trade_metrics(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    trade_in_quote: int,
) -> WashTradeMetrics:
    """Compute deterministic wash-trade metrics under CPMM v8 semantics.

    Raises ValueError on invalid inputs or if swaps are too small (0 output).
    """
    for name, v in (
        ("reserve_base", reserve_base),
        ("reserve_quote", reserve_quote),
        ("fee_bps", fee_bps),
        ("protocol_fee_share_bps", protocol_fee_share_bps),
        ("trade_in_quote", trade_in_quote),
    ):
        _require_int(name, v)

    if trade_in_quote <= 0:
        raise ValueError("trade_in_quote must be positive")
    if reserve_base <= 0 or reserve_quote <= 0:
        raise ValueError("reserves must be positive")
    if not (0 <= fee_bps <= BPS_DENOM):
        raise ValueError("fee_bps out of range")
    if not (0 <= protocol_fee_share_bps <= BPS_DENOM):
        raise ValueError("protocol_fee_share_bps out of range")

    price0_e8 = _spot_price_e8(reserve_base=reserve_base, reserve_quote=reserve_quote)

    leg1 = swap_exact_in(
        reserve_in=int(reserve_quote),
        reserve_out=int(reserve_base),
        amount_in=int(trade_in_quote),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
    )
    base_out = int(leg1.amount_out)
    q1 = int(leg1.new_reserve_in)
    b1 = int(leg1.new_reserve_out)
    pf1_quote = int(leg1.protocol_fee)
    lp1_quote = int(leg1.lp_fee)

    leg2 = swap_exact_in(
        reserve_in=int(b1),
        reserve_out=int(q1),
        amount_in=int(base_out),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
    )
    quote_back = int(leg2.amount_out)
    pf2_base = int(leg2.protocol_fee)
    lp2_base = int(leg2.lp_fee)

    # Convert base-denominated protocol fee to quote at p0 (floor).
    pf2_quote = int((pf2_base * price0_e8) // E8)

    cost_non_lp = int(trade_in_quote - quote_back)
    if cost_non_lp < 0:
        raise ValueError("negative roundtrip cost (unexpected)")

    b2 = int(leg2.new_reserve_in)
    q2 = int(leg2.new_reserve_out)

    pf_total_q = int(pf1_quote + pf2_quote)

    return WashTradeMetrics(
        reserve_base_before=int(reserve_base),
        reserve_quote_before=int(reserve_quote),
        trade_in_quote=int(trade_in_quote),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        price0_e8=int(price0_e8),
        base_out=int(base_out),
        protocol_fee_leg1_quote=int(pf1_quote),
        lp_fee_leg1_quote=int(lp1_quote),
        reserve_base_after_leg1=int(b1),
        reserve_quote_after_leg1=int(q1),
        quote_back=int(quote_back),
        protocol_fee_leg2_base=int(pf2_base),
        lp_fee_leg2_base=int(lp2_base),
        reserve_base_after=int(b2),
        reserve_quote_after=int(q2),
        roundtrip_cost_quote_non_lp=int(cost_non_lp),
        protocol_fee_leg2_quote_at_p0=int(pf2_quote),
        protocol_fee_total_quote_at_p0=int(pf_total_q),
    )


def wash_trade_usage_quote_at_p0(m: WashTradeMetrics) -> int:
    """Usage score candidate: total protocol fees (quote-equivalent at p0)."""
    _require_int("protocol_fee_total_quote_at_p0", m.protocol_fee_total_quote_at_p0)
    if int(m.protocol_fee_total_quote_at_p0) < 0:
        raise ValueError("negative usage (unexpected)")
    return int(m.protocol_fee_total_quote_at_p0)


def wash_trade_cost_quote_at_p0(*, m: WashTradeMetrics, attacker_lp_share_bps: int) -> Fraction:
    """Compute attacker net wash-trade cost in quote (at p0), under an LP-share model.

    Value model:
    - Wallet delta is measured in quote.
    - Pool is valued in quote using p0 (integer-e8 spot).
    - Attacker recaptures `attacker_lp_share_bps / 10_000` of pool value changes.

    Returns a non-negative Fraction (0 means the wash trade is value-neutral under the model).
    """
    _require_int("attacker_lp_share_bps", attacker_lp_share_bps)
    if not (0 <= int(attacker_lp_share_bps) <= BPS_DENOM):
        raise ValueError("attacker_lp_share_bps out of range")

    # Wallet-only delta: quote_back - trade_in_quote (typically negative).
    wallet_delta_q = int(m.quote_back) - int(m.trade_in_quote)

    price0_e8 = int(m.price0_e8)
    value_before = int(m.reserve_quote_before) + int((int(m.reserve_base_before) * price0_e8) // E8)
    value_after = int(m.reserve_quote_after) + int((int(m.reserve_base_after) * price0_e8) // E8)
    delta_pool_value_q = int(value_after - value_before)

    lp_share = Fraction(int(attacker_lp_share_bps), BPS_DENOM)
    attacker_delta = Fraction(int(wallet_delta_q), 1) + lp_share * Fraction(int(delta_pool_value_q), 1)
    if attacker_delta >= 0:
        return Fraction(0, 1)
    return -attacker_delta


@dataclass(frozen=True)
class MinCostToReachUsageResult:
    min_usage_quote: int
    found: bool
    best_metrics: WashTradeMetrics | None
    best_trade_in_quote: int | None
    best_cost_quote_at_p0: Fraction | None


def min_cost_to_reach_usage_fee_gated(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    min_usage_quote: int,
    attacker_lp_share_bps: int,
    max_trade_in_quote: int,
    local_search_window: int = 32,
) -> MinCostToReachUsageResult:
    """Attacker best response: minimize wash-trade cost subject to usage >= min_usage_quote.

    The search is bounded (<= max_trade_in_quote). We binary-search the smallest
    trade that reaches the usage threshold (usage is monotone nondecreasing), then
    scan a small window above that point to smooth rounding edges.
    """
    for name, v in (
        ("reserve_base", reserve_base),
        ("reserve_quote", reserve_quote),
        ("fee_bps", fee_bps),
        ("protocol_fee_share_bps", protocol_fee_share_bps),
        ("min_usage_quote", min_usage_quote),
        ("attacker_lp_share_bps", attacker_lp_share_bps),
        ("max_trade_in_quote", max_trade_in_quote),
        ("local_search_window", local_search_window),
    ):
        _require_int(name, v)

    if min_usage_quote < 0:
        raise ValueError("min_usage_quote must be non-negative")
    if max_trade_in_quote <= 0:
        raise ValueError("max_trade_in_quote must be positive")
    if local_search_window < 0:
        raise ValueError("local_search_window must be non-negative")

    def _usage_at(trade_in_quote: int) -> int | None:
        try:
            m = wash_trade_metrics(
                reserve_base=int(reserve_base),
                reserve_quote=int(reserve_quote),
                fee_bps=int(fee_bps),
                protocol_fee_share_bps=int(protocol_fee_share_bps),
                trade_in_quote=int(trade_in_quote),
            )
        except Exception:
            return None
        return wash_trade_usage_quote_at_p0(m)

    # Quick accept: min_usage=0 => cost is minimized at smallest trade that succeeds.
    target = int(min_usage_quote)

    # First, ensure the threshold is reachable at all within the bound.
    usage_hi = _usage_at(int(max_trade_in_quote))
    if usage_hi is None or usage_hi < target:
        return MinCostToReachUsageResult(
            min_usage_quote=int(min_usage_quote),
            found=False,
            best_metrics=None,
            best_trade_in_quote=None,
            best_cost_quote_at_p0=None,
        )

    # Binary search for the smallest trade that reaches target usage.
    lo = 1
    hi = int(max_trade_in_quote)
    while lo < hi:
        mid = (lo + hi) // 2
        usage_mid = _usage_at(mid)
        # If a mid swap is invalid, treat as "too small"; move lo upward.
        if usage_mid is None or usage_mid < target:
            lo = mid + 1
        else:
            hi = mid
    t_min = int(lo)

    best_cost: Fraction | None = None
    best_m: WashTradeMetrics | None = None
    best_t: int | None = None
    for t in range(t_min, min(int(max_trade_in_quote), t_min + int(local_search_window)) + 1):
        try:
            m = wash_trade_metrics(
                reserve_base=int(reserve_base),
                reserve_quote=int(reserve_quote),
                fee_bps=int(fee_bps),
                protocol_fee_share_bps=int(protocol_fee_share_bps),
                trade_in_quote=int(t),
            )
        except Exception:
            continue
        if wash_trade_usage_quote_at_p0(m) < target:
            continue
        cost = wash_trade_cost_quote_at_p0(m=m, attacker_lp_share_bps=int(attacker_lp_share_bps))
        if best_cost is None or cost < best_cost:
            best_cost = cost
            best_m = m
            best_t = int(t)

    if best_cost is None:
        return MinCostToReachUsageResult(
            min_usage_quote=int(min_usage_quote),
            found=False,
            best_metrics=None,
            best_trade_in_quote=None,
            best_cost_quote_at_p0=None,
        )

    return MinCostToReachUsageResult(
        min_usage_quote=int(min_usage_quote),
        found=True,
        best_metrics=best_m,
        best_trade_in_quote=best_t,
        best_cost_quote_at_p0=best_cost,
    )

