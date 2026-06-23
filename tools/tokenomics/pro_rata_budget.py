"""Pro-rata budget mining analysis (internal tooling).

We study a common mining pattern:

  - In an epoch, the protocol has a reward budget B (in quote units).
  - Traders earn rewards pro-rata to their usage share.
  - Usage is measured as protocol fees paid (quote-equivalent at p0).

If total usage in the epoch is U = U_other + U_attacker then an attacker earns:

  reward = floor(B * U_attacker / U)

We then compute a bounded attacker best response under a concrete DEX kernel:

  - The attacker performs a 2-leg wash trade (quote->base->quote) under CPMM v8.
  - The attacker chooses the swap size that maximizes profit:
        profit = reward - wash_trade_cost

POL model:
  - Protocol owns `pol_share_bps` of LP.
  - Worst-case attacker owns the rest (attacker_lp_share_bps = 10_000 - pol_share_bps).

Notes:
  - This is analysis-only code.
  - All searches are bounded and deterministic.
  - Attacker best-response supports a conservative multi-cycle mode:
      repeat the same wash trade up to `max_cycles` times (linearized),
      to catch usage-share amplification attacks.
"""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass
from fractions import Fraction

from tools.tokenomics.wash_trade import (
    BPS_DENOM,
    WashTradeMetrics,
    wash_trade_metrics,
    wash_trade_usage_quote_at_p0,
)


def _require_int(name: str, v: int) -> None:
    if not isinstance(v, int) or isinstance(v, bool):
        raise TypeError(f"{name} must be an int")


def pro_rata_reward_quote(*, budget_quote: int, usage_quote: int, other_usage_quote: int) -> int:
    """Compute floor(B * usage / (other_usage + usage)).

    All inputs are treated as non-negative integers.
    """
    for name, v in (
        ("budget_quote", budget_quote),
        ("usage_quote", usage_quote),
        ("other_usage_quote", other_usage_quote),
    ):
        _require_int(name, v)

    if budget_quote < 0 or usage_quote < 0 or other_usage_quote < 0:
        raise ValueError("inputs must be non-negative")

    denom = int(other_usage_quote) + int(usage_quote)
    if denom <= 0:
        return 0
    return (int(budget_quote) * int(usage_quote)) // int(denom)


@dataclass(frozen=True)
class ProRataSybilBestResponse:
    budget_quote: int
    other_usage_quote: int
    pol_share_bps: int
    attacker_lp_share_bps: int

    found: bool
    best_trade_in_quote: int | None
    best_metrics: WashTradeMetrics | None
    best_usage_quote: int | None
    best_reward_quote: int | None
    best_cost_quote_at_p0: Fraction | None
    best_profit_quote_at_p0: Fraction | None
    best_cycles: int | None = None


def _clamp_bps(x: int) -> int:
    if x < 0:
        return 0
    if x > BPS_DENOM:
        return BPS_DENOM
    return int(x)


@dataclass(frozen=True)
class _WashTradePrecomp:
    trade_in_quote: int
    usage_quote_at_p0: int
    wallet_delta_quote: int
    delta_pool_value_quote_at_p0: int


# Small deterministic LRU cache to avoid re-running the swap kernel across many evaluations.
_PRECOMP_CACHE_MAX = 16
_PRECOMP_CACHE: "OrderedDict[tuple[int, int, int, int, int, int], list[_WashTradePrecomp]]" = OrderedDict()


def _precompute_wash_trade_grid(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    max_trade_in_quote: int,
    scan_step: int,
) -> list[_WashTradePrecomp]:
    key = (
        int(reserve_base),
        int(reserve_quote),
        int(fee_bps),
        int(protocol_fee_share_bps),
        int(max_trade_in_quote),
        int(scan_step),
    )
    if key in _PRECOMP_CACHE:
        _PRECOMP_CACHE.move_to_end(key)
        return _PRECOMP_CACHE[key]

    out: list[_WashTradePrecomp] = []
    # Compute once per trade size; later evaluations only do arithmetic.
    for t in range(1, int(max_trade_in_quote) + 1, int(scan_step)):
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

        usage = wash_trade_usage_quote_at_p0(m)
        wallet_delta_q = int(m.quote_back) - int(m.trade_in_quote)

        # Pool value deltas are measured in quote at p0 (same convention as wash_trade_cost_quote_at_p0).
        price0_e8 = int(m.price0_e8)
        value_before = int(m.reserve_quote_before) + int((int(m.reserve_base_before) * price0_e8) // 100_000_000)
        value_after = int(m.reserve_quote_after) + int((int(m.reserve_base_after) * price0_e8) // 100_000_000)
        delta_pool_value_q = int(value_after - value_before)

        out.append(
            _WashTradePrecomp(
                trade_in_quote=int(t),
                usage_quote_at_p0=int(usage),
                wallet_delta_quote=int(wallet_delta_q),
                delta_pool_value_quote_at_p0=int(delta_pool_value_q),
            )
        )

    _PRECOMP_CACHE[key] = out
    _PRECOMP_CACHE.move_to_end(key)
    while len(_PRECOMP_CACHE) > int(_PRECOMP_CACHE_MAX):
        _PRECOMP_CACHE.popitem(last=False)
    return out


def max_sybil_profit_pro_rata_budget(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    pol_share_bps: int,
    other_usage_quote: int,
    budget_quote: int,
    max_trade_in_quote: int,
    scan_step: int = 1,
    max_cycles: int = 1,
) -> ProRataSybilBestResponse:
    """Bounded attacker best response for pro-rata epoch budgets.

    We scan trade sizes in [1, max_trade_in_quote] stepping by `scan_step`.
    The returned best response is the trade that maximizes profit.
    """
    for name, v in (
        ("reserve_base", reserve_base),
        ("reserve_quote", reserve_quote),
        ("fee_bps", fee_bps),
        ("protocol_fee_share_bps", protocol_fee_share_bps),
        ("pol_share_bps", pol_share_bps),
        ("other_usage_quote", other_usage_quote),
        ("budget_quote", budget_quote),
        ("max_trade_in_quote", max_trade_in_quote),
        ("scan_step", scan_step),
        ("max_cycles", max_cycles),
    ):
        _require_int(name, v)

    if max_trade_in_quote <= 0:
        raise ValueError("max_trade_in_quote must be positive")
    if scan_step <= 0:
        raise ValueError("scan_step must be positive")
    if max_cycles <= 0:
        raise ValueError("max_cycles must be positive")
    if budget_quote < 0 or other_usage_quote < 0:
        raise ValueError("budget_quote and other_usage_quote must be non-negative")

    attacker_lp_share_bps = _clamp_bps(BPS_DENOM - int(pol_share_bps))
    lp_share_bps = int(attacker_lp_share_bps)

    best_profit: Fraction | None = None
    best_profit_num: int | None = None  # profit * 10_000
    best_t: int | None = None
    best_m: WashTradeMetrics | None = None
    best_usage: int | None = None
    best_reward: int | None = None
    best_cost: Fraction | None = None
    best_cost_num: int | None = None  # cost * 10_000
    best_cycles: int | None = None

    grid = _precompute_wash_trade_grid(
        reserve_base=int(reserve_base),
        reserve_quote=int(reserve_quote),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        max_trade_in_quote=int(max_trade_in_quote),
        scan_step=int(scan_step),
    )

    for row in grid:
        usage_per_cycle = int(row.usage_quote_at_p0)

        # Exact per-cycle cost as a fixed-denominator rational (denom=10_000):
        attacker_delta_num = int(row.wallet_delta_quote) * BPS_DENOM + lp_share_bps * int(
            row.delta_pool_value_quote_at_p0
        )
        cost_num_per_cycle = 0 if attacker_delta_num >= 0 else -int(attacker_delta_num)

        # Multi-cycle attacker model (linearized): repeat the same trade N times
        # without re-evaluating on the evolved reserves. This is conservative in
        # many practical regimes (small trades), and is a fast falsifier surface.
        #
        # If max_cycles==1, this reduces to the original single-cycle model.
        for cycles in range(1, int(max_cycles) + 1):
            usage_total = int(usage_per_cycle) * int(cycles)
            reward = pro_rata_reward_quote(
                budget_quote=int(budget_quote),
                usage_quote=int(usage_total),
                other_usage_quote=int(other_usage_quote),
            )
            cost_num = int(cost_num_per_cycle) * int(cycles)
            profit_num = int(reward) * BPS_DENOM - int(cost_num)

            if best_profit_num is None or profit_num > best_profit_num:
                best_profit_num = int(profit_num)
                best_t = int(row.trade_in_quote)
                best_cycles = int(cycles)
                best_usage = int(usage_total)
                best_reward = int(reward)
                best_cost_num = int(cost_num)

    if best_profit_num is None:
        return ProRataSybilBestResponse(
            budget_quote=int(budget_quote),
            other_usage_quote=int(other_usage_quote),
            pol_share_bps=int(pol_share_bps),
            attacker_lp_share_bps=int(attacker_lp_share_bps),
            found=False,
            best_trade_in_quote=None,
            best_metrics=None,
            best_usage_quote=None,
            best_reward_quote=None,
            best_cost_quote_at_p0=None,
            best_profit_quote_at_p0=None,
            best_cycles=None,
        )

    # Recompute full metrics for the winning trade only (debug/witness aid).
    best_m = wash_trade_metrics(
        reserve_base=int(reserve_base),
        reserve_quote=int(reserve_quote),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        trade_in_quote=int(best_t),
    )

    best_cost = Fraction(int(best_cost_num), BPS_DENOM) if best_cost_num is not None else None
    best_profit = Fraction(int(best_profit_num), BPS_DENOM)

    return ProRataSybilBestResponse(
        budget_quote=int(budget_quote),
        other_usage_quote=int(other_usage_quote),
        pol_share_bps=int(pol_share_bps),
        attacker_lp_share_bps=int(attacker_lp_share_bps),
        found=True,
        best_trade_in_quote=best_t,
        best_metrics=best_m,
        best_usage_quote=best_usage,
        best_reward_quote=best_reward,
        best_cost_quote_at_p0=best_cost,
        best_profit_quote_at_p0=best_profit,
        best_cycles=int(best_cycles) if best_cycles is not None else None,
    )


def max_safe_budget_quote_pro_rata_budget(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    pol_share_bps: int,
    other_usage_quote: int,
    max_trade_in_quote: int,
    budget_hi_quote: int,
    scan_step: int = 1,
    max_cycles: int = 1,
) -> tuple[int, ProRataSybilBestResponse, ProRataSybilBestResponse]:
    """Return (max_safe_budget_quote, at_budget0, at_budget_hi).

    Safety notion: for the bounded best response, max_profit <= 0.
    """
    _require_int("budget_hi_quote", budget_hi_quote)
    if budget_hi_quote < 0:
        raise ValueError("budget_hi_quote must be non-negative")

    at0 = max_sybil_profit_pro_rata_budget(
        reserve_base=int(reserve_base),
        reserve_quote=int(reserve_quote),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        pol_share_bps=int(pol_share_bps),
        other_usage_quote=int(other_usage_quote),
        budget_quote=0,
        max_trade_in_quote=int(max_trade_in_quote),
        scan_step=int(scan_step),
        max_cycles=int(max_cycles),
    )

    at_hi = max_sybil_profit_pro_rata_budget(
        reserve_base=int(reserve_base),
        reserve_quote=int(reserve_quote),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        pol_share_bps=int(pol_share_bps),
        other_usage_quote=int(other_usage_quote),
        budget_quote=int(budget_hi_quote),
        max_trade_in_quote=int(max_trade_in_quote),
        scan_step=int(scan_step),
        max_cycles=int(max_cycles),
    )

    def _safe(x: ProRataSybilBestResponse) -> bool:
        # If the scan found no valid wash trade, treat as safe for this bounded model.
        if not x.found or x.best_profit_quote_at_p0 is None:
            return True
        return x.best_profit_quote_at_p0 <= 0

    if _safe(at_hi):
        return int(budget_hi_quote), at0, at_hi

    lo = 0
    hi = int(budget_hi_quote)
    while lo < hi:
        mid = (lo + hi + 1) // 2  # upper mid; we want max safe
        at_mid = max_sybil_profit_pro_rata_budget(
            reserve_base=int(reserve_base),
            reserve_quote=int(reserve_quote),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(protocol_fee_share_bps),
            pol_share_bps=int(pol_share_bps),
            other_usage_quote=int(other_usage_quote),
            budget_quote=int(mid),
            max_trade_in_quote=int(max_trade_in_quote),
            scan_step=int(scan_step),
            max_cycles=int(max_cycles),
        )
        if _safe(at_mid):
            lo = mid
        else:
            hi = mid - 1

    return int(lo), at0, at_hi
