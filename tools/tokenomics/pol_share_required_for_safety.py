#!/usr/bin/env python3
"""Compute minimal POL share needed to make a fee-gated per-identity reward non-profitable (internal).

This is a calibration helper for token distribution / mining designs.

Model:
- Eligibility: usage_score >= min_usage_quote, where usage_score is protocol fees paid
  (quote-equivalent at p0) by a deterministic 2-leg wash trade (quote->base->quote)
  under CPMM v8 semantics.
- Reward: fixed per-identity reward in quote units: base_reward_per_identity_quote.
- POL: protocol holds pol_share_bps of LP; worst-case attacker holds the rest:
    attacker_lp_share_bps = 10000 - pol_share_bps
- Attacker best response: choose the minimum-cost wash trade within bounds.

We find the minimal pol_share_bps such that:
  cost_per_identity_quote_at_p0 >= base_reward_per_identity_quote
where cost is computed under attacker_lp_share_bps as above.

Notes:
- This is analysis-only.
- If no pol_share in [0, 9999] suffices under the bounded search, we return "impossible".
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

# Allow running as `python3 tools/tokenomics/pol_share_required_for_safety.py ...` from repo root.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from tools.tokenomics.wash_trade import min_cost_to_reach_usage_fee_gated  # noqa: E402


def _fstr(x: Fraction | None) -> str | None:
    if x is None:
        return None
    return f"{int(x.numerator)}/{int(x.denominator)}"


@dataclass(frozen=True)
class SafetyAtPOL:
    pol_share_bps: int
    attacker_lp_share_bps: int
    found: bool
    best_trade_in_quote: int | None
    cost_quote_at_p0: Fraction | None

    @property
    def cost_str(self) -> str | None:
        return _fstr(self.cost_quote_at_p0)


def _cost_at_pol_share(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    min_usage_quote: int,
    pol_share_bps: int,
    max_trade_in_quote: int,
    local_search_window: int,
) -> SafetyAtPOL:
    attacker_lp_share_bps = 10_000 - int(pol_share_bps)
    if attacker_lp_share_bps < 0:
        attacker_lp_share_bps = 0
    if attacker_lp_share_bps > 10_000:
        attacker_lp_share_bps = 10_000

    res = min_cost_to_reach_usage_fee_gated(
        reserve_base=int(reserve_base),
        reserve_quote=int(reserve_quote),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        min_usage_quote=int(min_usage_quote),
        attacker_lp_share_bps=int(attacker_lp_share_bps),
        max_trade_in_quote=int(max_trade_in_quote),
        local_search_window=int(local_search_window),
    )
    return SafetyAtPOL(
        pol_share_bps=int(pol_share_bps),
        attacker_lp_share_bps=int(attacker_lp_share_bps),
        found=bool(res.found),
        best_trade_in_quote=res.best_trade_in_quote,
        cost_quote_at_p0=res.best_cost_quote_at_p0 if res.found else None,
    )


def min_pol_share_bps_for_safety(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    min_usage_quote: int,
    base_reward_per_identity_quote: int,
    max_trade_in_quote: int,
    local_search_window: int = 64,
) -> tuple[int | None, SafetyAtPOL, SafetyAtPOL]:
    """Return (min_pol_share_bps or None, at_pol0, at_pol9999)."""
    at0 = _cost_at_pol_share(
        reserve_base=reserve_base,
        reserve_quote=reserve_quote,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_fee_share_bps,
        min_usage_quote=min_usage_quote,
        pol_share_bps=0,
        max_trade_in_quote=max_trade_in_quote,
        local_search_window=local_search_window,
    )
    at_hi = _cost_at_pol_share(
        reserve_base=reserve_base,
        reserve_quote=reserve_quote,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_fee_share_bps,
        min_usage_quote=min_usage_quote,
        pol_share_bps=9_999,
        max_trade_in_quote=max_trade_in_quote,
        local_search_window=local_search_window,
    )

    reward = Fraction(int(base_reward_per_identity_quote), 1)

    def ok(x: SafetyAtPOL) -> bool:
        return bool(x.found) and x.cost_quote_at_p0 is not None and x.cost_quote_at_p0 >= reward

    if ok(at0):
        return 0, at0, at_hi
    if not ok(at_hi):
        return None, at0, at_hi

    # Binary search for minimal pol_share_bps in [1, 9999] that makes it safe.
    lo = 1
    hi = 9_999
    while lo < hi:
        mid = (lo + hi) // 2
        m = _cost_at_pol_share(
            reserve_base=reserve_base,
            reserve_quote=reserve_quote,
            fee_bps=fee_bps,
            protocol_fee_share_bps=protocol_fee_share_bps,
            min_usage_quote=min_usage_quote,
            pol_share_bps=mid,
            max_trade_in_quote=max_trade_in_quote,
            local_search_window=local_search_window,
        )
        if ok(m):
            hi = mid
        else:
            lo = mid + 1
    return int(lo), at0, at_hi


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--reserve-base", type=int, default=10_000)
    ap.add_argument("--reserve-quote", type=int, default=10_000)
    ap.add_argument("--fee-bps", type=int, default=10)
    ap.add_argument("--protocol-fee-share-bps", type=int, default=10_000)
    ap.add_argument("--min-usage-quote", type=int, default=10)
    ap.add_argument("--base-reward-quote", type=int, default=10)
    ap.add_argument("--max-trade-in-quote", type=int, default=20_000)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()

    pol_min, at0, athi = min_pol_share_bps_for_safety(
        reserve_base=int(args.reserve_base),
        reserve_quote=int(args.reserve_quote),
        fee_bps=int(args.fee_bps),
        protocol_fee_share_bps=int(args.protocol_fee_share_bps),
        min_usage_quote=int(args.min_usage_quote),
        base_reward_per_identity_quote=int(args.base_reward_quote),
        max_trade_in_quote=int(args.max_trade_in_quote),
    )

    out_obj = {
        "schema": "tools/tokenomics/pol_share_required_for_safety/v1",
        "params": {
            "reserve_base": int(args.reserve_base),
            "reserve_quote": int(args.reserve_quote),
            "fee_bps": int(args.fee_bps),
            "protocol_fee_share_bps": int(args.protocol_fee_share_bps),
            "min_usage_quote": int(args.min_usage_quote),
            "base_reward_quote": int(args.base_reward_quote),
            "max_trade_in_quote": int(args.max_trade_in_quote),
        },
        "result": {
            "min_pol_share_bps": pol_min,
            "at_pol0": {
                "found": at0.found,
                "cost_quote_at_p0": at0.cost_str,
                "best_trade_in_quote": at0.best_trade_in_quote,
            },
            "at_pol9999": {
                "found": athi.found,
                "cost_quote_at_p0": athi.cost_str,
                "best_trade_in_quote": athi.best_trade_in_quote,
            },
        },
    }

    if args.out:
        Path(str(args.out)).write_text(json.dumps(out_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        print(json.dumps(out_obj, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

