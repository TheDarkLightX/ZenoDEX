#!/usr/bin/env python3
"""Compute a safe per-identity reward envelope under fee-gated eligibility (internal).

Given:
- pool reserves (base/quote)
- fee parameters (fee_bps, protocol_fee_share_bps)
- attacker LP internalization share (attacker_lp_share_bps)

We compute, for each usage threshold U in a list:
- attacker best-response minimal cost to reach usage >= U
- safe per-identity reward maximum (integer) such that reward <= cost (profit <= 0)

This tool is intended for mechanism calibration and for generating boundary cases.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from fractions import Fraction
from pathlib import Path

# Allow running as `python3 tools/tokenomics/safe_reward_envelope.py ...` from repo root.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from tools.tokenomics.wash_trade import min_cost_to_reach_usage_fee_gated  # noqa: E402


def _parse_int_list(s: str) -> list[int]:
    out: list[int] = []
    for part in str(s).split(","):
        part = part.strip()
        if not part:
            continue
        out.append(int(part))
    if not out:
        raise ValueError("empty list")
    return out


def _fstr(x: Fraction | None) -> str | None:
    if x is None:
        return None
    return f"{int(x.numerator)}/{int(x.denominator)}"


def _floor_fraction(x: Fraction) -> int:
    return int(x.numerator // x.denominator)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--reserve-base", type=int, default=10_000)
    ap.add_argument("--reserve-quote", type=int, default=10_000)
    ap.add_argument("--fee-bps", type=int, default=30)
    ap.add_argument("--protocol-fee-share-bps", type=int, default=10_000)
    ap.add_argument("--attacker-lp-share-bps", type=int, default=10_000)
    ap.add_argument("--max-trade-in-quote", type=int, default=20_000)
    ap.add_argument("--min-usage-list", type=str, default="0,1,2,5,10,20")
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()

    usage_list = _parse_int_list(args.min_usage_list)

    rows = []
    for u in usage_list:
        r = min_cost_to_reach_usage_fee_gated(
            reserve_base=int(args.reserve_base),
            reserve_quote=int(args.reserve_quote),
            fee_bps=int(args.fee_bps),
            protocol_fee_share_bps=int(args.protocol_fee_share_bps),
            min_usage_quote=int(u),
            attacker_lp_share_bps=int(args.attacker_lp_share_bps),
            max_trade_in_quote=int(args.max_trade_in_quote),
            local_search_window=64,
        )
        safe_reward = None
        cost_str = None
        if r.found and r.best_cost_quote_at_p0 is not None:
            safe_reward = _floor_fraction(r.best_cost_quote_at_p0)
            cost_str = _fstr(r.best_cost_quote_at_p0)
        rows.append(
            {
                "min_usage_quote": int(u),
                "found": bool(r.found),
                "best_trade_in_quote": r.best_trade_in_quote,
                "cost_quote_at_p0": cost_str,
                "safe_base_reward_max_int": safe_reward,
            }
        )

    out_obj = {
        "schema": "tools/tokenomics/safe_reward_envelope/v1",
        "params": {
            "reserve_base": int(args.reserve_base),
            "reserve_quote": int(args.reserve_quote),
            "fee_bps": int(args.fee_bps),
            "protocol_fee_share_bps": int(args.protocol_fee_share_bps),
            "attacker_lp_share_bps": int(args.attacker_lp_share_bps),
            "max_trade_in_quote": int(args.max_trade_in_quote),
            "min_usage_list": usage_list,
        },
        "rows": rows,
    }

    if args.out:
        Path(str(args.out)).write_text(json.dumps(out_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        print(json.dumps(out_obj, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

