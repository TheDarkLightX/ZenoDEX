#!/usr/bin/env python3
"""Protocol-Owned Liquidity (POL) reinvestment simulator (internal).

Goal: explore how protocol fee share + reinvest fraction compounds into POL and
pool depth under a simple CPMM model.

This is an *analysis* tool. It is intentionally explicit and bounded; it does
not attempt to model full market equilibrium or price discovery.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import dataclass
from math import isqrt
from pathlib import Path

# Allow `python3 tools/tokenomics/pol_reinvest_sim.py ...` from repo root without `PYTHONPATH=.`.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.kernels.python.cpmm_swap_v8 import swap_exact_in as swap_exact_in_v8


def _require_int(name: str, v: int) -> int:
    if not isinstance(v, int) or isinstance(v, bool):
        raise TypeError(f"{name} must be an int")
    return int(v)


def _clamp_int(v: int, lo: int, hi: int) -> int:
    if v < lo:
        return int(lo)
    if v > hi:
        return int(hi)
    return int(v)


def _lp_mint_uniswap_style(*, reserve0: int, reserve1: int, amount0: int, amount1: int, lp_supply: int) -> int:
    """LP mint formula for subsequent deposits (ignores MIN_LP_LOCK for analysis)."""
    if reserve0 <= 0 or reserve1 <= 0:
        raise ValueError("reserves must be positive")
    # Allow a "no-op" deposit (amounts=0) so POL reinvest can naturally stall
    # when protocol fees are too small in the current bounded regime.
    if amount0 <= 0 or amount1 <= 0:
        return 0
    if lp_supply <= 0:
        raise ValueError("lp_supply must be positive")
    return min((amount0 * lp_supply) // reserve0, (amount1 * lp_supply) // reserve1)


@dataclass(frozen=True)
class EpochRow:
    epoch: int
    reserve0: int
    reserve1: int
    total_lp: int
    protocol_lp: int
    protocol_lp_bps: int
    protocol_inventory0: int
    protocol_inventory1: int
    protocol_fees0: int
    protocol_fees1: int
    pairable_protocol_fees: int
    reinvest0: int
    reinvest1: int
    lp_minted: int
    swap_out_0_to_1: int
    swap_out_1_to_0: int


def simulate_pol_reinvest(
    *,
    initial_reserve: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    gross_in: int,
    epochs: int,
    reinvest_bps: int,
    initial_protocol_lp_bps: int = 0,
) -> list[EpochRow]:
    # Start symmetric on the "symmetric-reserve manifold": r0=r1.
    r0 = _require_int("initial_reserve", initial_reserve)
    r1 = int(r0)
    if r0 <= 0:
        raise ValueError("initial_reserve must be positive")

    fee_bps = _require_int("fee_bps", fee_bps)
    protocol_fee_share_bps = _require_int("protocol_fee_share_bps", protocol_fee_share_bps)
    gross_in = _require_int("gross_in", gross_in)
    epochs = _require_int("epochs", epochs)
    reinvest_bps = _require_int("reinvest_bps", reinvest_bps)
    initial_protocol_lp_bps = _require_int("initial_protocol_lp_bps", initial_protocol_lp_bps)

    if not (0 <= fee_bps <= 10_000):
        raise ValueError("fee_bps out of range")
    if not (0 <= protocol_fee_share_bps <= 10_000):
        raise ValueError("protocol_fee_share_bps out of range")
    if not (0 <= reinvest_bps <= 10_000):
        raise ValueError("reinvest_bps out of range")
    if gross_in <= 0:
        raise ValueError("gross_in must be positive")
    if epochs <= 0:
        raise ValueError("epochs must be positive")
    if not (0 <= initial_protocol_lp_bps <= 10_000):
        raise ValueError("initial_protocol_lp_bps out of range")

    # Analysis-only LP supply proxy: total_lp := floor(sqrt(k)).
    # This matches Uniswap-v2 proportionality on the symmetric manifold.
    total_lp = isqrt(r0 * r1)
    if total_lp <= 0:
        raise ValueError("invalid initial total_lp")
    protocol_lp = (total_lp * int(initial_protocol_lp_bps)) // 10_000
    inv0 = 0
    inv1 = 0

    rows: list[EpochRow] = []
    for e in range(int(epochs)):
        # Two symmetric trades per epoch: 0->1 then 1->0.
        t01 = swap_exact_in_v8(
            reserve_in=int(r0),
            reserve_out=int(r1),
            amount_in=int(gross_in),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(protocol_fee_share_bps),
        )
        r0 = int(t01.new_reserve_in)
        r1 = int(t01.new_reserve_out)
        proto0 = int(t01.protocol_fee)
        inv0 += int(proto0)

        t10 = swap_exact_in_v8(
            reserve_in=int(r1),
            reserve_out=int(r0),
            amount_in=int(gross_in),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(protocol_fee_share_bps),
        )
        # Careful: swap updates are in the swapped coordinate system.
        r1 = int(t10.new_reserve_in)
        r0 = int(t10.new_reserve_out)
        proto1 = int(t10.protocol_fee)
        inv1 += int(proto1)

        # Reinvest: to add liquidity we need both assets, so we only reinvest the
        # min(inventory0, inventory1) (balanced fees). Keep the remainder as inventory.
        pairable = min(int(inv0), int(inv1))
        reinvest_pairable = (int(pairable) * int(reinvest_bps)) // 10_000
        reinvest0 = int(reinvest_pairable)
        reinvest1 = int(reinvest_pairable)
        inv0 -= int(reinvest0)
        inv1 -= int(reinvest1)

        # Mint LP to protocol for reinvested liquidity (proportional share).
        minted = _lp_mint_uniswap_style(
            reserve0=int(r0),
            reserve1=int(r1),
            amount0=int(reinvest0),
            amount1=int(reinvest1),
            lp_supply=int(total_lp),
        )
        if minted < 0:
            raise RuntimeError("lp minted negative")

        r0 += int(reinvest0)
        r1 += int(reinvest1)
        protocol_lp += int(minted)
        total_lp += int(minted)

        protocol_lp_bps = 0
        if total_lp > 0:
            protocol_lp_bps = _clamp_int((protocol_lp * 10_000) // total_lp, 0, 10_000)

        rows.append(
            EpochRow(
                epoch=int(e),
                reserve0=int(r0),
                reserve1=int(r1),
                total_lp=int(total_lp),
                protocol_lp=int(protocol_lp),
                protocol_lp_bps=int(protocol_lp_bps),
                protocol_inventory0=int(inv0),
                protocol_inventory1=int(inv1),
                protocol_fees0=int(proto0),
                protocol_fees1=int(proto1),
                pairable_protocol_fees=int(pairable),
                reinvest0=int(reinvest0),
                reinvest1=int(reinvest1),
                lp_minted=int(minted),
                swap_out_0_to_1=int(t01.amount_out),
                swap_out_1_to_0=int(t10.amount_out),
            )
        )

    return rows


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--initial-reserve", type=int, default=1_000_000, help="Initial symmetric reserve per asset.")
    ap.add_argument("--fee-bps", type=int, default=30, help="Swap fee in bps.")
    ap.add_argument("--protocol-fee-share-bps", type=int, default=2_000, help="Protocol share of swap fees in bps.")
    ap.add_argument("--gross-in", type=int, default=10_000, help="Gross input amount per trade (two trades per epoch).")
    ap.add_argument("--epochs", type=int, default=50, help="Number of epochs to simulate.")
    ap.add_argument("--reinvest-bps", type=int, default=10_000, help="Fraction of pairable protocol fees reinvested.")
    ap.add_argument(
        "--initial-protocol-lp-bps",
        type=int,
        default=0,
        help="Initial protocol-owned share of LP supply, in bps (analysis-only).",
    )
    ap.add_argument("--out", type=str, default="", help="Optional path to write JSON report.")
    args = ap.parse_args()

    rows = simulate_pol_reinvest(
        initial_reserve=int(args.initial_reserve),
        fee_bps=int(args.fee_bps),
        protocol_fee_share_bps=int(args.protocol_fee_share_bps),
        gross_in=int(args.gross_in),
        epochs=int(args.epochs),
        reinvest_bps=int(args.reinvest_bps),
        initial_protocol_lp_bps=int(args.initial_protocol_lp_bps),
    )

    out_obj = {
        "params": {
            "initial_reserve": int(args.initial_reserve),
            "fee_bps": int(args.fee_bps),
            "protocol_fee_share_bps": int(args.protocol_fee_share_bps),
            "gross_in": int(args.gross_in),
            "epochs": int(args.epochs),
            "reinvest_bps": int(args.reinvest_bps),
            "initial_protocol_lp_bps": int(args.initial_protocol_lp_bps),
        },
        "summary": {},
        "rows": [r.__dict__ for r in rows],
    }

    end = rows[-1]
    out_obj["summary"] = {
        "initial_depth": int(isqrt(int(args.initial_reserve) * int(args.initial_reserve))),
        "end_depth": int(isqrt(int(end.reserve0) * int(end.reserve1))),
        "initial_protocol_lp_bps": int(args.initial_protocol_lp_bps),
        "end_protocol_lp_bps": int(end.protocol_lp_bps),
        "protocol_fees0_total": int(sum(r.protocol_fees0 for r in rows)),
        "protocol_fees1_total": int(sum(r.protocol_fees1 for r in rows)),
        "lp_minted_total": int(sum(r.lp_minted for r in rows)),
        "reinvest0_total": int(sum(r.reinvest0 for r in rows)),
        "reinvest1_total": int(sum(r.reinvest1 for r in rows)),
        "final_inventory0": int(end.protocol_inventory0),
        "final_inventory1": int(end.protocol_inventory1),
    }

    if args.out:
        Path(str(args.out)).write_text(json.dumps(out_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        # Print a concise tail summary.
        last = rows[-1]
        print(json.dumps({"summary": out_obj["summary"], "last": last.__dict__}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
