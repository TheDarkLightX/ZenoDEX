#!/usr/bin/env python3
"""BMSE-style bounded search over POL reinvest parameters (internal).

This is a lightweight grid search that uses the deterministic POL simulator
(`tools/tokenomics/pol_reinvest_sim.py`) to compare parameter sets and emit a
Pareto frontier across:
  - liquidity proxy: end_depth = floor(sqrt(reserve0 * reserve1))
  - protocol POL share proxy: end_protocol_lp_bps

This is an analysis tool; it does not attempt to model equilibrium volume.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from math import isqrt
from pathlib import Path
from typing import Any

# Allow `python3 tools/tokenomics/bmse_pol_reinvest_grid.py ...` from repo root.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from tools.tokenomics.pol_reinvest_sim import simulate_pol_reinvest  # noqa: E402


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


def _pareto_frontier(rows: list[dict[str, Any]], *, keys_max: tuple[str, ...]) -> list[int]:
    """Return indices of non-dominated rows for the given max-keys."""

    def dominates(a: dict[str, Any], b: dict[str, Any]) -> bool:
        ge_all = True
        gt_any = False
        for k in keys_max:
            av = int(a[k])
            bv = int(b[k])
            if av < bv:
                ge_all = False
                break
            if av > bv:
                gt_any = True
        return ge_all and gt_any

    frontier: list[int] = []
    for i, r in enumerate(rows):
        dominated = False
        for j, s in enumerate(rows):
            if i == j:
                continue
            if dominates(s, r):
                dominated = True
                break
        if not dominated:
            frontier.append(i)
    return frontier


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--initial-reserve", type=int, default=10_000)
    ap.add_argument("--epochs", type=int, default=50)
    ap.add_argument("--gross-in", type=int, default=1_000)
    ap.add_argument("--fee-bps-list", type=str, default="10,30,100")
    ap.add_argument("--protocol-fee-share-bps-list", type=str, default="0,2000,5000,10000")
    ap.add_argument("--reinvest-bps-list", type=str, default="0,2500,5000,10000")
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()

    fee_bps_list = _parse_int_list(args.fee_bps_list)
    pfs_list = _parse_int_list(args.protocol_fee_share_bps_list)
    reinvest_list = _parse_int_list(args.reinvest_bps_list)

    initial_depth = isqrt(int(args.initial_reserve) * int(args.initial_reserve))
    rows_out: list[dict[str, Any]] = []

    for fee_bps in fee_bps_list:
        for pfs in pfs_list:
            for reinvest_bps in reinvest_list:
                try:
                    rows = simulate_pol_reinvest(
                        initial_reserve=int(args.initial_reserve),
                        fee_bps=int(fee_bps),
                        protocol_fee_share_bps=int(pfs),
                        gross_in=int(args.gross_in),
                        epochs=int(args.epochs),
                        reinvest_bps=int(reinvest_bps),
                    )
                except Exception as e:  # noqa: BLE001 - BMSE wants to keep going
                    rows_out.append(
                        {
                            "status": "error",
                            "error": type(e).__name__,
                            "fee_bps": int(fee_bps),
                            "protocol_fee_share_bps": int(pfs),
                            "reinvest_bps": int(reinvest_bps),
                        }
                    )
                    continue

                end = rows[-1]
                end_depth = isqrt(int(end.reserve0) * int(end.reserve1))
                rows_out.append(
                    {
                        "status": "ok",
                        "fee_bps": int(fee_bps),
                        "protocol_fee_share_bps": int(pfs),
                        "reinvest_bps": int(reinvest_bps),
                        "end_depth": int(end_depth),
                        "depth_delta": int(end_depth - int(initial_depth)),
                        "end_protocol_lp_bps": int(end.protocol_lp_bps),
                        "end_protocol_lp": int(end.protocol_lp),
                        "end_total_lp": int(end.total_lp),
                        "protocol_fees0_total": int(sum(r.protocol_fees0 for r in rows)),
                        "protocol_fees1_total": int(sum(r.protocol_fees1 for r in rows)),
                    }
                )

    ok_rows = [r for r in rows_out if r.get("status") == "ok"]
    frontier = _pareto_frontier(ok_rows, keys_max=("end_depth", "end_protocol_lp_bps"))
    out_obj = {
        "schema": "tools/tokenomics/bmse_pol_reinvest_grid/v1",
        "params": {
            "initial_reserve": int(args.initial_reserve),
            "epochs": int(args.epochs),
            "gross_in": int(args.gross_in),
            "fee_bps_list": fee_bps_list,
            "protocol_fee_share_bps_list": pfs_list,
            "reinvest_bps_list": reinvest_list,
        },
        "rows": rows_out,
        "ok_rows": ok_rows,
        "pareto_frontier_indices_in_ok_rows": frontier,
    }

    if args.out:
        Path(str(args.out)).write_text(json.dumps(out_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        print(json.dumps(out_obj, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

