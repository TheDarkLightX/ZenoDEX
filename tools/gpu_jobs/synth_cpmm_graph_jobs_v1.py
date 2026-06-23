#!/usr/bin/env python3
"""
Synthetic CPMM graph + job generator (internal).

Purpose:
- Create deterministic synthetic pool graphs and swap jobs for benchmarking and
  regression generation of routing/proposer/verifier pipelines.

This is NOT consensus-critical. It intentionally uses Python's PRNG for
reproducible synthetic data.
"""

from __future__ import annotations

import argparse
import json
import os
import random
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple

# Allow `python3 tools/gpu_jobs/...` from repo root without needing `-m`.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.core.amm_dispatch import swap_exact_in_for_pool  # noqa: E402
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus  # noqa: E402


def _token_id(i: int) -> str:
    # Deterministic 32-byte ids.
    body = f"{i:064x}"
    return "0x" + body[-64:]


def _pool_obj(
    *,
    pool_id: str,
    asset0: str,
    asset1: str,
    reserve0: int,
    reserve1: int,
    fee_bps: int,
) -> Dict[str, Any]:
    return {
        "pool_id": str(pool_id),
        "asset0": str(asset0),
        "asset1": str(asset1),
        "reserve0": int(reserve0),
        "reserve1": int(reserve1),
        "fee_bps": int(fee_bps),
        "curve_tag": CURVE_TAG_CPMM,
        "curve_params": "",
        "lp_supply": 0,
        "status": PoolStatus.ACTIVE.value,
        "created_at": 0,
    }


def _to_pool_state(p: Dict[str, Any]) -> PoolState:
    return PoolState(
        pool_id=str(p["pool_id"]),
        asset0=str(p["asset0"]),
        asset1=str(p["asset1"]),
        reserve0=int(p["reserve0"]),
        reserve1=int(p["reserve1"]),
        fee_bps=int(p["fee_bps"]),
        lp_supply=int(p.get("lp_supply", 0)),
        status=PoolStatus.ACTIVE,
        created_at=int(p.get("created_at", 0)),
        curve_tag=str(p.get("curve_tag", CURVE_TAG_CPMM)),
        curve_params=p.get("curve_params", ""),
    )


def _dir_reserves(p: PoolState, asset_in: str, asset_out: str) -> Tuple[int, int]:
    if asset_in == p.asset0 and asset_out == p.asset1:
        return int(p.reserve0), int(p.reserve1)
    if asset_in == p.asset1 and asset_out == p.asset0:
        return int(p.reserve1), int(p.reserve0)
    raise ValueError("bad direction")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True, help="Directory to write pools.json and jobs.jsonl.")
    ap.add_argument("--seed", type=int, default=0, help="PRNG seed for reproducibility.")
    ap.add_argument("--tokens", type=int, default=64, help="Number of distinct synthetic tokens.")
    ap.add_argument("--pools", type=int, default=256, help="Number of synthetic CPMM pools.")
    ap.add_argument("--jobs", type=int, default=512, help="Number of swap jobs to emit.")
    ap.add_argument("--reserve-min", type=int, default=100_000, help="Min reserve per pool side (inclusive).")
    ap.add_argument("--reserve-max", type=int, default=10_000_000, help="Max reserve per pool side (inclusive).")
    ap.add_argument("--fee-bps", type=int, default=30, help="Pool fee in basis points (constant for all pools).")
    ap.add_argument("--amount-min", type=int, default=1, help="Min amount_in to try for jobs (inclusive).")
    ap.add_argument("--amount-max-frac", type=int, default=100, help="Try amount_in up to reserve_in/FRAC.")
    ap.add_argument("--max-tries", type=int, default=200, help="Max resamples per job before giving up.")
    args = ap.parse_args()

    rnd = random.Random(int(args.seed))
    n_tokens = int(args.tokens)
    n_pools = int(args.pools)
    n_jobs = int(args.jobs)

    if n_tokens < 2:
        raise ValueError("--tokens must be >= 2")
    if n_pools <= 0 or n_jobs <= 0:
        raise ValueError("--pools and --jobs must be positive")
    rmin = int(args.reserve_min)
    rmax = int(args.reserve_max)
    if rmin <= 0 or rmax < rmin:
        raise ValueError("invalid reserve range")
    fee_bps = int(args.fee_bps)
    if not (0 <= fee_bps <= 10_000):
        raise ValueError("--fee-bps must be in [0,10000]")

    tokens = [_token_id(i + 1) for i in range(n_tokens)]

    pools: List[Dict[str, Any]] = []
    used_pairs = set()
    for i in range(n_pools):
        # Avoid too many duplicates (but allow if tokens are small).
        for _ in range(20):
            a, b = rnd.sample(tokens, 2)
            pair = (a, b) if a < b else (b, a)
            if pair not in used_pairs:
                used_pairs.add(pair)
                break
        else:
            a, b = rnd.sample(tokens, 2)
        reserve0 = rnd.randint(rmin, rmax)
        reserve1 = rnd.randint(rmin, rmax)
        # PoolState requires canonical asset ordering.
        asset0, asset1 = (a, b) if a < b else (b, a)
        if asset0 != a:
            reserve0, reserve1 = reserve1, reserve0
        pools.append(
            _pool_obj(
                pool_id=f"pool_{i:06d}",
                asset0=asset0,
                asset1=asset1,
                reserve0=reserve0,
                reserve1=reserve1,
                fee_bps=fee_bps,
            )
        )

    pool_states = [_to_pool_state(p) for p in pools]

    jobs_out: List[Dict[str, Any]] = []
    amount_min = int(args.amount_min)
    frac = int(args.amount_max_frac)
    if amount_min <= 0 or frac <= 0:
        raise ValueError("invalid amount parameters")

    for j in range(n_jobs):
        ok = False
        for _try in range(int(args.max_tries)):
            p = rnd.choice(pool_states)
            if rnd.random() < 0.5:
                asset_in, asset_out = p.asset0, p.asset1
            else:
                asset_in, asset_out = p.asset1, p.asset0

            rin, rout = _dir_reserves(p, asset_in, asset_out)
            upper = max(amount_min, int(rin) // frac)
            amount_in = rnd.randint(amount_min, max(amount_min, upper))
            try:
                # Validate dust rules by actually quoting exact-in.
                swap_exact_in_for_pool(p, reserve_in=rin, reserve_out=rout, amount_in=int(amount_in))
            except Exception:
                continue

            jobs_out.append({"job_id": f"job_{j:06d}", "asset_in": asset_in, "asset_out": asset_out, "amount_in": int(amount_in)})
            ok = True
            break
        if not ok:
            raise RuntimeError(f"failed to generate a valid job after {args.max_tries} tries (job={j})")

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "pools.json").write_text(json.dumps(pools, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    with (out_dir / "jobs.jsonl").open("w", encoding="utf-8") as f:
        for job in jobs_out:
            f.write(json.dumps(job, sort_keys=True) + "\n")

    sys.stdout.write(
        json.dumps(
            {
                "seed": int(args.seed),
                "tokens": int(n_tokens),
                "pools": int(n_pools),
                "jobs": int(n_jobs),
                "fee_bps": int(fee_bps),
                "reserve_min": int(rmin),
                "reserve_max": int(rmax),
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
