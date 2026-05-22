#!/usr/bin/env python3
"""Scan CPMM exact-in u256 overflow flags over a budgeted sample set (internal).

This is an analysis-only helper for "representation intractability detection":
it finds inputs where naive u256 arithmetic would overflow (mul/add), and
records small-ish witnesses that can be promoted into BVA scenarios or tests.

Example:
  python3 tools/uintwidth/scan_cpmm_u256.py --n 20000 --seed 0 --out internal/uintwidth/cpmm_u256_scan.json
"""

from __future__ import annotations

import argparse
import json
import os
import random
import sys

_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.core.cpmm_u256_safety import CpmmExactInU256OverflowReport, analyze_cpmm_exact_in_u256_overflows
from src.core.fixed_width import U256_MAX


def _label(r: CpmmExactInU256OverflowReport) -> str:
    flags: list[str] = []
    if r.fee_mul_overflow_naive:
        flags.append("fee_mul_overflow_naive")
    if r.fee_mul_overflow_decomposed:
        flags.append("fee_mul_overflow_decomposed")
    if r.denom_add_overflow:
        flags.append("denom_add_overflow")
    if r.numerator_mul_overflow:
        flags.append("numerator_mul_overflow")
    return "|".join(flags) if flags else "ok"


def _pick_special(rng: random.Random) -> int:
    specials = [
        0,
        1,
        2,
        (1 << 64) - 1,
        1 << 64,
        (1 << 128) - 1,
        1 << 128,
        (1 << 128) + 1,
        U256_MAX - 1,
        U256_MAX,
    ]
    return int(rng.choice(specials))


def _pick_u256(rng: random.Random, *, p_special: float, max_hint: int | None) -> int:
    if rng.random() < float(p_special):
        return _pick_special(rng)
    if max_hint is not None:
        return int(rng.randrange(0, int(max_hint) + 1))
    # Bit-length-uniform-ish sample for u256:
    bits = rng.randrange(0, 257)
    if bits == 0:
        return 0
    lo = 1 << (bits - 1)
    hi = min(U256_MAX, (1 << bits) - 1)
    return int(rng.randrange(int(lo), int(hi) + 1))


def _pick_fee_bps(rng: random.Random) -> int:
    specials = [0, 1, 30, 100, 300, 1000, 10_000]
    if rng.random() < 0.30:
        return int(rng.choice(specials))
    return int(rng.randrange(0, 10_001))


def _witness_key(reserve_in: int, reserve_out: int, amount_in: int, fee_bps: int) -> tuple[int, int, int, int]:
    # Prefer smaller witnesses when possible. This is a heuristic key only.
    m = max(int(reserve_in), int(reserve_out), int(amount_in))
    s = int(reserve_in) + int(reserve_out) + int(amount_in)
    return (int(m), int(s), int(fee_bps), int(amount_in))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20_000, help="Number of sampled cases.")
    ap.add_argument("--seed", type=int, default=0, help="RNG seed (deterministic).")
    ap.add_argument("--p-special", type=float, default=0.35, help="Probability of choosing a special boundary value.")
    ap.add_argument(
        "--max-hint",
        type=int,
        default=None,
        help="If set, sample reserves/amounts uniformly in [0..max_hint] instead of bit-length sampling.",
    )
    ap.add_argument("--out", type=str, default=None, help="Optional JSON output path (recommended under internal/).")
    args = ap.parse_args()

    if args.n <= 0:
        raise SystemExit("--n must be positive")
    if not (0.0 <= float(args.p_special) <= 1.0):
        raise SystemExit("--p-special must be in [0,1]")
    if args.max_hint is not None and args.max_hint < 0:
        raise SystemExit("--max-hint must be non-negative")

    rng = random.Random(int(args.seed))

    counts: dict[str, int] = {}
    best_witness: dict[str, dict[str, int]] = {}

    for _ in range(int(args.n)):
        rin = _pick_u256(rng, p_special=float(args.p_special), max_hint=args.max_hint)
        rout = _pick_u256(rng, p_special=float(args.p_special), max_hint=args.max_hint)
        ain = _pick_u256(rng, p_special=float(args.p_special), max_hint=args.max_hint)
        fee = _pick_fee_bps(rng)

        rep = analyze_cpmm_exact_in_u256_overflows(reserve_in=rin, reserve_out=rout, amount_in=ain, fee_bps=fee)
        lab = _label(rep)
        counts[lab] = int(counts.get(lab, 0) + 1)

        if lab == "ok":
            continue

        w = {"reserve_in": int(rin), "reserve_out": int(rout), "amount_in": int(ain), "fee_bps": int(fee)}
        prev = best_witness.get(lab)
        if prev is None or _witness_key(**w) < _witness_key(**prev):
            best_witness[lab] = w

    result = {
        "schema": "zenodex/uintwidth-scan/v1",
        "n": int(args.n),
        "seed": int(args.seed),
        "p_special": float(args.p_special),
        "max_hint": int(args.max_hint) if args.max_hint is not None else None,
        "counts": dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))),
        "best_witness": best_witness,
    }

    if args.out:
        out_path = str(args.out)
        os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(result, f, sort_keys=True, indent=2)
            f.write("\n")
    else:
        print(json.dumps(result, sort_keys=True, indent=2))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
