#!/usr/bin/env python3
"""
Generate shared fee-split test vectors from the authoritative Python runtime.

These vectors are consumed by:
  * the SPARK/Ada kernel (``fee_router.adb``) — as proof/test oracle,
  * the Rust shadow and Python reference — already covered by the differential
    suite, included here so all three runtimes share one vector set.

Each vector uses a zero dust-in (single split), matching the SPARK postcondition
``buyburn + stakers + reserve + hosts + dust = amount``.

Usage::

    python3 spark-kernels/fee_router/export_test_vectors.py --out spark-kernels/fee_router/test_vectors.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.core.fee_router import (  # noqa: E402
    BORROW,
    DEX,
    PERPS,
    REDEMPTION,
    FeeAccumulator,
    RouteAccepted,
    canonical_split_table,
    route_fee,
)

_AMOUNTS = [0, 1, 10_000, 12_347, 999_983, 1_000_000_000]
_DOMAINS = [DEX, PERPS, BORROW, REDEMPTION]


def build_vectors() -> dict:
    cases = []
    for source in _DOMAINS:
        table = canonical_split_table(source)
        for amount in _AMOUNTS:
            result = route_fee(
                source=source,
                asset="zUSD",
                amount=amount,
                split_table=table,
                accumulator=FeeAccumulator(),
            )
            assert isinstance(result, RouteAccepted), (source, amount)
            r = result.receipt
            assert amount == r.buyburn + r.stakers + r.reserve + r.hosts + r.dust
            cases.append(
                {
                    "domain": source,
                    "amount": amount,
                    "split": {
                        "buyburn_bps": table.buyburn_bps,
                        "stakers_bps": table.stakers_bps,
                        "reserve_bps": table.reserve_bps,
                        "hosts_bps": table.hosts_bps,
                    },
                    "expected": {
                        "buyburn": r.buyburn,
                        "stakers": r.stakers,
                        "reserve": r.reserve,
                        "hosts": r.hosts,
                        "dust": r.dust,
                    },
                }
            )
    return {"version": 1, "kernel": "fee_split_conservation", "cases": cases}


def serialize(vectors: dict) -> str:
    return json.dumps(vectors, sort_keys=True, indent=2) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Export shared fee-split test vectors.")
    parser.add_argument("--out", required=True, help="output JSON path")
    args = parser.parse_args(argv)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(serialize(build_vectors()), encoding="utf-8")
    print(f"wrote {len(build_vectors()['cases'])} vectors -> {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
