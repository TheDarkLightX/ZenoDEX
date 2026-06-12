#!/usr/bin/env python3
"""Export shared burn-rail conservation vectors from the Python authority.

Common oracle for the SPARK kernel (`burn_rails.ads/.adb`), the Rust shadow
(`zenodex-runtime-core::burn_receipts`), and the Python reference
(`src/core/burn_receipts.py`). Each case is a burn (do_burn = 1) over inputs
`(supply_before, burn_amount, batch_before, burn_budget)`; the expected outputs
are the conservation results `supply_after = supply_before - burn_amount` and
`batch_after = batch_before + burn_amount`, confirmed by the Python rails.

Usage::

    python3 spark-kernels/burn_rails/export_test_vectors.py            # (re)write
    python3 spark-kernels/burn_rails/export_test_vectors.py --check     # CI guard
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

from src.core.burn_receipts import (  # noqa: E402
    _rail_amount_guard,
    _rail_batch_sum_guard,
    _rail_replay_guard,
    _rail_supply_guard,
)

_OUT = _HERE / "test_vectors.json"
MAX_AMOUNT = 0x7FFF
MAX_BATCH_AFTER = 0xFFFF

# (supply_before, burn_amount, batch_before, burn_budget)
_CASES = [
    (1, 1, 0, 1),
    (100, 1, 0, 100),
    (100, 100, 0, 100),
    (0x7FFF, 1, 0, 0x7FFF),
    (0x7FFF, 0x7FFF, 0, 0x7FFF),
    (500, 250, 250, 1000),
    (0x7FFF, 0x4000, 0x4000, 0x7FFF),  # batch_after = 0x8000, in range
    (0x7FFF, 0x7FFF, 0x7FFF, 0x7FFF),  # batch_after = 0xFFFE, near max
    (10, 3, 7, 9),
]


def _burn_accepts(supply_before, burn_amount, batch_before, burn_budget,
                  supply_after, batch_after) -> bool:
    """True iff all four Python rails accept this burn (do_burn = 1)."""
    return (
        _rail_replay_guard(do_burn=1, receipt_bound=1, nullifier_unused=1, policy_ok=1)
        and _rail_amount_guard(
            do_burn=1, burn_amount=burn_amount, receipt_amount=burn_amount, burn_budget=burn_budget
        )
        and _rail_supply_guard(
            do_burn=1, burn_amount=burn_amount, supply_before=supply_before, supply_after=supply_after
        )
        and _rail_batch_sum_guard(
            do_burn=1,
            burn_amount=burn_amount,
            batch_burn_sum_before=batch_before,
            batch_burn_sum_after=batch_after,
        )
    )


def build_vectors() -> dict:
    cases = []
    for supply_before, burn_amount, batch_before, burn_budget in _CASES:
        assert 0 < burn_amount <= supply_before <= MAX_AMOUNT
        assert burn_amount <= burn_budget <= MAX_AMOUNT
        supply_after = supply_before - burn_amount
        batch_after = batch_before + burn_amount
        assert batch_after <= MAX_BATCH_AFTER
        # Conservation oracle: confirmed by the Python authority's rails.
        assert _burn_accepts(
            supply_before, burn_amount, batch_before, burn_budget, supply_after, batch_after
        )
        # The load-bearing invariant the SPARK Post encodes.
        assert supply_before - supply_after == batch_after - batch_before == burn_amount
        cases.append(
            {
                "supply_before": supply_before,
                "burn_amount": burn_amount,
                "batch_before": batch_before,
                "burn_budget": burn_budget,
                "expected": {"supply_after": supply_after, "batch_after": batch_after},
            }
        )
    return {"version": 1, "kernel": "burn_rail_conservation", "cases": cases}


def serialize(vectors: dict) -> str:
    return json.dumps(vectors, sort_keys=True, indent=2) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Export SPARK burn-rail vectors.")
    parser.add_argument("--check", action="store_true", help="fail if file is stale")
    args = parser.parse_args(argv)

    content = serialize(build_vectors())
    if args.check:
        existing = _OUT.read_text(encoding="utf-8") if _OUT.is_file() else None
        if existing != content:
            print("stale burn-rail vectors; re-run export_test_vectors.py", file=sys.stderr)
            return 1
        return 0
    _OUT.write_text(content, encoding="utf-8")
    print(f"wrote {len(build_vectors()['cases'])} cases -> {_OUT.relative_to(_REPO)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
