#!/usr/bin/env python3
"""
Export a golden trace from the authoritative Python runtime.

Golden traces are the conformance anchor for the Rust shadow runtime; see
``docs/runtime/GOLDEN_TRACE_FORMAT.md``. Output is canonical (sorted keys,
2-space indent, trailing newline) so regeneration is byte-stable.

Usage::

    python3 tools/runtime/export_golden_trace.py --out tests/runtime/golden_traces/smoke.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
for _p in (str(_REPO), str(_HERE)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import balance_kernel_lib  # noqa: E402
import burn_receipts_lib  # noqa: E402
import cpmm_settlement_lib  # noqa: E402
import golden_trace_lib  # noqa: E402
import replay_guard_lib  # noqa: E402
import zusd_kernel_lib  # noqa: E402

# scenario name -> (build_trace, replay_trace) from the owning kernel library.
_SCENARIOS = {
    "smoke": (golden_trace_lib.build_smoke_trace, golden_trace_lib.replay_trace),
    "replay_guard_smoke": (
        replay_guard_lib.build_smoke_trace,
        replay_guard_lib.replay_trace,
    ),
    "balance_smoke": (
        balance_kernel_lib.build_smoke_trace,
        balance_kernel_lib.replay_trace,
    ),
    "zusd_smoke": (
        zusd_kernel_lib.build_smoke_trace,
        zusd_kernel_lib.replay_trace,
    ),
    "burn_smoke": (
        burn_receipts_lib.build_smoke_trace,
        burn_receipts_lib.replay_trace,
    ),
    "cpmm_smoke": (
        cpmm_settlement_lib.build_smoke_trace,
        cpmm_settlement_lib.replay_trace,
    ),
}


def serialize(trace: dict) -> str:
    return json.dumps(trace, sort_keys=True, indent=2, ensure_ascii=False) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Export a ZenoDEX golden trace.")
    parser.add_argument("--out", required=True, help="output JSON path")
    parser.add_argument(
        "--scenario", default="smoke", choices=sorted(_SCENARIOS), help="trace scenario"
    )
    args = parser.parse_args(argv)

    build_trace, replay_trace = _SCENARIOS[args.scenario]
    trace = build_trace()
    # Self-check before writing: the trace must replay cleanly against the
    # runtime that produced it (guards against a half-baked exporter).
    summary = replay_trace(trace)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(serialize(trace), encoding="utf-8")

    print(
        f"wrote {args.scenario} trace -> {out_path} "
        f"({summary['steps']} steps: {summary['accepted']} accept / "
        f"{summary['rejected']} reject)"
    )
    print(f"final_state_root = {summary['final_state_root']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
