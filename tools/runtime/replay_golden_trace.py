#!/usr/bin/env python3
"""
Replay a golden trace through the authoritative Python runtime.

Re-executes every ``tx`` and checks the recorded accept/reject outcome, reject
reason, ``receipt_hash`` and ``post_state_root``, plus the initial/final state
roots. Exits non-zero with a precise message on the first disagreement.

Usage::

    python3 tools/runtime/replay_golden_trace.py tests/runtime/golden_traces/smoke.json
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
import golden_trace_lib  # noqa: E402
import replay_guard_lib  # noqa: E402
import zusd_kernel_lib  # noqa: E402

# kernel -> (replay_trace, ReplayMismatch) from the owning library.
_REPLAYERS = {
    golden_trace_lib.KERNEL: (golden_trace_lib.replay_trace, golden_trace_lib.ReplayMismatch),
    replay_guard_lib.KERNEL: (replay_guard_lib.replay_trace, replay_guard_lib.ReplayMismatch),
    balance_kernel_lib.KERNEL: (
        balance_kernel_lib.replay_trace,
        balance_kernel_lib.ReplayMismatch,
    ),
    zusd_kernel_lib.KERNEL: (zusd_kernel_lib.replay_trace, zusd_kernel_lib.ReplayMismatch),
    burn_receipts_lib.KERNEL: (
        burn_receipts_lib.replay_trace,
        burn_receipts_lib.ReplayMismatch,
    ),
}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Replay a ZenoDEX golden trace.")
    parser.add_argument("trace", help="path to a golden trace JSON file")
    args = parser.parse_args(argv)

    trace_path = Path(args.trace)
    if not trace_path.is_file():
        print(f"error: trace not found: {trace_path}", file=sys.stderr)
        return 2

    trace = json.loads(trace_path.read_text(encoding="utf-8"))
    kernel = trace.get("kernel")
    if kernel not in _REPLAYERS:
        print(f"error: unknown trace kernel: {kernel!r}", file=sys.stderr)
        return 2
    replay_trace, replay_mismatch = _REPLAYERS[kernel]
    try:
        summary = replay_trace(trace)
    except replay_mismatch as exc:
        print(f"REPLAY MISMATCH: {exc}", file=sys.stderr)
        return 1

    print(
        f"OK: {trace_path} replayed cleanly "
        f"({summary['steps']} steps: {summary['accepted']} accept / "
        f"{summary['rejected']} reject)"
    )
    print(f"final_state_root = {summary['final_state_root']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
