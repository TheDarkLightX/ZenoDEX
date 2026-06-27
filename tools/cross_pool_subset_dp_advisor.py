#!/usr/bin/env python3
"""CLI for the exact cross-pool subset-DP advisory comparator."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.cross_pool_subset_dp_advisor import advise_two_pool_cpmm_batch  # noqa: E402
from src.core.cross_pool_subset_dp import SubsetDPLimits, TwoPoolCPMM  # noqa: E402


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", default="-", help="Input JSON path, or '-' for stdin.")
    parser.add_argument("--max-intents", type=int, default=20)
    parser.add_argument("--max-total-input", type=int, default=100_000)
    parser.add_argument("--max-states-per-subset", type=int, default=250_000)
    parser.add_argument("--include-execution-preview", action="store_true")
    args = parser.parse_args(argv)

    payload = _read_payload(args.input_json)
    limits = SubsetDPLimits(
        max_intents=int(args.max_intents),
        max_total_input=int(args.max_total_input),
        max_states_per_subset=int(args.max_states_per_subset),
    )
    advisory = advise_two_pool_cpmm_batch(
        _pool_from_json(payload["pool0"], name="pool0"),
        _pool_from_json(payload["pool1"], name="pool1"),
        payload["intents"],
        candidate_amount_out_total=payload.get("candidate_amount_out_total"),
        limits=limits,
        include_execution_preview=bool(args.include_execution_preview),
    )
    print(json.dumps(advisory.to_dict(), sort_keys=True))
    return 0


def _read_payload(input_json: str) -> dict[str, Any]:
    if input_json == "-":
        raw = sys.stdin.read()
    else:
        raw = Path(input_json).read_text(encoding="utf-8")
    payload = json.loads(raw)
    if not isinstance(payload, dict):
        raise ValueError("input JSON must be an object")
    return payload


def _pool_from_json(value: object, *, name: str) -> TwoPoolCPMM:
    if not isinstance(value, dict):
        raise ValueError(f"{name} must be an object")
    return TwoPoolCPMM(
        x=value["x"],
        y=value["y"],
        fee_bps=value.get("fee_bps", 0),
    )


if __name__ == "__main__":
    raise SystemExit(main())
