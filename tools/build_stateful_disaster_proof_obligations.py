#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.stateful_scenario_bridge import build_stateful_disaster_proof_obligation_packet


def _print_text(payload: dict) -> None:
    print("Stateful Disaster Proof Obligations")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"obligation_count: {payload['obligation_count']}")
    print(f"classification_gap_count: {payload['classification_gap_count']}")
    if payload.get("errors"):
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")
    for obligation in payload.get("obligations", []):
        print(
            f"- {obligation['surface_id']} severity={obligation['severity_band']} "
            f"formal_lanes={obligation['formal_lane_count']} witnesses={len(obligation['witness_ids'])}"
        )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build proof-obligation packet from stateful disaster ratchet output.")
    parser.add_argument("--ratchet-report", required=True)
    parser.add_argument("--min-severity", choices=("low", "medium", "high", "critical"), default="high")
    parser.add_argument("--include-unknown", action="store_true")
    parser.add_argument("--allow-no-formal-lane", action="store_true")
    parser.add_argument("--output", help="Optional path to write the proof-obligation packet JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    payload = build_stateful_disaster_proof_obligation_packet(
        ratchet_report=args.ratchet_report,
        min_severity=args.min_severity,
        include_unknown=bool(args.include_unknown),
        require_formal_lane=not bool(args.allow_no_formal_lane),
    )
    if args.output:
        out = Path(args.output)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.format == "json":
        json.dump(payload, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        _print_text(payload)
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
