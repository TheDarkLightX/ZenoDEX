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

from tools.stateful_scenario_bridge import run_stateful_disaster_proof_obligations


def _split_csv(value: str | None) -> list[str] | None:
    if value is None:
        return None
    rows = [item.strip() for item in value.split(",") if item.strip()]
    return rows or None


def _print_text(payload: dict) -> None:
    print("Stateful Disaster Proof Obligation Closure")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"selected_obligation_count: {payload['selected_obligation_count']}")
    print(f"closed_count: {payload['closed_count']}")
    print(f"failed_count: {payload['failed_count']}")
    print(f"inconclusive_count: {payload['inconclusive_count']}")
    print(f"partial_count: {payload['partial_count']}")
    if payload.get("errors"):
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")
    for result in payload.get("obligation_results", []):
        print(f"- {result['surface_id']}: {result['closure_status']}")
        for lane in result.get("lane_results", []):
            print(f"  - {lane['kind']}:{lane['name']} {lane['status']}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run commands from a stateful disaster proof-obligation packet.")
    parser.add_argument("--packet", required=True, help="Proof-obligation packet JSON")
    parser.add_argument("--surface-id", action="append", help="Surface id to run; may be repeated")
    parser.add_argument("--surface-ids", help="Comma-separated surface ids to run")
    parser.add_argument("--lane-kind", action="append", help="Lane kind to run; may be repeated")
    parser.add_argument("--lane-kinds", help="Comma-separated lane kinds to run")
    parser.add_argument("--timeout-s", type=int, default=180)
    parser.add_argument("--output", help="Optional path to write the closure receipt JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    surface_ids = (args.surface_id or []) + (_split_csv(args.surface_ids) or [])
    lane_kinds = (args.lane_kind or []) + (_split_csv(args.lane_kinds) or [])
    payload = run_stateful_disaster_proof_obligations(
        packet=args.packet,
        surface_ids=surface_ids or None,
        lane_kinds=lane_kinds or None,
        timeout_s=int(args.timeout_s),
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
