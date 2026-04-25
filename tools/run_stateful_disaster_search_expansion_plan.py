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

from tools.stateful_scenario_bridge import run_disaster_search_expansion_plan


def _print_text(payload: dict) -> None:
    print("Stateful Disaster Search Expansion Receipt")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"selected_axis_count: {payload['selected_axis_count']}")
    print(f"unreachable_count: {payload['unreachable_count']}")
    print(f"failed_count: {payload['failed_count']}")
    print(f"inconclusive_count: {payload['inconclusive_count']}")
    if payload.get("errors"):
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")
    for axis in payload.get("axis_results", []):
        print(f"- {axis['axis_id']}: {axis['status']}")
        for result in axis.get("command_results", []):
            print(f"  - {' '.join(result.get('command') or [])}: {result['status']}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run stateful disaster search expansion axes.")
    parser.add_argument("--plan", help="Optional expansion-plan JSON. If omitted, build the current default plan.")
    parser.add_argument("--axis-id", action="append", help="Axis id to run; may be repeated")
    parser.add_argument("--timeout-s", type=int, default=240)
    parser.add_argument("--output", help="Optional path to write the receipt JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    payload = run_disaster_search_expansion_plan(
        plan=args.plan,
        axis_ids=args.axis_id,
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
