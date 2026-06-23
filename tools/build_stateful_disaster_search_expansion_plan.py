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

from tools.stateful_scenario_bridge import build_disaster_search_expansion_plan


def _print_text(payload: dict) -> None:
    print("Stateful Disaster Search Expansion Plan")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"axis_count: {payload['axis_count']}")
    print(f"readme_exhaustive_claim: {payload['policy']['readme_exhaustive_claim']}")
    if payload.get("errors"):
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")
    for axis in payload.get("axes", []):
        print(f"- {axis['axis_id']} priority={axis['priority_score']}: {axis['what_if']}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build next what-if axes for stateful disaster-state search.")
    parser.add_argument("--axis-id", action="append", help="Axis id to include; may be repeated")
    parser.add_argument("--target-manifest")
    parser.add_argument("--output", help="Optional path to write the expansion plan JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    payload = build_disaster_search_expansion_plan(
        axis_ids=args.axis_id,
        target_manifest=args.target_manifest,
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
