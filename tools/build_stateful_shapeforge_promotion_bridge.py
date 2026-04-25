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

from tools.stateful_scenario_bridge import build_shapeforge_promotion_bridge_report


def _print_text(payload: dict) -> None:
    print("Stateful ShapeForge Promotion Bridge")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"source_campaign_report: {payload['source_campaign_report']}")
    print(f"evidence_class_ceiling: {payload['evidence_class_ceiling']}")
    print(f"candidate_count: {payload['candidate_count']}")
    print(f"blocked_count: {payload['blocked_count']}")
    shape_validation = payload.get("shape_validation", {})
    print(f"shape_validation_ran: {'yes' if shape_validation.get('ran') else 'no'}")
    if payload.get("errors"):
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build a research-only ShapeForge candidate bridge from acceptance TCB stateful fuzz artifacts."
    )
    parser.add_argument("--campaign-report", required=True)
    parser.add_argument("--target-manifest")
    parser.add_argument("--output", help="Optional path to write the bridge report JSON")
    parser.add_argument("--run-shapeforge-checks", action="store_true")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    payload = build_shapeforge_promotion_bridge_report(
        campaign_report=args.campaign_report,
        target_manifest=args.target_manifest,
        run_shapeforge_checks=bool(args.run_shapeforge_checks),
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
