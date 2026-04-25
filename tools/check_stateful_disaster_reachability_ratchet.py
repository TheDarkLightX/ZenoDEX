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

from tools.stateful_scenario_bridge import (
    build_disaster_reachability_ratchet_report,
    build_shapeforge_promotion_bridge_report,
)


def _print_text(payload: dict) -> None:
    print("Stateful Disaster Reachability Ratchet")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"candidate_count: {payload['candidate_count']}")
    print(f"blocked_count: {payload['blocked_count']}")
    print(f"risk_counts: {json.dumps(payload['risk_counts'], sort_keys=True)}")
    if payload.get("errors"):
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")
    if payload.get("warnings"):
        print("warnings:")
        for warning in payload["warnings"]:
            print(f"- {warning}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Fail-closed ratchet for stateful disaster-state reachability artifacts.")
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--bridge-report", help="Existing stateful ShapeForge promotion bridge report")
    source.add_argument("--campaign-report", help="Acceptance TCB campaign report to bridge before checking")
    parser.add_argument("--target-manifest")
    parser.add_argument("--run-shapeforge-checks", action="store_true")
    parser.add_argument("--require-shape-validation", action="store_true")
    parser.add_argument("--max-blocked-surfaces", type=int, default=0)
    parser.add_argument("--allow-reached-no-witness", action="store_true")
    parser.add_argument("--require-guard-attribution", action="store_true")
    parser.add_argument("--high-severity-requires-witness", choices=("low", "medium", "high", "critical"), default="high")
    parser.add_argument("--output", help="Optional path to write the ratchet report JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    if args.campaign_report:
        bridge = build_shapeforge_promotion_bridge_report(
            campaign_report=args.campaign_report,
            target_manifest=args.target_manifest,
            run_shapeforge_checks=bool(args.run_shapeforge_checks),
        )
    else:
        bridge = args.bridge_report

    payload = build_disaster_reachability_ratchet_report(
        bridge_report=bridge,
        require_shape_validation=bool(args.require_shape_validation),
        max_blocked_surfaces=int(args.max_blocked_surfaces),
        require_witnesses=not bool(args.allow_reached_no_witness),
        require_guard_attribution=bool(args.require_guard_attribution),
        high_severity_requires_witness=args.high_severity_requires_witness,
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
