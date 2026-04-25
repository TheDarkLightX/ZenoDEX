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

from tools.stateful_scenario_bridge import DEFAULT_TARGET_MANIFEST, run_scenario_candidate


def _print_text(payload: dict) -> None:
    print("Stateful Scenario Candidate Runner")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"plan_only: {'yes' if payload['plan_only'] else 'no'}")
    print("command: " + " ".join(payload.get("command") or []))
    check = payload.get("candidate_check") or {}
    if check.get("errors"):
        print("candidate_errors:")
        for error in check["errors"]:
            print(f"- {error}")
    campaign = payload.get("campaign_result")
    if isinstance(campaign, dict):
        print(f"campaign_ok: {'yes' if campaign.get('ok') else 'no'}")
        if campaign.get("report_out"):
            print(f"campaign_report: {campaign['report_out']}")
    bridge = payload.get("bridge_report")
    if isinstance(bridge, dict):
        print(f"bridge_ok: {'yes' if bridge.get('ok') else 'no'}")
        print(f"bridge_candidates: {bridge.get('candidate_count')}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate and optionally execute a stateful disaster scenario candidate.")
    parser.add_argument("candidate", help="Path to a stateful scenario candidate JSON file")
    parser.add_argument("--target-manifest", default=str(DEFAULT_TARGET_MANIFEST))
    parser.add_argument("--execute", action="store_true", help="Run the generated acceptance TCB campaign command")
    parser.add_argument("--report-out")
    parser.add_argument("--campaign-root")
    parser.add_argument("--timestamp-utc")
    parser.add_argument("--run-id")
    parser.add_argument("--no-bridge", dest="build_bridge", action="store_false")
    parser.add_argument("--run-shapeforge-checks", action="store_true")
    parser.add_argument("--output", help="Optional path to write the runner receipt JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    parser.set_defaults(build_bridge=True)
    args = parser.parse_args(argv)

    candidate = json.loads(Path(args.candidate).read_text(encoding="utf-8"))
    payload = run_scenario_candidate(
        candidate=candidate,
        target_manifest=args.target_manifest,
        execute=bool(args.execute),
        report_out=args.report_out,
        campaign_root=args.campaign_root,
        timestamp_utc=args.timestamp_utc,
        run_id=args.run_id,
        build_bridge=bool(args.build_bridge),
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
