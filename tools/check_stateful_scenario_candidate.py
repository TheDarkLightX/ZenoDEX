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

from tools.stateful_scenario_bridge import DEFAULT_TARGET_MANIFEST, check_scenario_candidate


def _print_text(payload: dict) -> None:
    print("Stateful Scenario Candidate")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"scenario_id: {payload.get('scenario_id')}")
    print(f"surface_id: {payload.get('surface_id')}")
    print(f"evidence_class_ceiling: {payload.get('evidence_class_ceiling')}")
    if payload.get("matched_surface"):
        print(f"machine_family: {payload['matched_surface']['machine_family']}")
    if payload.get("errors"):
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")
    if payload.get("warnings"):
        print("warnings:")
        for warning in payload["warnings"]:
            print(f"- {warning}")
    command = payload.get("replay_plan", {}).get("command")
    if command:
        print("replay_command: " + " ".join(command))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate an LLM-proposed stateful fuzz scenario candidate.")
    parser.add_argument("candidate", help="Path to a stateful scenario candidate JSON file")
    parser.add_argument("--target-manifest", default=str(DEFAULT_TARGET_MANIFEST))
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    candidate = json.loads(Path(args.candidate).read_text(encoding="utf-8"))
    payload = check_scenario_candidate(candidate, target_manifest=args.target_manifest)
    if args.format == "json":
        json.dump(payload, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        _print_text(payload)
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
