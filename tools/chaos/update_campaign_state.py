#!/usr/bin/env python3
"""Build regret-aware campaign state from chaos experiment journals."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from tools.chaos.regret_scheduler import (
    ChaosCampaignConfigError,
    build_campaign_state,
    write_json_artifact,
)


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_RUNS_ROOT = ROOT / "runs" / "chaos"
DEFAULT_EXPERIMENTS_DIR = ROOT / "tools" / "chaos" / "experiments"


def main() -> int:
    parser = argparse.ArgumentParser(description="Build chaos campaign/regret artifacts")
    parser.add_argument("--runs-root", type=Path, default=DEFAULT_RUNS_ROOT, help="Chaos runs root directory")
    parser.add_argument(
        "--experiments-dir",
        type=Path,
        default=DEFAULT_EXPERIMENTS_DIR,
        help="Experiment metadata directory",
    )
    parser.add_argument("--context-key", type=str, default="", help="Current context key (default: git:unknown)")
    parser.add_argument(
        "--max-blast-radius",
        type=float,
        default=None,
        help="Only consider experiments with blast radius <= threshold",
    )
    parser.add_argument(
        "--campaign-state-out",
        type=Path,
        default=DEFAULT_RUNS_ROOT / "campaign_state.json",
        help="Output path for campaign state artifact",
    )
    parser.add_argument(
        "--regret-out",
        type=Path,
        default=DEFAULT_RUNS_ROOT / "regret_snapshot.json",
        help="Output path for regret snapshot artifact",
    )
    parser.add_argument("--json", action="store_true", help="Print artifacts as JSON to stdout")
    args = parser.parse_args()

    try:
        campaign_state, regret_snapshot = build_campaign_state(
            runs_root=args.runs_root,
            experiments_dir=args.experiments_dir,
            context_key=args.context_key or None,
            max_blast_radius=args.max_blast_radius,
        )
    except ChaosCampaignConfigError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    args.campaign_state_out.parent.mkdir(parents=True, exist_ok=True)
    args.regret_out.parent.mkdir(parents=True, exist_ok=True)
    write_json_artifact(args.campaign_state_out, campaign_state)
    write_json_artifact(args.regret_out, regret_snapshot)

    if args.json:
        print(
            json.dumps(
                {
                    "campaign_state": campaign_state,
                    "regret_snapshot": regret_snapshot,
                },
                indent=2,
                sort_keys=True,
            )
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
