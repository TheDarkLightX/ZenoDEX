#!/usr/bin/env python3
"""Run the advisory-only tabular Q-learning sandbox for ZenoDEX auto-trader research."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.autotrader_q_learning_sandbox import (  # noqa: E402
    AUTOTRADER_TABULAR_Q_COMPARE_SCHEMA,
    AUTOTRADER_TABULAR_Q_SCHEMA,
    AutoTraderQLConfig,
    AutoTraderQLRewardProfile,
    compare_autotrader_q_reward_profiles,
    train_autotrader_q_table,
)


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--episodes", type=int, default=48, help="Training episodes over the full bounded state set")
    ap.add_argument("--alpha", type=float, default=0.30, help="Q-learning alpha")
    ap.add_argument("--gamma", type=float, default=0.90, help="Q-learning gamma")
    ap.add_argument("--epsilon", type=float, default=0.15, help="Exploration epsilon")
    ap.add_argument("--seed", type=int, default=7, help="Deterministic RNG seed")
    ap.add_argument(
        "--reward-profile",
        choices=[profile.value for profile in AutoTraderQLRewardProfile],
        default=AutoTraderQLRewardProfile.BALANCED.value,
        help="Reward posture for the advisory sandbox",
    )
    ap.add_argument(
        "--compare-reward-profiles",
        action="store_true",
        help="Emit one advisory comparison payload across all reward profiles",
    )
    ap.add_argument(
        "--baseline-profile",
        choices=[profile.value for profile in AutoTraderQLRewardProfile],
        default=AutoTraderQLRewardProfile.BALANCED.value,
        help="Baseline profile for pairwise deltas when comparing profiles",
    )
    ap.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    ap.add_argument(
        "--summary-out",
        help="Optional output path for the emitted advisory summary JSON",
    )
    ap.add_argument(
        "--include-q-table",
        action="store_true",
        help="Include the full learned Q-table in stdout JSON",
    )
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        config = AutoTraderQLConfig(
            episodes=args.episodes,
            alpha=args.alpha,
            gamma=args.gamma,
            epsilon=args.epsilon,
            seed=args.seed,
            reward_profile=AutoTraderQLRewardProfile(args.reward_profile),
        )
        if args.compare_reward_profiles:
            comparison = compare_autotrader_q_reward_profiles(
                config,
                baseline_profile=AutoTraderQLRewardProfile(args.baseline_profile),
            )
            payload = comparison.to_dict()
        else:
            result = train_autotrader_q_table(config)
            payload = result.to_dict(include_q_table=bool(args.include_q_table))
        text = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
        sys.stdout.write(text)
        if args.summary_out:
            out = Path(args.summary_out).expanduser().resolve()
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text, encoding="utf-8")
        return 0
    except Exception as exc:
        payload = {
            "schema": AUTOTRADER_TABULAR_Q_COMPARE_SCHEMA if args.compare_reward_profiles else AUTOTRADER_TABULAR_Q_SCHEMA,
            "ok": False,
            "advisory_only": True,
            "error": f"{type(exc).__name__}: {exc}",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
