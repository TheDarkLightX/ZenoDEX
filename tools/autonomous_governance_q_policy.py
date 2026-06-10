#!/usr/bin/env python3
"""Sample and evaluate deterministic autonomous-governance Q policies."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.autonomous_governance_q_policy import (  # noqa: E402
    commit_autonomous_governance_surface_q_policy_v1,
    evaluate_autonomous_governance_q_policy_v1,
    evaluate_autonomous_governance_surface_q_policy_v1,
    sample_autonomous_governance_q_policy_v1,
    sample_autonomous_governance_surface_q_policy_v1,
)


MAX_INPUT_BYTES = 500_000


def _sample_bundle() -> dict[str, Any]:
    policy = sample_autonomous_governance_q_policy_v1()
    return {
        "schema": "zenodex.autonomous_governance.q_policy_eval_bundle.v1",
        "policy": policy,
        "expected_policy_hash": policy["policy_hash"],
        "parameters": {
            "fee": {"current": 30, "minimum": 0, "maximum": 100, "step": 10},
            "buyback": {"current": 20, "minimum": 0, "maximum": 100, "step": 10},
            "rebate": {"current": 10, "minimum": 0, "maximum": 100, "step": 10},
            "floor": {"current": 100_000, "minimum": 0, "maximum": 1_000_000, "step": 1_000},
            "unit": {"current": 10_000, "minimum": 1, "maximum": 10_000, "step": 0},
            "tier1": {"current": 30, "minimum": 1, "maximum": 365, "step": 10},
            "tier2": {"current": 90, "minimum": 2, "maximum": 730, "step": 10},
            "weight1": {"current": 100, "minimum": 0, "maximum": 1_000, "step": 25},
            "weight2": {"current": 200, "minimum": 0, "maximum": 1_000, "step": 25},
            "weight3": {"current": 300, "minimum": 0, "maximum": 1_000, "step": 25},
        },
        "observation": {
            "observed_price_bps": 10_500,
            "target_price_bps": 10_000,
            "volatility_bps": 250,
            "divergence_bps": 10,
            "freshness_lag_epochs": 0,
            "liquidity_depth_bps": 5_000,
        },
        "current_epoch": 12,
        "proposal_epoch": 10,
        "min_delay_epochs": 1,
        "last_update_epoch": 10,
    }


def _sample_surface_bundle() -> dict[str, Any]:
    policy = sample_autonomous_governance_surface_q_policy_v1()
    return {
        "schema": "zenodex.autonomous_governance.q_surface_policy_eval_bundle.v1",
        "policy": policy,
        "expected_policy_hash": policy["policy_hash"],
        "surface_state": {
            "fee_bps": 30,
            "buyburn_bps": 6_000,
            "stakers_bps": 0,
            "reserve_bps": 2_000,
            "hosts_bps": 2_000,
            "mcr_bps": 11_000,
            "ccr_bps": 15_000,
            "staker_bps": 5_000,
            "funding_cap_bps": 120,
        },
        "observation": {
            "observed_price_bps": 10_500,
            "target_price_bps": 10_000,
            "volatility_bps": 250,
            "divergence_bps": 10,
            "freshness_lag_epochs": 0,
            "liquidity_depth_bps": 5_000,
        },
        "current_epoch": 34,
        "proposal_epoch": 10,
        "last_update_epoch": 32,
    }


def _load_json(path: Path) -> dict[str, Any]:
    if path.stat().st_size > MAX_INPUT_BYTES:
        raise ValueError(f"input_file_too_large:{path.stat().st_size}>{MAX_INPUT_BYTES}")
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("input_must_be_json_object")
    return data


def _cmd_sample(args: argparse.Namespace) -> int:
    bundle = _sample_surface_bundle() if args.surface else _sample_bundle()
    text = json.dumps(bundle, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def _cmd_evaluate(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "surface_state" in bundle:
            result = evaluate_autonomous_governance_surface_q_policy_v1(
                policy=bundle.get("policy", {}),
                surface_state=bundle.get("surface_state", {}),
                observation=bundle.get("observation", {}),
                current_epoch=bundle.get("current_epoch"),
                proposal_epoch=bundle.get("proposal_epoch"),
                last_update_epoch=bundle.get("last_update_epoch"),
                expected_policy_hash=bundle.get("expected_policy_hash"),
            )
        else:
            result = evaluate_autonomous_governance_q_policy_v1(
                policy=bundle.get("policy", {}),
                parameters=bundle.get("parameters", {}),
                observation=bundle.get("observation", {}),
                current_epoch=bundle.get("current_epoch"),
                proposal_epoch=bundle.get("proposal_epoch"),
                min_delay_epochs=bundle.get("min_delay_epochs"),
                last_update_epoch=bundle.get("last_update_epoch"),
                expected_policy_hash=bundle.get("expected_policy_hash"),
            )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"evaluate_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def _cmd_step(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
        if "surface_state" not in bundle:
            raise ValueError("step_requires_governance_surface_bundle")
        result = commit_autonomous_governance_surface_q_policy_v1(
            policy=bundle.get("policy", {}),
            surface_state=bundle.get("surface_state", {}),
            observation=bundle.get("observation", {}),
            current_epoch=bundle.get("current_epoch"),
            proposal_epoch=bundle.get("proposal_epoch"),
            last_update_epoch=bundle.get("last_update_epoch"),
            expected_policy_hash=bundle.get("expected_policy_hash"),
        )
    except Exception as exc:
        result = {
            "schema": "zenodex.autonomous_governance.q_policy_eval_error.v1",
            "ok": False,
            "status": "inconclusive",
            "errors": [f"step_failed:{exc}"],
        }
        sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return 3

    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result.get("ok") is True else 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    sample = sub.add_parser("sample", help="write a sample evaluation bundle")
    sample.add_argument("--output", help="path to write; stdout when omitted")
    sample.add_argument("--surface", action="store_true", help="sample the governance-surface bundle")
    sample.set_defaults(func=_cmd_sample)

    evaluate = sub.add_parser("evaluate", help="evaluate a policy bundle")
    evaluate.add_argument("bundle", help="path to evaluation bundle JSON")
    evaluate.set_defaults(func=_cmd_evaluate)

    step = sub.add_parser("step", help="evaluate and apply one governance-surface policy step")
    step.add_argument("bundle", help="path to surface evaluation bundle JSON")
    step.set_defaults(func=_cmd_step)

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
