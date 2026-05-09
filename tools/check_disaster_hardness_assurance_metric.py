#!/usr/bin/env python3
"""Compute the public disaster hardness and assurance metric."""

# ruff: noqa: E402, I001

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_disaster_proof_schema_map import build_disaster_proof_schema_map_report
from tools.macos_scout.build_witness_space_receipt import (
    build_receipt as build_macos_witness_receipt,
)
from tools.stateful_scenario_bridge import (
    CLOSED_DISASTER_SEARCH_AXIS_IDS,
    DISASTER_SEARCH_EXPANSION_AXES,
)
from tools.zenodex_oracle_devnet_disaster_harness import run_harness as run_oracle_devnet_harness

SCHEMA = "zenodex/disaster-hardness-assurance-metric/v1"
MACOS_SCOUT_SCREENED_CANDIDATES = 1_700_256
SEARCH_PRESSURE_FULL_CREDIT_CANDIDATES = 1_000_000
PRODUCTION_BLOCKER_CAP = 84.0

POST_HARDENING_FIXTURE = ROOT / "tests" / "fixtures" / "macos_scout" / "post_hardening_zero"
PRE_HARDENING_FIXTURE = ROOT / "tests" / "fixtures" / "macos_scout" / "pre_hardening_blocked"


def _ratio(numerator: int | float, denominator: int | float) -> float:
    if denominator <= 0:
        return 0.0
    return max(0.0, min(1.0, float(numerator) / float(denominator)))


def _round(value: float) -> float:
    return round(float(value), 1)


def _level(score: float) -> str:
    if score < 40:
        return "L0_NAMED_RISK_INVENTORY"
    if score < 60:
        return "L1_REPLAY_SEEDED"
    if score < 75:
        return "L2_BOUNDED_REPLAY_SUPPORTED"
    if score < 85:
        return "L3_STRONG_BOUNDED_DISASTER_HARDENING"
    if score < 95:
        return "L4_PRODUCTION_CANDIDATE_DISASTER_ASSURANCE"
    return "L5_PRODUCTION_OPERATIONAL_DISASTER_ASSURANCE"


def build_metric() -> dict[str, Any]:
    core_selected = len(CLOSED_DISASTER_SEARCH_AXIS_IDS)
    core_inventory = len(DISASTER_SEARCH_EXPANSION_AXES)

    with tempfile.TemporaryDirectory(prefix="zeno-oracle-metric-") as tmp:
        oracle_receipt = run_oracle_devnet_harness(Path(tmp))

    proof_schema_report = build_disaster_proof_schema_map_report()

    post_witness_receipt = build_macos_witness_receipt(
        [POST_HARDENING_FIXTURE],
        blocked_run_dirs=[PRE_HARDENING_FIXTURE],
        require_clean=True,
    )
    pre_witness_receipt = build_macos_witness_receipt([PRE_HARDENING_FIXTURE])

    oracle_selected = int(oracle_receipt["selected_disaster_state_count"])
    oracle_unreachable = int(oracle_receipt["unreachable_count"])
    macos_materialized = int(post_witness_receipt["materialized_witness_count"])
    macos_reachable = int(post_witness_receipt["reachable_witness_count"])
    pre_macos_reachable = int(pre_witness_receipt["reachable_witness_count"])
    proof_schema_axis_count = int(proof_schema_report["axis_count"]) if proof_schema_report["ok"] else 0

    promoted_selected = core_selected + oracle_selected + macos_materialized
    promoted_closed = core_selected + oracle_unreachable + (macos_materialized - macos_reachable)

    promoted_closure_rate = _ratio(promoted_closed, promoted_selected)
    frontier_exposure_rate = _ratio(core_selected, core_inventory)
    witness_reduction_rate = _ratio(pre_macos_reachable - macos_reachable, pre_macos_reachable)
    proof_schema_coverage_rate = _ratio(proof_schema_axis_count, core_selected)
    search_pressure_rate = _ratio(
        MACOS_SCOUT_SCREENED_CANDIDATES,
        SEARCH_PRESSURE_FULL_CREDIT_CANDIDATES,
    )

    components = {
        "promoted_closure": {
            "weight": 30.0,
            "rate": _round(promoted_closure_rate),
            "points": _round(30.0 * promoted_closure_rate),
        },
        "frontier_exposure": {
            "weight": 25.0,
            "rate": _round(frontier_exposure_rate),
            "points": _round(25.0 * frontier_exposure_rate),
        },
        "witness_reduction": {
            "weight": 20.0,
            "rate": _round(witness_reduction_rate),
            "points": _round(20.0 * witness_reduction_rate),
        },
        "proof_schema_coverage": {
            "weight": 15.0,
            "rate": _round(proof_schema_coverage_rate),
            "points": _round(15.0 * proof_schema_coverage_rate),
        },
        "search_pressure": {
            "weight": 10.0,
            "rate": _round(search_pressure_rate),
            "points": _round(10.0 * search_pressure_rate),
        },
    }
    raw_score = _round(sum(float(row["points"]) for row in components.values()))
    score = _round(min(raw_score, PRODUCTION_BLOCKER_CAP))

    errors: list[str] = []
    if oracle_receipt["ok"] is not True:
        errors.append("oracle devnet disaster harness rejected")
    if proof_schema_report["ok"] is not True:
        errors.append("disaster proof schema map rejected")
    if post_witness_receipt["ok"] is not True:
        errors.append("macOS post-hardening witness fixture rejected")
    if pre_witness_receipt["reachable_witness_count"] <= 0:
        errors.append("macOS pre-hardening fixture no longer demonstrates reachable witnesses")

    return {
        "schema": SCHEMA,
        "ok": not errors,
        "errors": errors,
        "score": score,
        "raw_score": raw_score,
        "production_blocker_cap": PRODUCTION_BLOCKER_CAP,
        "level": _level(score),
        "hardness_subscore": _round(
            100.0
            * (
                components["promoted_closure"]["points"]
                + components["witness_reduction"]["points"]
                + components["search_pressure"]["points"]
            )
            / 60.0
        ),
        "assurance_subscore": _round(
            100.0
            * (
                components["promoted_closure"]["points"]
                + components["frontier_exposure"]["points"]
                + components["proof_schema_coverage"]["points"]
            )
            / 70.0
        ),
        "components": components,
        "statistics": {
            "core_closed_axis_count": core_selected,
            "core_inventory_axis_count": core_inventory,
            "core_open_inventory_axis_count": core_inventory - core_selected,
            "oracle_devnet_selected_disaster_state_count": oracle_selected,
            "oracle_devnet_unreachable_count": oracle_unreachable,
            "macos_post_materialized_witness_count": macos_materialized,
            "macos_post_reachable_witness_count": macos_reachable,
            "macos_pre_reachable_witness_count": pre_macos_reachable,
            "proof_schema_mapped_closed_axis_count": proof_schema_axis_count,
            "macos_scout_screened_candidate_count": MACOS_SCOUT_SCREENED_CANDIDATES,
        },
        "replay_commands": [
            "python3 tools/check_disaster_search_closed_receipt.py",
            "python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text",
            "python3 tools/check_disaster_proof_schema_map.py",
            (
                "python3 tools/macos_scout/build_witness_space_receipt.py "
                "--run-dir tests/fixtures/macos_scout/post_hardening_zero "
                "--blocked-run-dir tests/fixtures/macos_scout/pre_hardening_blocked "
                "--require-clean --format text"
            ),
        ],
        "non_claims": [
            "does_not_claim_exhaustive_disaster_state_closure",
            "does_not_claim_live_production_oracle_network",
            "does_not_claim_live_zenoproof_market_settlement",
            "does_not_claim_unbounded_formal_proof_coverage",
        ],
    }


def _print_text(payload: dict[str, Any]) -> None:
    stats = payload["statistics"]
    print("Disaster Hardness and Assurance Metric")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"score: {payload['score']:.1f}/100")
    print(f"raw_score: {payload['raw_score']:.1f}/100")
    print(f"level: {payload['level']}")
    print(f"hardness_subscore: {payload['hardness_subscore']:.1f}/100")
    print(f"assurance_subscore: {payload['assurance_subscore']:.1f}/100")
    print(f"core_closed_axis_count: {stats['core_closed_axis_count']}")
    print(f"core_inventory_axis_count: {stats['core_inventory_axis_count']}")
    print(f"core_open_inventory_axis_count: {stats['core_open_inventory_axis_count']}")
    print(f"oracle_devnet_unreachable_count: {stats['oracle_devnet_unreachable_count']}")
    print(f"macos_post_reachable_witness_count: {stats['macos_post_reachable_witness_count']}")
    print(f"macos_pre_reachable_witness_count: {stats['macos_pre_reachable_witness_count']}")
    print("components:")
    for name, row in payload["components"].items():
        print(f"- {name}: {row['points']:.1f}/{row['weight']:.1f}")
    if payload["errors"]:
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="Optional path to write the metric JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    payload = build_metric()
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
