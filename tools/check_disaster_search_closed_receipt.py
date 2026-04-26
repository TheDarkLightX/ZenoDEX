#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.stateful_scenario_bridge import (
    CLOSED_DISASTER_SEARCH_AXIS_IDS,
    DISASTER_SEARCH_EXPANSION_AXES,
    DISASTER_SEARCH_EXPANSION_RECEIPT_SCHEMA,
    run_disaster_search_expansion_plan,
)

CLOSED_DISASTER_SEARCH_RATCHET_SCHEMA = "zenodex/disaster-search-closed-receipt-ratchet/v1"


def _axis_inventory_ids() -> set[str]:
    return {str(axis.get("axis_id")) for axis in DISASTER_SEARCH_EXPANSION_AXES}


def build_closed_receipt_ratchet_report(
    receipt: dict[str, Any],
    *,
    expected_axis_ids: Sequence[str] = CLOSED_DISASTER_SEARCH_AXIS_IDS,
) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []
    expected = [str(axis_id) for axis_id in expected_axis_ids]
    expected_set = set(expected)

    if len(expected) != len(expected_set):
        errors.append("closed disaster axis list contains duplicates")

    inventory_ids = _axis_inventory_ids()
    missing_from_inventory = sorted(expected_set - inventory_ids)
    if missing_from_inventory:
        errors.append(f"closed axis id(s) missing from expansion inventory: {', '.join(missing_from_inventory)}")

    if receipt.get("schema") != DISASTER_SEARCH_EXPANSION_RECEIPT_SCHEMA:
        errors.append(f"receipt schema must equal {DISASTER_SEARCH_EXPANSION_RECEIPT_SCHEMA}")
    if receipt.get("ok") is not True:
        errors.append("closed disaster receipt is not ok")

    axis_results = receipt.get("axis_results", [])
    if not isinstance(axis_results, list):
        errors.append("receipt axis_results must be a list")
        axis_results = []
    actual_ids = [str(row.get("axis_id")) for row in axis_results if isinstance(row, dict)]
    actual_set = set(actual_ids)
    if actual_set != expected_set:
        missing = sorted(expected_set - actual_set)
        unexpected = sorted(actual_set - expected_set)
        if missing:
            errors.append(f"receipt is missing closed axis id(s): {', '.join(missing)}")
        if unexpected:
            errors.append(f"receipt contains unexpected axis id(s): {', '.join(unexpected)}")

    selected_count = int(receipt.get("selected_axis_count", -1))
    unreachable_count = int(receipt.get("unreachable_count", -1))
    failed_count = int(receipt.get("failed_count", -1))
    inconclusive_count = int(receipt.get("inconclusive_count", -1))

    if selected_count != len(expected):
        errors.append(f"selected_axis_count {selected_count} must equal pinned closed count {len(expected)}")
    if unreachable_count != len(expected):
        errors.append(f"unreachable_count {unreachable_count} must equal pinned closed count {len(expected)}")
    if failed_count != 0:
        errors.append(f"failed_count must be 0, got {failed_count}")
    if inconclusive_count != 0:
        errors.append(f"inconclusive_count must be 0, got {inconclusive_count}")

    regressed_axes: list[str] = []
    for row in axis_results:
        if not isinstance(row, dict):
            continue
        axis_id = str(row.get("axis_id"))
        if row.get("status") != "unreachable_under_current_bounds":
            regressed_axes.append(axis_id)
    if regressed_axes:
        errors.append(f"closed axis status regressed: {', '.join(sorted(regressed_axes))}")

    policy = receipt.get("policy", {})
    if isinstance(policy, dict) and policy.get("skips_are_inconclusive") is not True:
        warnings.append("receipt policy does not explicitly mark skips as inconclusive")

    return {
        "schema": CLOSED_DISASTER_SEARCH_RATCHET_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "warnings": warnings,
        "pinned_axis_count": len(expected),
        "receipt_selected_axis_count": selected_count,
        "receipt_unreachable_count": unreachable_count,
        "receipt_failed_count": failed_count,
        "receipt_inconclusive_count": inconclusive_count,
        "closed_axis_ids": expected,
    }


def _print_text(payload: dict[str, Any]) -> None:
    print("Closed Disaster Search Receipt Ratchet")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"pinned_axis_count: {payload['pinned_axis_count']}")
    print(f"receipt_selected_axis_count: {payload['receipt_selected_axis_count']}")
    print(f"receipt_unreachable_count: {payload['receipt_unreachable_count']}")
    print(f"receipt_failed_count: {payload['receipt_failed_count']}")
    print(f"receipt_inconclusive_count: {payload['receipt_inconclusive_count']}")
    if payload.get("errors"):
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")
    if payload.get("warnings"):
        print("warnings:")
        for warning in payload["warnings"]:
            print(f"- {warning}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run and ratchet the pinned closed disaster-state receipt.")
    parser.add_argument("--timeout-s", type=int, default=240)
    parser.add_argument("--receipt", help="Existing receipt JSON to ratchet instead of running the closed axes")
    parser.add_argument("--output", help="Optional path to write the ratchet report JSON")
    parser.add_argument("--receipt-output", help="Optional path to write the raw closed receipt JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    if args.receipt:
        receipt_path = Path(args.receipt)
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    else:
        receipt = run_disaster_search_expansion_plan(
            axis_ids=list(CLOSED_DISASTER_SEARCH_AXIS_IDS),
            timeout_s=int(args.timeout_s),
        )

    if args.receipt_output:
        receipt_out = Path(args.receipt_output)
        receipt_out.parent.mkdir(parents=True, exist_ok=True)
        receipt_out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    payload = build_closed_receipt_ratchet_report(receipt)
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
