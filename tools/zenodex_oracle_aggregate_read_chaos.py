#!/usr/bin/env python3
"""Replay deterministic chaos cases against the aggregate-read bridge verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle import receipt_content_hash  # noqa: E402
from zenodex_oracle_admitted_median3 import aggregate_content_hash  # noqa: E402
from zenodex_oracle_aggregate_read import (  # noqa: E402
    bridge_content_hash,
    sample_aggregate_read_bridge,
    sample_hash,
    verify_aggregate_read_bridge,
)

_BASE_BRIDGE: dict[str, Any] | None = None


def base_bridge() -> dict[str, Any]:
    global _BASE_BRIDGE
    if _BASE_BRIDGE is None:
        _BASE_BRIDGE = sample_aggregate_read_bridge()
    return copy.deepcopy(_BASE_BRIDGE)


def _read(bridge: dict[str, Any]) -> dict[str, Any]:
    return bridge["receipt_bundle"]["receipts"][0]


def _action(bridge: dict[str, Any]) -> dict[str, Any]:
    return bridge["receipt_bundle"]["receipts"][1]


def _refresh_read_action_ids(bridge: dict[str, Any]) -> None:
    read = _read(bridge)
    action = _action(bridge)
    read["id"] = receipt_content_hash(read)
    action["read_receipt_id"] = read["id"]
    action["depends_on"] = [read["id"]]
    action["id"] = receipt_content_hash(action)
    bridge["receipt_bundle"]["terminal"]["read_receipt_id"] = read["id"]
    bridge["receipt_bundle"]["terminal"]["consumer_action_receipt_id"] = action["id"]


def _refresh_aggregate_id(bridge: dict[str, Any]) -> None:
    bridge["aggregate"]["aggregate_id"] = aggregate_content_hash(bridge["aggregate"])


def _refresh_bridge_id(bridge: dict[str, Any]) -> None:
    bridge["bridge_id"] = bridge_content_hash(bridge)


def _mutate(mutator: Callable[[dict[str, Any]], None], *, refresh: bool = True) -> dict[str, Any]:
    bridge = copy.deepcopy(base_bridge())
    mutator(bridge)
    if refresh:
        _refresh_bridge_id(bridge)
    return bridge


def _wrong_query(bridge: dict[str, Any]) -> None:
    wrong = sample_hash("wrong-read-query")
    _read(bridge)["query_id"] = wrong
    _action(bridge)["query_id"] = wrong
    _refresh_read_action_ids(bridge)


def _wrong_value_hash(bridge: dict[str, Any]) -> None:
    wrong = sample_hash("wrong-read-value")
    _read(bridge)["value_hash"] = wrong
    _action(bridge)["value_hash"] = wrong
    _refresh_read_action_ids(bridge)


def _wrong_observed_epoch(bridge: dict[str, Any]) -> None:
    _read(bridge)["observed_epoch"] += 1
    _refresh_read_action_ids(bridge)


def _wrong_expiry(bridge: dict[str, Any]) -> None:
    _read(bridge)["expires_at_epoch"] += 1
    _refresh_read_action_ids(bridge)


def _wrong_action_window(bridge: dict[str, Any]) -> None:
    _action(bridge)["freshness_window_epochs"] += 1
    _refresh_read_action_ids(bridge)


def _rejected_aggregate(bridge: dict[str, Any]) -> None:
    bridge["aggregate"]["aggregate"]["value_e8"] += 1
    _refresh_aggregate_id(bridge)


def _bundle_not_accepted(bridge: dict[str, Any]) -> None:
    _read(bridge)["fresh"] = False
    _refresh_read_action_ids(bridge)


def aggregate_read_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "bridge_hash_forgery_survives",
            _mutate(lambda b: b.__setitem__("freshness_window_epochs", 3), refresh=False),
            ["bridge_content_hash_mismatch:"],
        ),
        (
            "rejected_aggregate_survives",
            _mutate(_rejected_aggregate),
            ["admitted_aggregate_not_accepted", "aggregate:aggregate_value_not_median"],
        ),
        (
            "rejected_bundle_survives",
            _mutate(_bundle_not_accepted),
            ["receipt_bundle_not_accepted", "bundle:read_fresh_required"],
        ),
        (
            "query_mismatch_survives",
            _mutate(_wrong_query),
            ["bundle_query_id_mismatch"],
        ),
        (
            "value_hash_mismatch_survives",
            _mutate(_wrong_value_hash),
            ["bundle_value_hash_mismatch"],
        ),
        (
            "observed_epoch_mismatch_survives",
            _mutate(_wrong_observed_epoch),
            ["bundle_observed_epoch_mismatch"],
        ),
        (
            "expiry_mismatch_survives",
            _mutate(_wrong_expiry),
            ["bundle_expiry_mismatch"],
        ),
        (
            "freshness_window_mismatch_survives",
            _mutate(_wrong_action_window),
            ["bundle_freshness_window_mismatch"],
        ),
        (
            "missing_aggregate_survives",
            _mutate(lambda b: b.__setitem__("aggregate", None)),
            ["aggregate_must_be_object"],
        ),
        (
            "missing_receipt_bundle_survives",
            _mutate(lambda b: b.__setitem__("receipt_bundle", None)),
            ["receipt_bundle_must_be_object"],
        ),
        (
            "hidden_top_level_field_survives",
            _mutate(lambda b: b.__setitem__("trusted_override", True)),
            ["unknown_aggregate_read_field:trusted_override"],
        ),
        (
            "wrong_schema_survives",
            _mutate(lambda b: b.__setitem__("schema", "zenodex.oracle.aggregate_read_bridge.v0")),
            ["aggregate_read_schema_mismatch"],
        ),
        (
            "boolean_freshness_window_survives",
            _mutate(lambda b: b.__setitem__("freshness_window_epochs", True)),
            ["freshness_window_epochs_must_be_int_between_1_and_9223372036854775807"],
        ),
        (
            "zero_freshness_window_survives",
            _mutate(lambda b: b.__setitem__("freshness_window_epochs", 0)),
            ["freshness_window_epochs_must_be_int_between_1_and_9223372036854775807"],
        ),
        (
            "weakened_read_evidence_survives",
            _mutate(lambda b: (_read(b).__setitem__("evidence_class", "O2"), _refresh_read_action_ids(b))),
            ["receipt_bundle_not_accepted", "bundle:critical_read_requires_o3_or_higher"],
        ),
        (
            "read_evidence_overclaim_survives",
            _mutate(lambda b: (_read(b).__setitem__("evidence_class", "O4"), _refresh_read_action_ids(b))),
            ["bundle_evidence_class_mismatch"],
        ),
        (
            "read_expiry_before_observed_survives",
            _mutate(lambda b: (_read(b).__setitem__("expires_at_epoch", _read(b)["observed_epoch"] - 1), _refresh_read_action_ids(b))),
            ["receipt_bundle_not_accepted", "bundle:read_expires_before_observed"],
        ),
    ]


@dataclass(frozen=True)
class AggregateReadChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_aggregate_read_chaos() -> dict[str, Any]:
    baseline = verify_aggregate_read_bridge(base_bridge())
    results: list[AggregateReadChaosCaseResult] = []
    for name, bridge, expected_fragments in aggregate_read_chaos_cases():
        result = verify_aggregate_read_bridge(bridge)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            AggregateReadChaosCaseResult(
                name=name,
                expected_reject=True,
                actual_status=result.status,
                expected_error_fragments=expected_fragments,
                actual_errors=actual_errors,
                passed=passed,
            )
        )

    failures = [case for case in results if not case.passed]
    return {
        "schema": "zenodex.oracle.aggregate_read_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the aggregate-read chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_aggregate_read_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
