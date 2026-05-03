#!/usr/bin/env python3
"""Replay deterministic chaos cases against the aggregate-adapter bridge."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_adapter import profile_content_hash  # noqa: E402
from zenodex_oracle_aggregate_adapter import (  # noqa: E402
    aggregate_adapter_content_hash,
    sample_aggregate_adapter_bridge,
    sample_hash,
    verify_aggregate_adapter_bridge,
)
from zenodex_oracle_aggregate_read import bridge_content_hash as aggregate_read_content_hash  # noqa: E402


def base_bridge() -> dict[str, Any]:
    return sample_aggregate_adapter_bridge()


def _refresh_bridge_id(bridge: dict[str, Any]) -> None:
    bridge["bridge_id"] = aggregate_adapter_content_hash(bridge)


def _refresh_aggregate_read_id(bridge: dict[str, Any]) -> None:
    aggregate_read = bridge["aggregate_read"]
    aggregate_read["bridge_id"] = aggregate_read_content_hash(aggregate_read)


def _refresh_profile_id(bridge: dict[str, Any]) -> None:
    bridge["profile"]["profile_id"] = profile_content_hash(bridge["profile"])


def _mutate(mutator: Callable[[dict[str, Any]], None], *, refresh: bool = True) -> dict[str, Any]:
    bridge = copy.deepcopy(base_bridge())
    mutator(bridge)
    if refresh:
        _refresh_bridge_id(bridge)
    return bridge


def _bad_aggregate_read(bridge: dict[str, Any]) -> None:
    bridge["aggregate_read"]["receipt_bundle"]["receipts"][0]["fresh"] = False
    _refresh_aggregate_read_id(bridge)


def aggregate_adapter_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "bridge_hash_forgery_survives",
            _mutate(lambda b: b["action"].__setitem__("critical", False), refresh=False),
            ["aggregate_adapter_content_hash_mismatch:"],
        ),
        (
            "aggregate_read_rejection_survives",
            _mutate(_bad_aggregate_read),
            ["aggregate_read_not_accepted", "aggregate_read:receipt_bundle_not_accepted"],
        ),
        (
            "action_query_mismatch_survives",
            _mutate(lambda b: b["action"].__setitem__("query_id", sample_hash("wrong-action-query"))),
            ["adapter_not_accepted", "adapter:adapter_query_id_mismatch"],
        ),
        (
            "action_value_hash_mismatch_survives",
            _mutate(lambda b: b["action"].__setitem__("value_hash", sample_hash("wrong-action-value"))),
            ["adapter_not_accepted", "adapter:adapter_value_hash_mismatch"],
        ),
        (
            "action_id_mismatch_survives",
            _mutate(lambda b: b["action"].__setitem__("action_id", sample_hash("wrong-action-id"))),
            ["adapter_not_accepted", "adapter:adapter_action_id_mismatch"],
        ),
        (
            "action_read_receipt_mismatch_survives",
            _mutate(lambda b: b["action"].__setitem__("read_receipt_id", sample_hash("wrong-read"))),
            ["adapter_not_accepted", "adapter:adapter_read_receipt_id_mismatch"],
        ),
        (
            "action_consumer_receipt_mismatch_survives",
            _mutate(lambda b: b["action"].__setitem__("consumer_action_receipt_id", sample_hash("wrong-consumer"))),
            ["adapter_not_accepted", "adapter:adapter_consumer_action_receipt_id_mismatch"],
        ),
        (
            "profile_hash_forgery_survives",
            _mutate(lambda b: b["profile"].__setitem__("max_freshness_window_epochs", b["profile"]["max_freshness_window_epochs"] + 1)),
            ["adapter_not_accepted", "adapter:profile_content_hash_mismatch:"],
        ),
        (
            "profile_module_mismatch_survives",
            _mutate(
                lambda b: (
                    b["profile"].__setitem__("consumer_module", "zenodex.oracle.other"),
                    _refresh_profile_id(b),
                )
            ),
            ["adapter_not_accepted", "adapter:profile_consumer_module_mismatch"],
        ),
        (
            "action_freshness_exceeds_profile_survives",
            _mutate(lambda b: b["action"].__setitem__("max_freshness_window_epochs", b["action"]["max_freshness_window_epochs"] + 1)),
            ["adapter_not_accepted", "adapter:action_freshness_window_exceeds_profile"],
        ),
        (
            "action_not_critical_survives",
            _mutate(lambda b: b["action"].__setitem__("critical", False)),
            ["adapter_not_accepted", "adapter:action_must_be_critical"],
        ),
        (
            "missing_aggregate_read_survives",
            _mutate(lambda b: b.__setitem__("aggregate_read", None)),
            ["aggregate_read_must_be_object"],
        ),
        (
            "missing_action_survives",
            _mutate(lambda b: b.__setitem__("action", None)),
            ["action_must_be_object"],
        ),
        (
            "missing_profile_survives",
            _mutate(lambda b: b.__setitem__("profile", None)),
            ["profile_must_be_object"],
        ),
        (
            "hidden_top_level_field_survives",
            _mutate(lambda b: b.__setitem__("trusted_override", True)),
            ["unknown_aggregate_adapter_field:trusted_override"],
        ),
        (
            "wrong_schema_survives",
            _mutate(lambda b: b.__setitem__("schema", "zenodex.oracle.aggregate_adapter_bridge.v0")),
            ["aggregate_adapter_schema_mismatch"],
        ),
    ]


@dataclass(frozen=True)
class AggregateAdapterChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_aggregate_adapter_chaos() -> dict[str, Any]:
    baseline = verify_aggregate_adapter_bridge(base_bridge())
    results: list[AggregateAdapterChaosCaseResult] = []
    for name, bridge, expected_fragments in aggregate_adapter_chaos_cases():
        result = verify_aggregate_adapter_bridge(bridge)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            AggregateAdapterChaosCaseResult(
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
        "schema": "zenodex.oracle.aggregate_adapter_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the aggregate-adapter chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_aggregate_adapter_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
