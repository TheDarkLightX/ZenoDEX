#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Zeno Oracle query-policy verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_query_policy import (  # noqa: E402
    content_hash,
    sample_hash,
    sample_policy_trace,
    verify_policy_trace,
)


def base_trace() -> dict[str, Any]:
    return sample_policy_trace()


def _refresh_policy_id(trace: dict[str, Any], event_index: int) -> None:
    policy = trace["events"][event_index]["policy"]
    policy["policy_id"] = content_hash(policy, omit_key="policy_id")


def _mutate(mutator: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    trace = copy.deepcopy(base_trace())
    mutator(trace)
    return trace


def _policy_mutation(mutator: Callable[[dict[str, Any]], None]) -> Callable[[dict[str, Any]], None]:
    def inner(trace: dict[str, Any]) -> None:
        mutator(trace["events"][2]["policy"])
        _refresh_policy_id(trace, 2)

    return inner


def _first_policy_mutation(mutator: Callable[[dict[str, Any]], None]) -> Callable[[dict[str, Any]], None]:
    def inner(trace: dict[str, Any]) -> None:
        mutator(trace["events"][0]["policy"])
        _refresh_policy_id(trace, 0)

    return inner


def _nonlatest_binding(trace: dict[str, Any]) -> None:
    publish_v2 = trace["events"][2]
    bind_v1 = trace["events"][1]
    publish_v2["epoch"] = 2
    bind_v1["epoch"] = 3
    bind_v1["action_epoch"] = 3
    trace["events"] = [trace["events"][0], publish_v2, bind_v1]


def query_policy_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "staleness_downgrade_survives",
            _mutate(_policy_mutation(lambda p: p.__setitem__("max_staleness_epochs", 5))),
            ["policy_staleness_downgrade"],
        ),
        (
            "deviation_downgrade_survives",
            _mutate(_policy_mutation(lambda p: p.__setitem__("max_deviation_bps", 250))),
            ["policy_deviation_downgrade"],
        ),
        (
            "evidence_floor_downgrade_survives",
            _mutate(_policy_mutation(lambda p: p.__setitem__("evidence_floor", "O2"))),
            ["evidence_floor_below_critical_minimum", "policy_evidence_floor_downgrade"],
        ),
        (
            "source_quorum_downgrade_survives",
            _mutate(_policy_mutation(lambda p: p.__setitem__("min_distinct_sources", 2))),
            ["policy_source_quorum_downgrade"],
        ),
        (
            "reporter_quorum_downgrade_survives",
            _mutate(_policy_mutation(lambda p: p.__setitem__("min_distinct_reporters", 2))),
            ["policy_reporter_quorum_downgrade"],
        ),
        (
            "aggregation_schema_drift_survives",
            _mutate(_policy_mutation(lambda p: p.__setitem__("aggregation_schema", "zenodex.oracle.mean3_aggregate.v1"))),
            ["policy_aggregation_schema_change"],
        ),
        (
            "read_schema_drift_survives",
            _mutate(_policy_mutation(lambda p: p.__setitem__("read_schema", "zenodex.oracle.receipt_bundle.v0"))),
            ["policy_read_schema_change"],
        ),
        (
            "policy_content_hash_forgery_survives",
            _mutate(lambda t: t["events"][0]["policy"].__setitem__("max_staleness_epochs", 7)),
            ["policy_content_hash_mismatch"],
        ),
        (
            "policy_query_mismatch_survives",
            _mutate(_first_policy_mutation(lambda p: p.__setitem__("query_id", sample_hash("other-query")))),
            ["policy_query_id_mismatch"],
        ),
        (
            "wrong_supersedes_survives",
            _mutate(_policy_mutation(lambda p: p.__setitem__("supersedes_policy_id", sample_hash("wrong-policy")))),
            ["policy_supersedes_must_equal_active_policy"],
        ),
        (
            "version_skip_survives",
            _mutate(_policy_mutation(lambda p: p.__setitem__("version", 3))),
            ["policy_version_must_increment_by_1"],
        ),
        (
            "unknown_policy_binding_survives",
            _mutate(lambda t: t["events"][1].__setitem__("policy_id", sample_hash("missing-policy"))),
            ["consumer_binds_unknown_policy"],
        ),
        (
            "nonlatest_policy_binding_survives",
            _mutate(_nonlatest_binding),
            ["consumer_binds_nonlatest_policy"],
        ),
        (
            "noncritical_binding_survives",
            _mutate(lambda t: t["events"][1].__setitem__("critical", False)),
            ["consumer_binding_must_be_critical"],
        ),
        (
            "action_before_binding_survives",
            _mutate(lambda t: t["events"][1].__setitem__("action_epoch", 1)),
            ["consumer_action_before_policy_binding"],
        ),
        (
            "hidden_policy_field_survives",
            _mutate(_first_policy_mutation(lambda p: p.__setitem__("admin_override", True))),
            ["unknown_policy_field:admin_override"],
        ),
        (
            "hidden_event_field_survives",
            _mutate(lambda t: t["events"][1].__setitem__("admin_override", True)),
            ["unknown_event_bind_consumer_field:admin_override"],
        ),
        (
            "event_epoch_regression_survives",
            _mutate(lambda t: t["events"][2].__setitem__("epoch", 0)),
            ["event_epoch_regression:2"],
        ),
        (
            "wrong_schema_survives",
            _mutate(lambda t: t.__setitem__("schema", "zenodex.oracle.query_policy_trace.v0")),
            ["query_policy_schema_mismatch"],
        ),
    ]


@dataclass(frozen=True)
class QueryPolicyChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_query_policy_chaos() -> dict[str, Any]:
    baseline = verify_policy_trace(base_trace())
    results: list[QueryPolicyChaosCaseResult] = []
    for name, trace, expected_fragments in query_policy_chaos_cases():
        result = verify_policy_trace(trace)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            QueryPolicyChaosCaseResult(
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
        "schema": "zenodex.oracle.query_policy_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the query-policy chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_query_policy_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
