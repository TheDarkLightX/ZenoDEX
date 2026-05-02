#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Oracle feed registry verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_feed_registry import (  # noqa: E402
    content_hash,
    sample_feed_registry,
    verify_feed_registry,
)
from zenodex_oracle_source_diversity import source_set_content_hash  # noqa: E402


def base_registry() -> dict[str, Any]:
    return sample_feed_registry()


def _refresh_query_spec(feed: dict[str, Any]) -> None:
    feed["query_spec"]["query_id"] = content_hash(feed["query_spec"], omit_key="query_id")


def _refresh_source_diversity(feed: dict[str, Any]) -> None:
    feed["source_diversity"]["source_set_id"] = source_set_content_hash(feed["source_diversity"])


def _refresh_aggregate_policy(feed: dict[str, Any]) -> None:
    feed["aggregate_policy"]["policy_id"] = content_hash(feed["aggregate_policy"], omit_key="policy_id")


def _refresh_feed(feed: dict[str, Any]) -> None:
    feed["feed_id"] = content_hash(feed, omit_key="feed_id")


def _refresh_registry(registry: dict[str, Any]) -> None:
    registry["registry_id"] = content_hash(registry, omit_key="registry_id")


def _refresh_all(registry: dict[str, Any]) -> None:
    for feed in registry["feeds"]:
        _refresh_query_spec(feed)
        feed["source_diversity"]["query_id"] = feed["query_spec"]["query_id"]
        _refresh_source_diversity(feed)
        _refresh_aggregate_policy(feed)
        _refresh_feed(feed)
    _refresh_registry(registry)


def _mutate(
    mutator: Callable[[dict[str, Any]], None],
    *,
    refresh: Callable[[dict[str, Any]], None] = _refresh_all,
) -> dict[str, Any]:
    registry = copy.deepcopy(base_registry())
    mutator(registry)
    refresh(registry)
    return registry


def _refresh_feed_and_registry(registry: dict[str, Any]) -> None:
    for feed in registry["feeds"]:
        _refresh_feed(feed)
    _refresh_registry(registry)


def _refresh_registry_only(registry: dict[str, Any]) -> None:
    _refresh_registry(registry)


def _append_duplicate_query(registry: dict[str, Any]) -> None:
    duplicate = copy.deepcopy(registry["feeds"][0])
    duplicate["created_epoch"] = 9
    _refresh_feed(duplicate)
    registry["feeds"].append(duplicate)


def feed_registry_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "registry_hash_forgery_survives",
            _mutate(lambda r: r.__setitem__("current_epoch", 11), refresh=lambda _r: None),
            ["registry_content_hash_mismatch:"],
        ),
        (
            "feed_hash_forgery_survives",
            _mutate(
                lambda r: r["feeds"][0].__setitem__("created_epoch", 9),
                refresh=_refresh_registry_only,
            ),
            ["feed_content_hash_mismatch:"],
        ),
        (
            "query_hash_forgery_survives",
            _mutate(
                lambda r: r["feeds"][0]["query_spec"].__setitem__("base_asset", "wbtc"),
                refresh=_refresh_feed_and_registry,
            ),
            ["query_spec_content_hash_mismatch:"],
        ),
        (
            "aggregate_policy_hash_forgery_survives",
            _mutate(
                lambda r: r["feeds"][0]["aggregate_policy"].__setitem__("max_deviation_bps", 150),
                refresh=_refresh_feed_and_registry,
            ),
            ["aggregate_policy_content_hash_mismatch:"],
        ),
        (
            "source_diversity_hash_forgery_survives",
            _mutate(
                lambda r: r["feeds"][0]["source_diversity"].__setitem__("min_sources", 2),
                refresh=_refresh_feed_and_registry,
            ),
            ["source_diversity_rejected", "source_diversity:source_set_content_hash_mismatch:"],
        ),
        (
            "duplicate_feed_id_survives",
            _mutate(lambda r: r["feeds"].append(copy.deepcopy(r["feeds"][0])), refresh=_refresh_registry_only),
            ["duplicate_feed_id:"],
        ),
        (
            "duplicate_query_id_survives",
            _mutate(_append_duplicate_query, refresh=_refresh_registry_only),
            ["duplicate_query_id:"],
        ),
        (
            "base_quote_same_survives",
            _mutate(lambda r: r["feeds"][0]["query_spec"].__setitem__("quote_asset", "agrs")),
            ["base_quote_assets_must_differ"],
        ),
        (
            "weak_min_reporters_survives",
            _mutate(lambda r: r["feeds"][0]["aggregate_policy"].__setitem__("min_reporters", 2)),
            ["min_reporters_must_be_int_between_3_and_64"],
        ),
        (
            "weak_min_sources_survives",
            _mutate(lambda r: r["feeds"][0]["aggregate_policy"].__setitem__("min_sources", 2)),
            ["min_sources_must_be_int_between_3_and_64"],
        ),
        (
            "zero_freshness_survives",
            _mutate(lambda r: r["feeds"][0]["aggregate_policy"].__setitem__("freshness_window_epochs", 0)),
            ["freshness_window_epochs_must_be_int_between_1_and_1000000000000"],
        ),
        (
            "excessive_deviation_survives",
            _mutate(lambda r: r["feeds"][0]["aggregate_policy"].__setitem__("max_deviation_bps", 10_001)),
            ["max_deviation_bps_must_be_int_between_0_and_10000"],
        ),
        (
            "weak_evidence_floor_survives",
            _mutate(lambda r: r["feeds"][0]["aggregate_policy"].__setitem__("evidence_floor", "O2")),
            ["evidence_floor_below_critical_minimum"],
        ),
        (
            "unsupported_aggregate_policy_survives",
            _mutate(lambda r: r["feeds"][0]["aggregate_policy"].__setitem__("aggregation_schema", "zenodex.oracle.mean.v1")),
            ["aggregation_schema_must_be_admitted_median3"],
        ),
        (
            "unsupported_report_schema_survives",
            _mutate(lambda r: r["feeds"][0]["aggregate_policy"].__setitem__("report_schema", "zenodex.oracle.raw_report.v1")),
            ["report_schema_must_be_signed_report_v1"],
        ),
        (
            "source_query_mismatch_survives",
            _mutate(
                lambda r: r["feeds"][0]["source_diversity"].__setitem__(
                    "query_id",
                    "sha256:" + ("1" * 64),
                ),
                refresh=lambda r: (
                    _refresh_source_diversity(r["feeds"][0]),
                    _refresh_feed(r["feeds"][0]),
                    _refresh_registry(r),
                ),
            ),
            ["source_diversity_query_mismatch"],
        ),
        (
            "source_operator_correlation_survives",
            _mutate(lambda r: r["feeds"][0]["source_diversity"]["sources"][1].__setitem__("operator_id", "operator.dex")),
            ["source_diversity_rejected", "source_diversity:not_enough_distinct_operators"],
        ),
        (
            "future_created_feed_survives",
            _mutate(lambda r: r["feeds"][0].__setitem__("created_epoch", 11)),
            ["feed_created_epoch_in_future"],
        ),
        (
            "inactive_feed_survives",
            _mutate(lambda r: r["feeds"][0].__setitem__("status", "paused")),
            ["feed_status_must_be_active"],
        ),
        (
            "hidden_registry_field_survives",
            _mutate(lambda r: r.__setitem__("governance_override", True)),
            ["unknown_feed_registry_field:governance_override"],
        ),
        (
            "hidden_feed_field_survives",
            _mutate(lambda r: r["feeds"][0].__setitem__("admin_override", True)),
            ["unknown_feed_field:admin_override"],
        ),
        (
            "hidden_query_field_survives",
            _mutate(lambda r: r["feeds"][0]["query_spec"].__setitem__("semantic_alias", "trusted")),
            ["unknown_query_spec_field:semantic_alias"],
        ),
        (
            "hidden_policy_field_survives",
            _mutate(lambda r: r["feeds"][0]["aggregate_policy"].__setitem__("skip_disputes", True)),
            ["unknown_aggregate_policy_field:skip_disputes"],
        ),
        (
            "wrong_registry_schema_survives",
            _mutate(lambda r: r.__setitem__("schema", "zenodex.oracle.feed_registry.v0")),
            ["feed_registry_schema_mismatch"],
        ),
        (
            "feeds_as_object_survives",
            _mutate(lambda r: r.__setitem__("feeds", {"feed_id": "feed.fake"}), refresh=_refresh_registry_only),
            ["feeds_must_be_list"],
        ),
        (
            "boolean_current_epoch_survives",
            _mutate(lambda r: r.__setitem__("current_epoch", True)),
            ["current_epoch_must_be_int_between_0_and_1000000000000"],
        ),
    ]


@dataclass(frozen=True)
class FeedRegistryChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_feed_registry_chaos() -> dict[str, Any]:
    baseline = verify_feed_registry(base_registry())
    results: list[FeedRegistryChaosCaseResult] = []
    for name, registry, expected_fragments in feed_registry_chaos_cases():
        result = verify_feed_registry(registry)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            FeedRegistryChaosCaseResult(
                name=name,
                expected_reject=True,
                actual_status=result.status,
                expected_error_fragments=expected_fragments,
                actual_errors=actual_errors,
                passed=passed,
            )
        )

    failures = [case for case in results if not case.passed]
    rejected = [case for case in results if case.actual_status == "rejected"]
    return {
        "schema": "zenodex.oracle.feed_registry_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": len(rejected),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the feed registry chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_feed_registry_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
