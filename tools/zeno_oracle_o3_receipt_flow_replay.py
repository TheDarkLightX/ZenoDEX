#!/usr/bin/env python3
"""Replay one deterministic end-to-end ZenoOracle O3 receipt flow."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from zenodex_oracle import verify_bundle  # noqa: E402
from zenodex_oracle_adapter import ACTION_SCHEMA, PROFILE_SCHEMA, profile_content_hash  # noqa: E402
from zenodex_oracle_admitted_median3 import (  # noqa: E402
    ADMITTED_MEDIAN3_SCHEMA,
    MIN_CRITICAL_EVIDENCE,
    _confidence,
    _deviation_bps,
    _median3,
    _single_report_admission,
    aggregate_content_hash,
    verify_admitted_median3_aggregate,
)
from zenodex_oracle_aggregate_adapter import (  # noqa: E402
    AGGREGATE_ADAPTER_SCHEMA,
    aggregate_adapter_content_hash,
    verify_aggregate_adapter_bridge,
)
from zenodex_oracle_aggregate_read import (  # noqa: E402
    AGGREGATE_READ_SCHEMA,
    _bundle_for_aggregate,
    aggregate_read_value_hash,
    bridge_content_hash as aggregate_read_content_hash,
    verify_aggregate_read_bridge,
)
from zenodex_oracle_feed_registry import (  # noqa: E402
    content_hash as feed_registry_content_hash,
    sample_feed_registry,
    verify_feed_registry,
)
from zenodex_oracle_report_admission import verify_report_admission  # noqa: E402


RESULT_SCHEMA = "zenodex.oracle.o3_receipt_flow_replay.v1"
REPLAY_COMMAND = "python3 tools/zeno_oracle_o3_receipt_flow_replay.py --format text"
NOT_CLAIMED = [
    "does_not_claim_true_market_price",
    "does_not_claim_reporter_honesty",
    "does_not_claim_source_honesty",
    "does_not_claim_production_oracle_network_live",
    "does_not_claim_onchain_feed_governance_live",
]


def _stage(name: str, *, ok: bool, status: str, observed: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "name": name,
        "ok": bool(ok),
        "status": status,
        "observed": dict(observed),
    }


def _active_feed(registry: Mapping[str, Any]) -> Mapping[str, Any]:
    feeds = registry.get("feeds")
    if not isinstance(feeds, list):
        raise ValueError("feed registry sample must contain feeds")
    active = [feed for feed in feeds if isinstance(feed, Mapping) and feed.get("status") == "active"]
    if len(active) != 1:
        raise ValueError(f"expected exactly one active feed, got {len(active)}")
    return active[0]


def _sample_registry_at_epoch(current_epoch: int) -> dict[str, Any]:
    registry = sample_feed_registry()
    registry["current_epoch"] = current_epoch
    registry["registry_id"] = feed_registry_content_hash(registry, omit_key="registry_id")
    return registry


def _build_admissions(feed: Mapping[str, Any], *, current_epoch: int) -> list[dict[str, Any]]:
    source_diversity = feed.get("source_diversity")
    if not isinstance(source_diversity, Mapping):
        raise ValueError("active feed source_diversity must be an object")
    query_id = str(feed["query_spec"]["query_id"])
    source_ids = [str(source["source_id"]) for source in source_diversity["sources"]]
    values = [100_000_000, 101_000_000, 99_500_000]
    epochs = [100, 101, 102]
    reporters = ["reporter.alpha", "reporter.beta", "reporter.gamma"]
    private_keys = [43, 44, 45]
    policy = feed.get("aggregate_policy")
    if not isinstance(policy, Mapping):
        raise ValueError("active feed aggregate_policy must be an object")
    return [
        _single_report_admission(
            private_key=private_keys[index],
            reporter_id=reporters[index],
            source_id=source_ids[index],
            query_id=query_id,
            value_e8=values[index],
            observed_epoch=epochs[index],
            source_diversity=source_diversity,
            current_epoch=current_epoch,
            max_staleness_epochs=int(policy["freshness_window_epochs"]),
        )
        for index in range(3)
    ]


def _build_aggregate(
    feed: Mapping[str, Any],
    admissions: list[dict[str, Any]],
    *,
    current_epoch: int,
) -> dict[str, Any]:
    policy = feed.get("aggregate_policy")
    if not isinstance(policy, Mapping):
        raise ValueError("active feed aggregate_policy must be an object")
    admitted_reports = [verify_report_admission(admission).admitted_reports[0] for admission in admissions]
    values = [int(report["value_e8"]) for report in admitted_reports]
    epochs = [int(report["observed_epoch"]) for report in admitted_reports]
    median = _median3(values)
    confidence = _confidence(values, median)
    deviation = _deviation_bps(confidence, median)
    aggregate = {
        "schema": ADMITTED_MEDIAN3_SCHEMA,
        "query_id": str(feed["query_spec"]["query_id"]),
        "current_epoch": current_epoch,
        "max_staleness_epochs": int(policy["freshness_window_epochs"]),
        "evidence_floor": MIN_CRITICAL_EVIDENCE,
        "evidence_class": MIN_CRITICAL_EVIDENCE,
        "max_deviation_bps": int(policy["max_deviation_bps"]),
        "min_distinct_sources": int(policy["min_sources"]),
        "report_admissions": admissions,
        "aggregate": {
            "value_e8": median,
            "confidence_e8": confidence,
            "deviation_bps": deviation,
            "observed_epoch": max(epochs),
            "report_count": len(admitted_reports),
        },
    }
    aggregate["aggregate_id"] = aggregate_content_hash(aggregate)
    return aggregate


def _build_aggregate_read(aggregate: Mapping[str, Any], *, freshness_window_epochs: int) -> dict[str, Any]:
    aggregate_result = verify_admitted_median3_aggregate(aggregate)
    if aggregate_result.status != "accepted":
        raise ValueError(f"aggregate must be accepted: {aggregate_result.errors}")
    value_hash = aggregate_read_value_hash(
        aggregate_id=str(aggregate_result.aggregate_id),
        query_id=str(aggregate_result.query_id),
        value_e8=int(aggregate_result.value_e8),
        confidence_e8=int(aggregate_result.confidence_e8),
        deviation_bps=int(aggregate_result.deviation_bps),
        observed_epoch=int(aggregate_result.observed_epoch),
        report_count=int(aggregate_result.report_count),
        admission_count=int(aggregate_result.admission_count),
    )
    bridge = {
        "schema": AGGREGATE_READ_SCHEMA,
        "freshness_window_epochs": freshness_window_epochs,
        "aggregate": dict(aggregate),
        "receipt_bundle": _bundle_for_aggregate(
            aggregate_id=str(aggregate_result.aggregate_id),
            query_id=str(aggregate_result.query_id),
            value_hash=value_hash,
            observed_epoch=int(aggregate_result.observed_epoch),
            freshness_window_epochs=freshness_window_epochs,
        ),
    }
    bridge["bridge_id"] = aggregate_read_content_hash(bridge)
    return bridge


def _build_aggregate_adapter(aggregate_read: Mapping[str, Any]) -> dict[str, Any]:
    bundle_result = verify_bundle(aggregate_read["receipt_bundle"])
    if bundle_result.status != "accepted":
        raise ValueError(f"receipt bundle must be accepted: {bundle_result.errors}")
    action = {
        "schema": ACTION_SCHEMA,
        "consumer_module": bundle_result.consumer_module,
        "action_kind": bundle_result.action_kind,
        "action_id": bundle_result.action_id,
        "action_epoch": bundle_result.action_epoch,
        "query_id": bundle_result.query_id,
        "value_hash": bundle_result.value_hash,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": bundle_result.freshness_window_epochs,
        "read_receipt_id": bundle_result.read_receipt_id,
        "consumer_action_receipt_id": bundle_result.consumer_action_receipt_id,
        "critical": True,
    }
    profile = {
        "schema": PROFILE_SCHEMA,
        "consumer_module": bundle_result.consumer_module,
        "action_kind": bundle_result.action_kind,
        "query_id": bundle_result.query_id,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": bundle_result.freshness_window_epochs,
        "critical": True,
    }
    profile["profile_id"] = profile_content_hash(profile)
    bridge = {
        "schema": AGGREGATE_ADAPTER_SCHEMA,
        "aggregate_read": dict(aggregate_read),
        "action": action,
        "profile": profile,
    }
    bridge["bridge_id"] = aggregate_adapter_content_hash(bridge)
    return bridge


def build_o3_receipt_flow_replay() -> dict[str, Any]:
    current_epoch = 104
    stages: list[dict[str, Any]] = []
    errors: list[str] = []

    registry = _sample_registry_at_epoch(current_epoch)
    feed_result = verify_feed_registry(registry).to_json_obj()
    stages.append(
        _stage(
            "feed_registry",
            ok=feed_result["status"] == "accepted",
            status=str(feed_result["status"]),
            observed={
                "registry_id": feed_result["registry_id"],
                "active_feed_count": feed_result["active_feed_count"],
                "query_ids": feed_result["query_ids"],
            },
        )
    )
    if feed_result["status"] != "accepted":
        errors.extend(f"feed_registry:{error}" for error in feed_result["errors"])

    feed = _active_feed(registry)
    admissions = _build_admissions(feed, current_epoch=current_epoch)
    admission_results = [verify_report_admission(admission).to_json_obj() for admission in admissions]
    reporter_ids = [
        admission["signed_submission"]["reporter_id"]
        for admission in admissions
        if isinstance(admission.get("signed_submission"), Mapping)
    ]
    stages.append(
        _stage(
            "reporter_lifecycle",
            ok=all(result["status"] == "accepted" for result in admission_results),
            status=(
                "accepted"
                if all(result["status"] == "accepted" for result in admission_results)
                else "rejected"
            ),
            observed={"reporter_ids": reporter_ids, "reporter_count": len(set(reporter_ids))},
        )
    )
    signed_report_count = sum(
        len(admission["signed_submission"]["reports"])
        for admission in admissions
        if isinstance(admission.get("signed_submission"), Mapping)
    )
    stages.append(
        _stage(
            "signed_report",
            ok=signed_report_count == 3 and all(result["status"] == "accepted" for result in admission_results),
            status=(
                "accepted"
                if signed_report_count == 3
                and all(result["status"] == "accepted" for result in admission_results)
                else "rejected"
            ),
            observed={"signed_report_count": signed_report_count},
        )
    )
    stages.append(
        _stage(
            "report_admission",
            ok=all(result["status"] == "accepted" for result in admission_results),
            status="accepted" if all(result["status"] == "accepted" for result in admission_results) else "rejected",
            observed={
                "admission_count": len(admission_results),
                "admission_ids": [result["admission_id"] for result in admission_results],
            },
        )
    )
    for index, result in enumerate(admission_results):
        if result["status"] != "accepted":
            errors.extend(f"report_admission_{index}:{error}" for error in result["errors"])

    aggregate = _build_aggregate(feed, admissions, current_epoch=current_epoch)
    aggregate_result = verify_admitted_median3_aggregate(aggregate).to_json_obj()
    stages.append(
        _stage(
            "admitted_median3",
            ok=aggregate_result["status"] == "accepted",
            status=str(aggregate_result["status"]),
            observed={
                "aggregate_id": aggregate_result["aggregate_id"],
                "query_id": aggregate_result["query_id"],
                "evidence_class": aggregate_result["evidence_class"],
                "report_count": aggregate_result["report_count"],
                "admission_count": aggregate_result["admission_count"],
                "distinct_source_count": aggregate_result["distinct_source_count"],
            },
        )
    )
    if aggregate_result["status"] != "accepted":
        errors.extend(f"admitted_median3:{error}" for error in aggregate_result["errors"])

    freshness_window_epochs = int(feed["aggregate_policy"]["freshness_window_epochs"])
    aggregate_read = _build_aggregate_read(aggregate, freshness_window_epochs=freshness_window_epochs)
    read_result = verify_aggregate_read_bridge(aggregate_read).to_json_obj()
    stages.append(
        _stage(
            "accepted_read",
            ok=read_result["status"] == "accepted",
            status=str(read_result["status"]),
            observed={
                "aggregate_read_bridge_id": read_result["bridge_id"],
                "read_receipt_id": read_result["read_receipt_id"],
                "consumer_action_receipt_id": read_result["consumer_action_receipt_id"],
                "evidence_class": read_result["evidence_class"],
            },
        )
    )
    if read_result["status"] != "accepted":
        errors.extend(f"accepted_read:{error}" for error in read_result["errors"])

    aggregate_adapter = _build_aggregate_adapter(aggregate_read)
    adapter_result = verify_aggregate_adapter_bridge(aggregate_adapter).to_json_obj()
    stages.append(
        _stage(
            "action_adapter",
            ok=adapter_result["status"] == "accepted",
            status=str(adapter_result["status"]),
            observed={
                "aggregate_adapter_bridge_id": adapter_result["bridge_id"],
                "consumer_module": adapter_result["consumer_module"],
                "action_kind": adapter_result["action_kind"],
                "profile_id": adapter_result["profile_id"],
            },
        )
    )
    if adapter_result["status"] != "accepted":
        errors.extend(f"action_adapter:{error}" for error in adapter_result["errors"])

    terminal_result = verify_bundle(aggregate_read["receipt_bundle"]).to_json_obj()
    stages.append(
        _stage(
            "terminal_dag_replay",
            ok=terminal_result["status"] == "accepted",
            status=str(terminal_result["status"]),
            observed={
                "read_receipt_id": terminal_result["read_receipt_id"],
                "consumer_action_receipt_id": terminal_result["consumer_action_receipt_id"],
                "evidence_class": terminal_result["evidence_class"],
            },
        )
    )
    if terminal_result["status"] != "accepted":
        errors.extend(f"terminal_dag:{error}" for error in terminal_result["errors"])

    if str(feed["query_spec"]["query_id"]) != aggregate_result.get("query_id"):
        errors.append("feed_registry_query_does_not_match_aggregate")
    if terminal_result.get("read_receipt_id") != read_result.get("read_receipt_id"):
        errors.append("terminal_read_receipt_does_not_match_accepted_read")
    if terminal_result.get("consumer_action_receipt_id") != read_result.get("consumer_action_receipt_id"):
        errors.append("terminal_action_receipt_does_not_match_accepted_read")

    failed_stages = [stage["name"] for stage in stages if not stage["ok"]]
    return {
        "schema": RESULT_SCHEMA,
        "ok": not errors and not failed_stages,
        "status": "accepted" if not errors and not failed_stages else "rejected",
        "stage_count": len(stages),
        "accepted_stage_count": len(stages) - len(failed_stages),
        "failed_stage_count": len(failed_stages),
        "stages": stages,
        "query_id": aggregate_result.get("query_id"),
        "aggregate_id": aggregate_result.get("aggregate_id"),
        "read_receipt_id": terminal_result.get("read_receipt_id"),
        "consumer_action_receipt_id": terminal_result.get("consumer_action_receipt_id"),
        "replay_command": REPLAY_COMMAND,
        "errors": errors,
        "not_claimed": NOT_CLAIMED,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--output", help="optional output path for the JSON receipt")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    receipt = build_o3_receipt_flow_replay()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    if args.format == "json":
        sys.stdout.write(text)
    else:
        sys.stdout.write(
            "\n".join(
                [
                    f"schema = {receipt['schema']}",
                    f"stage_count = {receipt['stage_count']}",
                    f"accepted_stage_count = {receipt['accepted_stage_count']}",
                    f"failed_stage_count = {receipt['failed_stage_count']}",
                    f"status = {receipt['status']}",
                ]
            )
            + "\n"
        )
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
