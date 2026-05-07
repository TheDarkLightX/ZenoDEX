#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Zeno Oracle reporter lifecycle verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_reporter_lifecycle import (  # noqa: E402
    sample_hash,
    sample_lifecycle,
    verify_lifecycle_trace,
)


def base_lifecycle() -> dict[str, Any]:
    return sample_lifecycle()


def _mutate(mutator: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    trace = copy.deepcopy(base_lifecycle())
    mutator(trace)
    return trace


def _report_id(trace: dict[str, Any]) -> str:
    return next(event["report_id"] for event in trace["events"] if event.get("type") == "submit_report")


def _dispute_id(trace: dict[str, Any]) -> str:
    return next(event["dispute_id"] for event in trace["events"] if event.get("type") == "open_dispute")


def _duplicate_report(trace: dict[str, Any]) -> None:
    event = copy.deepcopy(next(event for event in trace["events"] if event.get("type") == "submit_report"))
    event["epoch"] = 4
    trace["events"].insert(3, event)


def _double_slash(trace: dict[str, Any]) -> None:
    event = copy.deepcopy(next(event for event in trace["events"] if event.get("type") == "slash"))
    event["epoch"] = 6
    trace["events"].insert(5, event)


def lifecycle_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "duplicate_reporter_registration",
            _mutate(lambda t: t["events"].insert(1, {"type": "register", "epoch": 2})),
            ["reporter_already_active", "reporter_duplicate_registration"],
        ),
        (
            "bond_deposit_before_registration",
            {
                "schema": "zenodex.oracle.reporter_lifecycle.v1",
                "reporter_id": "reporter.sample",
                "required_bond": 100,
                "events": [{"type": "deposit_bond", "epoch": 1, "amount": 100}],
            },
            ["bond_deposit_before_registration"],
        ),
        (
            "report_before_registration",
            {
                "schema": "zenodex.oracle.reporter_lifecycle.v1",
                "reporter_id": "reporter.sample",
                "required_bond": 100,
                "events": [
                    {
                        "type": "submit_report",
                        "epoch": 1,
                        "report_id": sample_hash("early-report"),
                        "query_id": sample_hash("query"),
                        "value_hash": sample_hash("value"),
                    }
                ],
            },
            ["report_submitted_by_inactive_reporter", "report_submitted_under_required_bond"],
        ),
        (
            "report_under_required_bond",
            _mutate(lambda t: t["events"][1].__setitem__("amount", 99)),
            ["report_submitted_under_required_bond"],
        ),
        (
            "duplicate_report_id_survives",
            _mutate(_duplicate_report),
            ["duplicate_report_id"],
        ),
        (
            "dispute_for_unknown_report",
            _mutate(lambda t: t["events"][3].__setitem__("report_id", sample_hash("missing-report"))),
            ["dispute_for_unknown_report"],
        ),
        (
            "zero_dispute_bond_survives",
            _mutate(lambda t: t["events"][3].__setitem__("dispute_bond", 0)),
            ["dispute_bond_required"],
        ),
        (
            "slash_without_open_dispute",
            _mutate(lambda t: t["events"][4].__setitem__("dispute_id", sample_hash("missing-dispute"))),
            ["slash_without_open_dispute"],
        ),
        (
            "slash_exceeds_reporter_bond",
            _mutate(lambda t: t["events"][4].__setitem__("amount", 101)),
            ["slash_exceeds_reporter_bond"],
        ),
        (
            "double_slash_same_dispute",
            _mutate(_double_slash),
            ["dispute_already_slashed"],
        ),
        (
            "resolve_unknown_dispute",
            _mutate(lambda t: t["events"][5].__setitem__("dispute_id", sample_hash("missing-dispute"))),
            ["resolve_unknown_dispute"],
        ),
        (
            "unregister_with_open_dispute",
            _mutate(lambda t: t.__setitem__("events", t["events"][:4] + [{"type": "unregister", "epoch": 5}])),
            ["unregister_with_open_dispute"],
        ),
        (
            "withdraw_while_active",
            _mutate(lambda t: t.__setitem__("events", t["events"][:2] + [{"type": "withdraw_bond", "epoch": 3, "amount": 1}])),
            ["withdraw_while_reporter_active"],
        ),
        (
            "withdraw_with_open_dispute",
            _mutate(lambda t: t.__setitem__("events", t["events"][:4] + [{"type": "withdraw_bond", "epoch": 5, "amount": 1}])),
            ["withdraw_while_reporter_active", "withdraw_with_open_dispute"],
        ),
        (
            "withdraw_exceeds_bond",
            _mutate(lambda t: t["events"][7].__setitem__("amount", 91)),
            ["withdraw_exceeds_bond"],
        ),
        (
            "event_epoch_regression",
            _mutate(lambda t: t["events"][1].__setitem__("epoch", 0)),
            ["event_epoch_regression"],
        ),
        (
            "hidden_event_field_survives",
            _mutate(lambda t: t["events"][0].__setitem__("admin_override", True)),
            ["unknown_event_register_field:admin_override"],
        ),
        (
            "unknown_event_type_survives",
            _mutate(lambda t: t["events"].insert(2, {"type": "force_activate", "epoch": 3})),
            ["unsupported_event_type:force_activate"],
        ),
        (
            "boolean_bond_amount_survives",
            _mutate(lambda t: t["events"][1].__setitem__("amount", True)),
            ["amount_must_be_int_between_0_and_1000000000000000000000000"],
        ),
        (
            "too_many_events_survive",
            _mutate(lambda t: t.__setitem__("events", [{"type": "register", "epoch": i} for i in range(65)])),
            ["events_exceed_max"],
        ),
    ]


@dataclass(frozen=True)
class LifecycleChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_lifecycle_chaos() -> dict[str, Any]:
    baseline = verify_lifecycle_trace(base_lifecycle())
    results: list[LifecycleChaosCaseResult] = []
    for name, trace, expected_fragments in lifecycle_chaos_cases():
        result = verify_lifecycle_trace(trace)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            LifecycleChaosCaseResult(
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
        "schema": "zenodex.oracle.reporter_lifecycle_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the lifecycle chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_lifecycle_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
