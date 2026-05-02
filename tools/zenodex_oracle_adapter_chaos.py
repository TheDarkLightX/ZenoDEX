#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Zeno Oracle adapter verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle import sample_hash  # noqa: E402
from zenodex_oracle_adapter import sample_action_and_bundle, verify_oracle_use  # noqa: E402


def base_pair() -> tuple[dict[str, Any], dict[str, Any]]:
    return sample_action_and_bundle()


def _mutate(
    mutator: Callable[[dict[str, Any], dict[str, Any]], None]
) -> tuple[dict[str, Any], dict[str, Any]]:
    action, bundle = base_pair()
    action = copy.deepcopy(action)
    bundle = copy.deepcopy(bundle)
    mutator(action, bundle)
    return action, bundle


def adapter_chaos_cases() -> list[tuple[str, dict[str, Any], dict[str, Any], list[str]]]:
    return [
        (
            "unaccepted_bundle_survives",
            *_mutate(lambda _a, b: b["receipts"][0].__setitem__("fresh", False)),
            ["oracle_bundle_not_accepted", "bundle:"],
        ),
        (
            "consumer_module_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("consumer_module", "zenodex.perps")),
            ["adapter_consumer_module_mismatch"],
        ),
        (
            "action_kind_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("action_kind", "settle_epoch")),
            ["adapter_action_kind_mismatch"],
        ),
        (
            "action_id_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("action_id", sample_hash("other-action"))),
            ["adapter_action_id_mismatch"],
        ),
        (
            "action_epoch_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("action_epoch", a["action_epoch"] + 1)),
            ["adapter_action_epoch_mismatch"],
        ),
        (
            "query_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("query_id", sample_hash("other-query"))),
            ["adapter_query_id_mismatch"],
        ),
        (
            "value_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("value_hash", sample_hash("other-value"))),
            ["adapter_value_hash_mismatch"],
        ),
        (
            "read_receipt_id_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("read_receipt_id", sample_hash("other-read"))),
            ["adapter_read_receipt_id_mismatch"],
        ),
        (
            "consumer_action_receipt_id_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("consumer_action_receipt_id", sample_hash("other-action-receipt"))),
            ["adapter_consumer_action_receipt_id_mismatch"],
        ),
        (
            "evidence_below_action_floor_survives",
            *_mutate(lambda a, _b: a.__setitem__("required_evidence_floor", "O4")),
            ["adapter_evidence_below_required_floor"],
        ),
        (
            "freshness_window_exceeds_action_limit_survives",
            *_mutate(lambda a, _b: a.__setitem__("max_freshness_window_epochs", 3)),
            ["adapter_freshness_window_exceeds_action_limit"],
        ),
        (
            "noncritical_action_descriptor_survives",
            *_mutate(lambda a, _b: a.__setitem__("critical", False)),
            ["action_must_be_critical"],
        ),
        (
            "weak_required_evidence_floor_survives",
            *_mutate(lambda a, _b: a.__setitem__("required_evidence_floor", "O2")),
            ["required_evidence_floor_below_critical_minimum"],
        ),
        (
            "hidden_action_field_survives",
            *_mutate(lambda a, _b: a.__setitem__("admin_override", True)),
            ["unknown_action_field:admin_override"],
        ),
        (
            "wrong_action_schema_survives",
            *_mutate(lambda a, _b: a.__setitem__("schema", "zenodex.oracle.consumer_action_binding.v0")),
            ["action_schema_mismatch"],
        ),
        (
            "missing_action_id_survives",
            *_mutate(lambda a, _b: a.pop("action_id")),
            ["action_id_must_be_sha256"],
        ),
        (
            "boolean_action_epoch_survives",
            *_mutate(lambda a, _b: a.__setitem__("action_epoch", True)),
            ["action_epoch_must_be_int_ge_0"],
        ),
    ]


@dataclass(frozen=True)
class AdapterChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_adapter_chaos() -> dict[str, Any]:
    baseline_action, baseline_bundle = base_pair()
    baseline = verify_oracle_use(baseline_action, baseline_bundle)
    results: list[AdapterChaosCaseResult] = []
    for name, action, bundle, expected_fragments in adapter_chaos_cases():
        result = verify_oracle_use(action, bundle)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            AdapterChaosCaseResult(
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
        "schema": "zenodex.oracle.adapter_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the adapter chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_adapter_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
