#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Zeno Oracle verifier shell."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle import sample_hash, sample_bundle, verify_bundle  # noqa: E402


def base_bundle() -> dict[str, Any]:
    return sample_bundle()


def _mutate(mutator: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    bundle = copy.deepcopy(base_bundle())
    mutator(bundle)
    return bundle


def _read(bundle: dict[str, Any]) -> dict[str, Any]:
    return next(
        receipt
        for receipt in bundle["receipts"]
        if receipt.get("type") == "accepted_read_receipt"
    )


def _action(bundle: dict[str, Any]) -> dict[str, Any]:
    return next(
        receipt
        for receipt in bundle["receipts"]
        if receipt.get("type") == "consumer_action_receipt"
    )


def chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "weak_o2_evidence_used_for_critical_action",
            _mutate(lambda b: _read(b).__setitem__("evidence_class", "O2")),
            ["critical_read_requires_o3_or_higher"],
        ),
        (
            "stale_read_used_for_critical_action",
            _mutate(lambda b: _read(b).__setitem__("fresh", False)),
            ["read_fresh_required"],
        ),
        (
            "open_dispute_used_for_critical_action",
            _mutate(lambda b: _read(b).__setitem__("dispute_clear", False)),
            ["read_dispute_clear_required"],
        ),
        (
            "high_uncertainty_erased_before_action",
            _mutate(lambda b: _read(b).__setitem__("uncertainty_accepted", False)),
            ["read_uncertainty_accepted_required"],
        ),
        (
            "consumer_action_borrows_other_query",
            _mutate(lambda b: _action(b).__setitem__("query_id", sample_hash("other-query"))),
            ["consumer_action_query_id_mismatch"],
        ),
        (
            "consumer_action_borrows_other_value",
            _mutate(lambda b: _action(b).__setitem__("value_hash", sample_hash("other-value"))),
            ["consumer_action_value_hash_mismatch"],
        ),
        (
            "consumer_action_drops_read_dependency",
            _mutate(lambda b: _action(b).__setitem__("depends_on", [])),
            ["consumer_action_must_depend_on_read_receipt"],
        ),
        (
            "emergency_oracle_bypass_flag_set",
            _mutate(lambda b: _action(b).__setitem__("emergency_oracle_bypass", True)),
            ["emergency_oracle_bypass_rejected"],
        ),
        (
            "terminal_points_to_missing_read",
            _mutate(lambda b: b["terminal"].__setitem__("read_receipt_id", sample_hash("missing-read"))),
            ["terminal_read_receipt_missing"],
        ),
        (
            "action_depends_on_missing_receipt",
            _mutate(lambda b: _action(b).__setitem__("depends_on", [sample_hash("missing-dependency")])),
            ["missing_dependency"],
        ),
        (
            "duplicate_receipt_id_shadows_terminal",
            _mutate(lambda b: b["receipts"].append(copy.deepcopy(b["receipts"][0]))),
            ["duplicate_receipt_id"],
        ),
        (
            "stray_receipt_hides_unreachable_evidence",
            _mutate(
                lambda b: b["receipts"].append(
                    {
                        "id": sample_hash("stray-receipt"),
                        "type": "accepted_read_receipt",
                        "status": "accepted",
                        "query_id": sample_hash("stray-query"),
                        "value_hash": sample_hash("stray-value"),
                        "evidence_class": "O3",
                        "fresh": True,
                        "dispute_clear": True,
                        "uncertainty_accepted": True,
                        "depends_on": [],
                    }
                )
            ),
            ["unreachable_receipt"],
        ),
        (
            "unsupported_receipt_type_in_terminal_closure",
            _mutate(
                lambda b: (
                    b["receipts"].insert(
                        0,
                        {
                            "id": sample_hash("unsupported-receipt"),
                            "type": "unsupported_source_receipt",
                            "status": "accepted",
                            "depends_on": [],
                        },
                    ),
                    _action(b).__setitem__(
                        "depends_on",
                        [sample_hash("zenodex-oracle-sample-read"), sample_hash("unsupported-receipt")],
                    ),
                )
            ),
            ["unsupported_receipt_type"],
        ),
        (
            "dependency_consumed_before_it_appears",
            _mutate(lambda b: b["receipts"].reverse()),
            ["dependency_order_violation"],
        ),
        (
            "read_receipt_depends_on_itself",
            _mutate(lambda b: _read(b).__setitem__("depends_on", [_read(b)["id"]])),
            ["dependency_self_reference"],
        ),
        (
            "read_receipt_status_downgraded_after_terminal_binding",
            _mutate(lambda b: _read(b).__setitem__("status", "pending")),
            ["read_receipt_not_accepted"],
        ),
    ]


@dataclass(frozen=True)
class ChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_chaos() -> dict[str, Any]:
    baseline = verify_bundle(base_bundle())
    results: list[ChaosCaseResult] = []
    for name, bundle, expected_fragments in chaos_cases():
        result = verify_bundle(bundle)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            ChaosCaseResult(
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
        "schema": "zenodex.oracle.chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
