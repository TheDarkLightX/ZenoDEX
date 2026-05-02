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
from zenodex_oracle_adapter import (  # noqa: E402
    profile_content_hash,
    sample_action_and_bundle,
    sample_action_bundle_profile,
    verify_oracle_use,
)


def base_pair() -> tuple[dict[str, Any], dict[str, Any]]:
    return sample_action_and_bundle()


def base_triple() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    return sample_action_bundle_profile()


def _mutate(
    mutator: Callable[[dict[str, Any], dict[str, Any]], None]
) -> tuple[dict[str, Any], dict[str, Any]]:
    action, bundle = base_pair()
    action = copy.deepcopy(action)
    bundle = copy.deepcopy(bundle)
    mutator(action, bundle)
    return action, bundle


def _mutate_profile(
    mutator: Callable[[dict[str, Any], dict[str, Any], dict[str, Any]], None]
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    action, bundle, profile = base_triple()
    action = copy.deepcopy(action)
    bundle = copy.deepcopy(bundle)
    profile = copy.deepcopy(profile)
    mutator(action, bundle, profile)
    return action, bundle, profile


def _refresh_profile_id(profile: dict[str, Any]) -> None:
    profile["profile_id"] = profile_content_hash(profile)


def adapter_chaos_cases() -> list[tuple[str, dict[str, Any], dict[str, Any], dict[str, Any] | None, list[str]]]:
    return [
        (
            "unaccepted_bundle_survives",
            *_mutate(lambda _a, b: b["receipts"][0].__setitem__("fresh", False)),
            None,
            ["oracle_bundle_not_accepted", "bundle:"],
        ),
        (
            "consumer_module_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("consumer_module", "zenodex.perps")),
            None,
            ["adapter_consumer_module_mismatch"],
        ),
        (
            "action_kind_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("action_kind", "settle_epoch")),
            None,
            ["adapter_action_kind_mismatch"],
        ),
        (
            "action_id_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("action_id", sample_hash("other-action"))),
            None,
            ["adapter_action_id_mismatch"],
        ),
        (
            "action_epoch_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("action_epoch", a["action_epoch"] + 1)),
            None,
            ["adapter_action_epoch_mismatch"],
        ),
        (
            "query_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("query_id", sample_hash("other-query"))),
            None,
            ["adapter_query_id_mismatch"],
        ),
        (
            "value_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("value_hash", sample_hash("other-value"))),
            None,
            ["adapter_value_hash_mismatch"],
        ),
        (
            "read_receipt_id_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("read_receipt_id", sample_hash("other-read"))),
            None,
            ["adapter_read_receipt_id_mismatch"],
        ),
        (
            "consumer_action_receipt_id_mismatch_survives",
            *_mutate(lambda a, _b: a.__setitem__("consumer_action_receipt_id", sample_hash("other-action-receipt"))),
            None,
            ["adapter_consumer_action_receipt_id_mismatch"],
        ),
        (
            "evidence_below_action_floor_survives",
            *_mutate(lambda a, _b: a.__setitem__("required_evidence_floor", "O4")),
            None,
            ["adapter_evidence_below_required_floor"],
        ),
        (
            "freshness_window_exceeds_action_limit_survives",
            *_mutate(lambda a, _b: a.__setitem__("max_freshness_window_epochs", 3)),
            None,
            ["adapter_freshness_window_exceeds_action_limit"],
        ),
        (
            "noncritical_action_descriptor_survives",
            *_mutate(lambda a, _b: a.__setitem__("critical", False)),
            None,
            ["action_must_be_critical"],
        ),
        (
            "weak_required_evidence_floor_survives",
            *_mutate(lambda a, _b: a.__setitem__("required_evidence_floor", "O2")),
            None,
            ["required_evidence_floor_below_critical_minimum"],
        ),
        (
            "hidden_action_field_survives",
            *_mutate(lambda a, _b: a.__setitem__("admin_override", True)),
            None,
            ["unknown_action_field:admin_override"],
        ),
        (
            "wrong_action_schema_survives",
            *_mutate(lambda a, _b: a.__setitem__("schema", "zenodex.oracle.consumer_action_binding.v0")),
            None,
            ["action_schema_mismatch"],
        ),
        (
            "missing_action_id_survives",
            *_mutate(lambda a, _b: a.pop("action_id")),
            None,
            ["action_id_must_be_sha256"],
        ),
        (
            "boolean_action_epoch_survives",
            *_mutate(lambda a, _b: a.__setitem__("action_epoch", True)),
            None,
            ["action_epoch_must_be_int_ge_0"],
        ),
        (
            "profile_content_hash_forgery_survives",
            *_mutate_profile(lambda _a, _b, p: p.__setitem__("max_freshness_window_epochs", 3)),
            ["profile_content_hash_mismatch"],
        ),
        (
            "profile_consumer_module_mismatch_survives",
            *_mutate_profile(
                lambda _a, _b, p: (
                    p.__setitem__("consumer_module", "zenodex.perps"),
                    _refresh_profile_id(p),
                )
            ),
            ["profile_consumer_module_mismatch"],
        ),
        (
            "profile_action_kind_mismatch_survives",
            *_mutate_profile(
                lambda _a, _b, p: (
                    p.__setitem__("action_kind", "settle_epoch"),
                    _refresh_profile_id(p),
                )
            ),
            ["profile_action_kind_mismatch"],
        ),
        (
            "profile_query_mismatch_survives",
            *_mutate_profile(
                lambda _a, _b, p: (
                    p.__setitem__("query_id", sample_hash("other-query")),
                    _refresh_profile_id(p),
                )
            ),
            ["profile_query_id_mismatch"],
        ),
        (
            "action_evidence_floor_below_profile_survives",
            *_mutate_profile(
                lambda _a, _b, p: (
                    p.__setitem__("required_evidence_floor", "O4"),
                    _refresh_profile_id(p),
                )
            ),
            ["action_evidence_floor_below_profile"],
        ),
        (
            "action_freshness_window_exceeds_profile_survives",
            *_mutate_profile(
                lambda _a, _b, p: (
                    p.__setitem__("max_freshness_window_epochs", 3),
                    _refresh_profile_id(p),
                )
            ),
            ["action_freshness_window_exceeds_profile"],
        ),
        (
            "noncritical_profile_survives",
            *_mutate_profile(
                lambda _a, _b, p: (
                    p.__setitem__("critical", False),
                    _refresh_profile_id(p),
                )
            ),
            ["profile_must_be_critical"],
        ),
        (
            "hidden_profile_field_survives",
            *_mutate_profile(
                lambda _a, _b, p: (
                    p.__setitem__("admin_override", True),
                    _refresh_profile_id(p),
                )
            ),
            ["unknown_profile_field:admin_override"],
        ),
        (
            "weak_profile_evidence_floor_survives",
            *_mutate_profile(
                lambda _a, _b, p: (
                    p.__setitem__("required_evidence_floor", "O2"),
                    _refresh_profile_id(p),
                )
            ),
            ["profile_required_evidence_floor_below_critical_minimum"],
        ),
        (
            "wrong_profile_schema_survives",
            *_mutate_profile(
                lambda _a, _b, p: (
                    p.__setitem__("schema", "zenodex.oracle.consumer_profile.v0"),
                    _refresh_profile_id(p),
                )
            ),
            ["profile_schema_mismatch"],
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
    for name, action, bundle, profile, expected_fragments in adapter_chaos_cases():
        result = verify_oracle_use(action, bundle, profile)
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
