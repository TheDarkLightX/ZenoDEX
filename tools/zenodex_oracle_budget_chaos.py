#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Zeno Oracle budget verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_budget import sample_budget_transition, verify_budget_transition  # noqa: E402


def base_transition() -> dict[str, Any]:
    return sample_budget_transition()


def _mutate(mutator: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    transition = copy.deepcopy(base_transition())
    mutator(transition)
    return transition


def budget_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "query_reward_exceeds_remaining_budget",
            _mutate(lambda t: t.__setitem__("query_reward_paid", t["query_budget_remaining"] + 1)),
            ["query_reward_exceeds_budget"],
        ),
        (
            "query_reward_from_zero_budget",
            _mutate(
                lambda t: (
                    t.__setitem__("query_budget_remaining", 0),
                    t.__setitem__("query_reward_paid", 1),
                )
            ),
            ["query_reward_exceeds_budget"],
        ),
        (
            "reporter_slash_exceeds_available_bond",
            _mutate(lambda t: t.__setitem__("reporter_slash_paid", t["reporter_bond_available"] + 1)),
            ["reporter_slash_exceeds_bond"],
        ),
        (
            "dispute_slash_exceeds_available_bond",
            _mutate(lambda t: t.__setitem__("dispute_slash_paid", t["dispute_bond_available"] + 1)),
            ["dispute_slash_exceeds_bond"],
        ),
        (
            "fee_split_spends_more_than_fee",
            _mutate(lambda t: t.__setitem__("burn_fee_share", t["burn_fee_share"] + 1)),
            ["fee_shares_exceed_fee_paid"],
        ),
        (
            "fee_split_spends_from_zero_fee",
            _mutate(
                lambda t: (
                    t.__setitem__("fee_paid", 0),
                    t.__setitem__("reporter_fee_share", 1),
                    t.__setitem__("treasury_fee_share", 0),
                    t.__setitem__("burn_fee_share", 0),
                )
            ),
            ["fee_shares_exceed_fee_paid"],
        ),
        (
            "hidden_mint_field_survives",
            _mutate(lambda t: t.__setitem__("hidden_mint", 1)),
            ["unknown_budget_field:hidden_mint"],
        ),
        (
            "negative_reward_amount_survives",
            _mutate(lambda t: t.__setitem__("query_reward_paid", -1)),
            ["query_reward_paid_must_be_int_ge_0"],
        ),
        (
            "boolean_burn_share_survives",
            _mutate(lambda t: t.__setitem__("burn_fee_share", True)),
            ["burn_fee_share_must_be_int_ge_0"],
        ),
        (
            "missing_fee_share_survives",
            _mutate(lambda t: t.pop("burn_fee_share")),
            ["burn_fee_share_must_be_int_ge_0"],
        ),
        (
            "wrong_schema_survives",
            _mutate(lambda t: t.__setitem__("schema", "zenodex.oracle.budget_transition.v0")),
            ["budget_schema_mismatch"],
        ),
        (
            "string_budget_amount_survives",
            _mutate(lambda t: t.__setitem__("query_budget_remaining", "1000")),
            ["query_budget_remaining_must_be_int_ge_0"],
        ),
    ]


@dataclass(frozen=True)
class BudgetChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_budget_chaos() -> dict[str, Any]:
    baseline = verify_budget_transition(base_transition())
    results: list[BudgetChaosCaseResult] = []
    for name, transition, expected_fragments in budget_chaos_cases():
        result = verify_budget_transition(transition)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            BudgetChaosCaseResult(
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
        "schema": "zenodex.oracle.budget_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the budget chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_budget_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
