#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Oracle economic security verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_economic_security import (  # noqa: E402
    sample_envelope,
    verify_economic_security_envelope,
)


def base_envelope() -> dict[str, Any]:
    return sample_envelope()


def _mutate(mutator: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    envelope = copy.deepcopy(base_envelope())
    mutator(envelope)
    return envelope


def economic_security_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "extractable_above_notional_survives",
            _mutate(lambda e: e.__setitem__("max_extractable_value_e8", e["notional_value_e8"] + 1)),
            ["extractable_value_exceeds_notional"],
        ),
        (
            "attack_cost_below_margin_survives",
            _mutate(lambda e: e.__setitem__("attack_cost_floor_e8", 59_999_999_999)),
            ["attack_cost_floor_below_required_margin"],
        ),
        (
            "reward_below_honest_cost_survives",
            _mutate(lambda e: e.__setitem__("reporter_reward_per_report_e8", 24_999_999)),
            ["reporter_reward_below_honest_cost_plus_risk"],
        ),
        (
            "reporter_reward_budget_overspend_survives",
            _mutate(lambda e: e.__setitem__("reporter_reward_budget_e8", 89_999_999)),
            ["reporter_reward_budget_exceeded"],
        ),
        (
            "cheat_gain_above_extractable_survives",
            _mutate(lambda e: e.__setitem__("expected_cheat_gain_e8", e["max_extractable_value_e8"] + 1)),
            ["expected_cheat_gain_exceeds_extractable_value"],
        ),
        (
            "weak_slash_deterrence_survives",
            _mutate(lambda e: e.__setitem__("slash_fraction_bps", 1_000)),
            ["slash_deterrence_below_required_margin"],
        ),
        (
            "dispute_reward_budget_overspend_survives",
            _mutate(lambda e: e.__setitem__("dispute_reward_e8", e["dispute_budget_e8"] + 1)),
            ["dispute_reward_budget_exceeded"],
        ),
        (
            "fee_split_overspend_survives",
            _mutate(lambda e: e.__setitem__("burn_fee_share_e8", e["burn_fee_share_e8"] + 1)),
            ["fee_shares_exceed_fee_paid"],
        ),
        (
            "hidden_mint_field_survives",
            _mutate(lambda e: e.__setitem__("hidden_mint", 1)),
            ["unknown_economic_security_field:hidden_mint"],
        ),
        (
            "boolean_attack_cost_survives",
            _mutate(lambda e: e.__setitem__("attack_cost_floor_e8", True)),
            ["attack_cost_floor_e8_must_be_int_between_0_and_1000000000000000000000000000000"],
        ),
        (
            "wrong_schema_survives",
            _mutate(lambda e: e.__setitem__("schema", "zenodex.oracle.economic_security_envelope.v0")),
            ["economic_security_schema_mismatch"],
        ),
        (
            "zero_reporter_count_survives",
            _mutate(lambda e: e.__setitem__("reporter_count", 0)),
            ["reporter_count_must_be_int_between_1_and_1024"],
        ),
        (
            "slash_fraction_over_100_percent_survives",
            _mutate(lambda e: e.__setitem__("slash_fraction_bps", 10_001)),
            ["slash_fraction_bps_must_be_int_between_0_and_10000"],
        ),
        (
            "negative_fee_share_survives",
            _mutate(lambda e: e.__setitem__("treasury_fee_share_e8", -1)),
            ["treasury_fee_share_e8_must_be_int_between_0_and_1000000000000000000000000000000"],
        ),
    ]


@dataclass(frozen=True)
class EconomicSecurityChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_economic_security_chaos() -> dict[str, Any]:
    baseline = verify_economic_security_envelope(base_envelope())
    results: list[EconomicSecurityChaosCaseResult] = []
    for name, envelope, expected_fragments in economic_security_chaos_cases():
        result = verify_economic_security_envelope(envelope)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            EconomicSecurityChaosCaseResult(
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
        "schema": "zenodex.oracle.economic_security_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the economic security chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_economic_security_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
