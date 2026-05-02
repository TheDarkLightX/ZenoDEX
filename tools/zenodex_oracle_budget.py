#!/usr/bin/env python3
"""Verify first-shell Zeno Oracle token budget transitions."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


BUDGET_SCHEMA = "zenodex.oracle.budget_transition.v1"
RESULT_SCHEMA = "zenodex.oracle.budget_verify_result.v1"
MAX_BUDGET_BYTES = 250_000
BUDGET_KEYS = {
    "schema",
    "query_budget_remaining",
    "query_reward_paid",
    "reporter_bond_available",
    "reporter_slash_paid",
    "dispute_bond_available",
    "dispute_slash_paid",
    "fee_paid",
    "reporter_fee_share",
    "treasury_fee_share",
    "burn_fee_share",
}
INT_FIELDS = {
    "query_budget_remaining",
    "query_reward_paid",
    "reporter_bond_available",
    "reporter_slash_paid",
    "dispute_bond_available",
    "dispute_slash_paid",
    "fee_paid",
    "reporter_fee_share",
    "treasury_fee_share",
    "burn_fee_share",
}
NOT_CLAIMED = [
    "does_not_claim_token_price_appreciation",
    "does_not_claim_reporter_honesty",
    "does_not_claim_production_oracle_token_live",
]


@dataclass(frozen=True)
class BudgetVerifyResult:
    status: str
    errors: list[str]
    query_reward_paid: int | None = None
    reporter_slash_paid: int | None = None
    dispute_slash_paid: int | None = None
    fee_paid: int | None = None
    fee_spend_total: int | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "query_reward_paid": self.query_reward_paid,
            "reporter_slash_paid": self.reporter_slash_paid,
            "dispute_slash_paid": self.dispute_slash_paid,
            "fee_paid": self.fee_paid,
            "fee_spend_total": self.fee_spend_total,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def sample_budget_transition() -> dict[str, Any]:
    return {
        "schema": BUDGET_SCHEMA,
        "query_budget_remaining": 1_000,
        "query_reward_paid": 250,
        "reporter_bond_available": 2_000,
        "reporter_slash_paid": 100,
        "dispute_bond_available": 500,
        "dispute_slash_paid": 50,
        "fee_paid": 300,
        "reporter_fee_share": 120,
        "treasury_fee_share": 90,
        "burn_fee_share": 90,
    }


def _unknown_fields(obj: Mapping[str, Any], errors: list[str]) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append("budget_field_must_be_string")
        elif key not in BUDGET_KEYS:
            errors.append(f"unknown_budget_field:{key}")


def _int_ge_zero(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        errors.append(f"{key}_must_be_int_ge_0")
        return None
    return int(value)


def verify_budget_transition(obj: Mapping[str, Any]) -> BudgetVerifyResult:
    errors: list[str] = []
    _unknown_fields(obj, errors)
    if obj.get("schema") != BUDGET_SCHEMA:
        errors.append("budget_schema_mismatch")

    values = {key: _int_ge_zero(obj, key, errors) for key in sorted(INT_FIELDS)}
    query_budget_remaining = values["query_budget_remaining"]
    query_reward_paid = values["query_reward_paid"]
    reporter_bond_available = values["reporter_bond_available"]
    reporter_slash_paid = values["reporter_slash_paid"]
    dispute_bond_available = values["dispute_bond_available"]
    dispute_slash_paid = values["dispute_slash_paid"]
    fee_paid = values["fee_paid"]
    reporter_fee_share = values["reporter_fee_share"]
    treasury_fee_share = values["treasury_fee_share"]
    burn_fee_share = values["burn_fee_share"]

    if (
        query_reward_paid is not None
        and query_budget_remaining is not None
        and query_reward_paid > query_budget_remaining
    ):
        errors.append("query_reward_exceeds_budget")
    if (
        reporter_slash_paid is not None
        and reporter_bond_available is not None
        and reporter_slash_paid > reporter_bond_available
    ):
        errors.append("reporter_slash_exceeds_bond")
    if (
        dispute_slash_paid is not None
        and dispute_bond_available is not None
        and dispute_slash_paid > dispute_bond_available
    ):
        errors.append("dispute_slash_exceeds_bond")

    fee_spend_total: int | None = None
    if reporter_fee_share is not None and treasury_fee_share is not None and burn_fee_share is not None:
        fee_spend_total = reporter_fee_share + treasury_fee_share + burn_fee_share
        if fee_paid is not None and fee_spend_total > fee_paid:
            errors.append("fee_shares_exceed_fee_paid")

    return BudgetVerifyResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        query_reward_paid=query_reward_paid,
        reporter_slash_paid=reporter_slash_paid,
        dispute_slash_paid=dispute_slash_paid,
        fee_paid=fee_paid,
        fee_spend_total=fee_spend_total,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_BUDGET_BYTES:
        raise ValueError(f"budget_file_too_large:{size}>{MAX_BUDGET_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("budget root must be a JSON object")
    return obj


def _write_result(result: BudgetVerifyResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        transition = _load_json(Path(args.transition))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = BudgetVerifyResult(status="inconclusive", errors=[f"budget_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_budget_transition(transition)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_budget_transition(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an Oracle budget transition JSON file")
    verify.add_argument("transition", help="path to a budget transition JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted Oracle budget transition")
    sample.add_argument("--output", help="optional output path for the sample transition JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
