#!/usr/bin/env python3
"""Verify first-shell Zeno Oracle economic security envelopes."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


ENVELOPE_SCHEMA = "zenodex.oracle.economic_security_envelope.v1"
RESULT_SCHEMA = "zenodex.oracle.economic_security_verify_result.v1"
MAX_ENVELOPE_BYTES = 250_000
MAX_AMOUNT = 10**30
MAX_COUNT = 1024
BPS_SCALE = 10_000
MAX_MARGIN_BPS = 1_000_000
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
ENVELOPE_KEYS = {
    "schema",
    "query_id",
    "consumer_module",
    "action_kind",
    "notional_value_e8",
    "max_extractable_value_e8",
    "attack_cost_floor_e8",
    "required_attack_margin_bps",
    "reporter_count",
    "reporter_reward_budget_e8",
    "reporter_reward_per_report_e8",
    "honest_reporter_cost_e8",
    "honest_reporter_risk_premium_e8",
    "reporter_bond_required_e8",
    "slash_fraction_bps",
    "expected_cheat_gain_e8",
    "deterrence_margin_bps",
    "dispute_reward_e8",
    "dispute_budget_e8",
    "fee_paid_e8",
    "reporter_fee_share_e8",
    "treasury_fee_share_e8",
    "burn_fee_share_e8",
}
NOT_CLAIMED = [
    "does_not_claim_token_price_appreciation",
    "does_not_claim_market_price_truth",
    "does_not_claim_reporter_honesty",
    "does_not_claim_attack_cost_estimate_is_correct",
    "does_not_claim_production_oracle_network_live",
]


@dataclass(frozen=True)
class EconomicSecurityResult:
    status: str
    errors: list[str]
    query_id: str | None = None
    consumer_module: str | None = None
    action_kind: str | None = None
    required_attack_cost_e8: int | None = None
    required_reporter_reward_per_report_e8: int | None = None
    total_reporter_reward_e8: int | None = None
    slash_amount_e8: int | None = None
    required_deterrence_slash_e8: int | None = None
    fee_spend_total_e8: int | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "query_id": self.query_id,
            "consumer_module": self.consumer_module,
            "action_kind": self.action_kind,
            "required_attack_cost_e8": self.required_attack_cost_e8,
            "required_reporter_reward_per_report_e8": self.required_reporter_reward_per_report_e8,
            "total_reporter_reward_e8": self.total_reporter_reward_e8,
            "slash_amount_e8": self.slash_amount_e8,
            "required_deterrence_slash_e8": self.required_deterrence_slash_e8,
            "fee_spend_total_e8": self.fee_spend_total_e8,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def sample_envelope() -> dict[str, Any]:
    return {
        "schema": ENVELOPE_SCHEMA,
        "query_id": sample_hash("zenodex.oracle.query.perps.index_price_e8"),
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "notional_value_e8": 1_000_000_000_000,
        "max_extractable_value_e8": 50_000_000_000,
        "attack_cost_floor_e8": 75_000_000_000,
        "required_attack_margin_bps": 2_000,
        "reporter_count": 3,
        "reporter_reward_budget_e8": 120_000_000,
        "reporter_reward_per_report_e8": 30_000_000,
        "honest_reporter_cost_e8": 20_000_000,
        "honest_reporter_risk_premium_e8": 5_000_000,
        "reporter_bond_required_e8": 250_000_000_000,
        "slash_fraction_bps": 5_000,
        "expected_cheat_gain_e8": 50_000_000_000,
        "deterrence_margin_bps": 2_000,
        "dispute_reward_e8": 10_000_000,
        "dispute_budget_e8": 20_000_000,
        "fee_paid_e8": 100_000_000,
        "reporter_fee_share_e8": 30_000_000,
        "treasury_fee_share_e8": 40_000_000,
        "burn_fee_share_e8": 30_000_000,
    }


def _ceil_div(numer: int, denom: int) -> int:
    return (numer + denom - 1) // denom


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and bool(SHA256_RE.match(value))


def _unknown_fields(obj: Mapping[str, Any], errors: list[str]) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append("economic_security_field_must_be_string")
        elif key not in ENVELOPE_KEYS:
            errors.append(f"unknown_economic_security_field:{key}")


def _hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _token(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{key}_must_be_token")
        return None
    return str(value)


def _int_between(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int = 0,
    maximum: int = MAX_AMOUNT,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum or value > maximum:
        errors.append(f"{key}_must_be_int_between_{minimum}_and_{maximum}")
        return None
    return int(value)


def verify_economic_security_envelope(obj: Mapping[str, Any]) -> EconomicSecurityResult:
    errors: list[str] = []
    _unknown_fields(obj, errors)
    if obj.get("schema") != ENVELOPE_SCHEMA:
        errors.append("economic_security_schema_mismatch")

    query_id = _hash(obj, "query_id", errors)
    consumer_module = _token(obj, "consumer_module", errors)
    action_kind = _token(obj, "action_kind", errors)
    notional_value = _int_between(obj, "notional_value_e8", errors)
    max_extractable = _int_between(obj, "max_extractable_value_e8", errors)
    attack_cost_floor = _int_between(obj, "attack_cost_floor_e8", errors)
    required_attack_margin_bps = _int_between(
        obj,
        "required_attack_margin_bps",
        errors,
        maximum=MAX_MARGIN_BPS,
    )
    reporter_count = _int_between(obj, "reporter_count", errors, minimum=1, maximum=MAX_COUNT)
    reporter_reward_budget = _int_between(obj, "reporter_reward_budget_e8", errors)
    reporter_reward_per_report = _int_between(obj, "reporter_reward_per_report_e8", errors)
    honest_reporter_cost = _int_between(obj, "honest_reporter_cost_e8", errors)
    honest_reporter_risk_premium = _int_between(obj, "honest_reporter_risk_premium_e8", errors)
    reporter_bond_required = _int_between(obj, "reporter_bond_required_e8", errors)
    slash_fraction_bps = _int_between(obj, "slash_fraction_bps", errors, maximum=BPS_SCALE)
    expected_cheat_gain = _int_between(obj, "expected_cheat_gain_e8", errors)
    deterrence_margin_bps = _int_between(
        obj,
        "deterrence_margin_bps",
        errors,
        maximum=MAX_MARGIN_BPS,
    )
    dispute_reward = _int_between(obj, "dispute_reward_e8", errors)
    dispute_budget = _int_between(obj, "dispute_budget_e8", errors)
    fee_paid = _int_between(obj, "fee_paid_e8", errors)
    reporter_fee_share = _int_between(obj, "reporter_fee_share_e8", errors)
    treasury_fee_share = _int_between(obj, "treasury_fee_share_e8", errors)
    burn_fee_share = _int_between(obj, "burn_fee_share_e8", errors)

    if (
        notional_value is not None
        and max_extractable is not None
        and max_extractable > notional_value
    ):
        errors.append("extractable_value_exceeds_notional")
    if (
        expected_cheat_gain is not None
        and max_extractable is not None
        and expected_cheat_gain > max_extractable
    ):
        errors.append("expected_cheat_gain_exceeds_extractable_value")

    required_attack_cost: int | None = None
    if max_extractable is not None and required_attack_margin_bps is not None:
        required_attack_cost = _ceil_div(
            max_extractable * (BPS_SCALE + required_attack_margin_bps),
            BPS_SCALE,
        )
        if attack_cost_floor is not None and attack_cost_floor < required_attack_cost:
            errors.append("attack_cost_floor_below_required_margin")

    required_reporter_reward_per_report: int | None = None
    if honest_reporter_cost is not None and honest_reporter_risk_premium is not None:
        required_reporter_reward_per_report = honest_reporter_cost + honest_reporter_risk_premium
        if (
            reporter_reward_per_report is not None
            and reporter_reward_per_report < required_reporter_reward_per_report
        ):
            errors.append("reporter_reward_below_honest_cost_plus_risk")

    total_reporter_reward: int | None = None
    if reporter_reward_per_report is not None and reporter_count is not None:
        total_reporter_reward = reporter_reward_per_report * reporter_count
        if reporter_reward_budget is not None and total_reporter_reward > reporter_reward_budget:
            errors.append("reporter_reward_budget_exceeded")

    slash_amount: int | None = None
    required_deterrence_slash: int | None = None
    if reporter_bond_required is not None and slash_fraction_bps is not None:
        slash_amount = (reporter_bond_required * slash_fraction_bps) // BPS_SCALE
    if expected_cheat_gain is not None and deterrence_margin_bps is not None:
        required_deterrence_slash = _ceil_div(
            expected_cheat_gain * (BPS_SCALE + deterrence_margin_bps),
            BPS_SCALE,
        )
    if (
        slash_amount is not None
        and required_deterrence_slash is not None
        and slash_amount < required_deterrence_slash
    ):
        errors.append("slash_deterrence_below_required_margin")

    if dispute_reward is not None and dispute_budget is not None and dispute_reward > dispute_budget:
        errors.append("dispute_reward_budget_exceeded")

    fee_spend_total: int | None = None
    if reporter_fee_share is not None and treasury_fee_share is not None and burn_fee_share is not None:
        fee_spend_total = reporter_fee_share + treasury_fee_share + burn_fee_share
        if fee_paid is not None and fee_spend_total > fee_paid:
            errors.append("fee_shares_exceed_fee_paid")

    return EconomicSecurityResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        query_id=query_id,
        consumer_module=consumer_module,
        action_kind=action_kind,
        required_attack_cost_e8=required_attack_cost,
        required_reporter_reward_per_report_e8=required_reporter_reward_per_report,
        total_reporter_reward_e8=total_reporter_reward,
        slash_amount_e8=slash_amount,
        required_deterrence_slash_e8=required_deterrence_slash,
        fee_spend_total_e8=fee_spend_total,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_ENVELOPE_BYTES:
        raise ValueError(f"economic_security_file_too_large:{size}>{MAX_ENVELOPE_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("economic security root must be a JSON object")
    return obj


def _write_result(result: EconomicSecurityResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        envelope = _load_json(Path(args.envelope))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = EconomicSecurityResult(
            status="inconclusive",
            errors=[f"economic_security_load_failed:{exc}"],
        )
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_economic_security_envelope(envelope)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_envelope(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an Oracle economic security envelope")
    verify.add_argument("envelope", help="path to an economic security envelope JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted economic security envelope")
    sample.add_argument("--output", help="optional output path for the sample envelope JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
