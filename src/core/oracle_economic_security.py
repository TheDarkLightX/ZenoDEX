"""Deterministic Oracle economic-envelope validation shared by all consumers."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Mapping

ENVELOPE_SCHEMA = "zenodex.oracle.economic_security_envelope.v1"
RESULT_SCHEMA = "zenodex.oracle.economic_security_verify_result.v1"
MAX_AMOUNT = 10**30
MAX_COUNT = 1024
BPS_SCALE = 10_000
MAX_MARGIN_BPS = 1_000_000
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
ENVELOPE_KEYS = frozenset(
    {
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
)
NOT_CLAIMED = (
    "does_not_claim_token_price_appreciation",
    "does_not_claim_market_price_truth",
    "does_not_claim_reporter_honesty",
    "does_not_claim_attack_cost_estimate_is_correct",
    "does_not_claim_production_oracle_network_live",
)


@dataclass(frozen=True)
class EconomicSecurityResult:
    status: str
    errors: tuple[str, ...]
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
            "not_claimed": list(NOT_CLAIMED),
        }


def _ceil_div(numer: int, denom: int) -> int:
    return (numer + denom - 1) // denom


def _is_hash(value: object) -> bool:
    return type(value) is str and SHA256_RE.fullmatch(value) is not None


def _unknown_fields(obj: Mapping[str, Any], errors: list[str]) -> None:
    for key in obj:
        if key not in ENVELOPE_KEYS:
            errors.append(f"unknown_economic_security_field:{key}")


def _hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return value


def _token(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if type(value) is not str or TOKEN_RE.fullmatch(value) is None:
        errors.append(f"{key}_must_be_token")
        return None
    return value


def _int_between(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int = 0,
    maximum: int = MAX_AMOUNT,
) -> int | None:
    value = obj.get(key)
    if type(value) is not int or value < minimum or value > maximum:
        errors.append(f"{key}_must_be_int_between_{minimum}_and_{maximum}")
        return None
    return value


def verify_economic_security_envelope(
    obj: Mapping[str, Any],
) -> EconomicSecurityResult:
    """Validate the complete closed V1 economic policy with integer arithmetic."""

    if type(obj) is not dict:
        return EconomicSecurityResult(
            status="rejected",
            errors=("economic_security_root_must_be_exact_object",),
        )
    if any(type(key) is not str for key in obj):
        return EconomicSecurityResult(
            status="rejected",
            errors=("economic_security_field_must_be_string",),
        )

    errors: list[str] = []
    _unknown_fields(obj, errors)
    schema = obj.get("schema")
    if type(schema) is not str or schema != ENVELOPE_SCHEMA:
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
    reporter_count = _int_between(
        obj,
        "reporter_count",
        errors,
        minimum=1,
        maximum=MAX_COUNT,
    )
    reporter_reward_budget = _int_between(obj, "reporter_reward_budget_e8", errors)
    reporter_reward_per_report = _int_between(obj, "reporter_reward_per_report_e8", errors)
    honest_reporter_cost = _int_between(obj, "honest_reporter_cost_e8", errors)
    honest_reporter_risk_premium = _int_between(
        obj,
        "honest_reporter_risk_premium_e8",
        errors,
    )
    reporter_bond_required = _int_between(obj, "reporter_bond_required_e8", errors)
    slash_fraction_bps = _int_between(
        obj,
        "slash_fraction_bps",
        errors,
        maximum=BPS_SCALE,
    )
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
    if (
        reporter_fee_share is not None
        and treasury_fee_share is not None
        and burn_fee_share is not None
    ):
        fee_spend_total = reporter_fee_share + treasury_fee_share + burn_fee_share
        if fee_paid is not None and fee_spend_total > fee_paid:
            errors.append("fee_shares_exceed_fee_paid")

    return EconomicSecurityResult(
        status="rejected" if errors else "accepted",
        errors=tuple(errors),
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
