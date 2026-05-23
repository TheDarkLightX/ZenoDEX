#!/usr/bin/env python3
"""Validate bounded tokenomics reward safety envelopes."""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.tokenomics.pro_rata_budget import max_safe_budget_quote_pro_rata_budget  # noqa: E402
from tools.tokenomics.wash_trade import min_cost_to_reach_usage_fee_gated  # noqa: E402

MANIFEST_SCHEMA = "zenodex.tokenomics.reward_safety_envelope.v0"
REPORT_SCHEMA = "zenodex.tokenomics.reward_safety_envelope_report.v0"


def validate_reward_safety_envelope_v0(manifest: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    programs_raw = obj.get("programs")
    if not isinstance(programs_raw, list):
        errors.append("programs must be a list")
        programs_raw = []

    program_reports: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for index, item in enumerate(programs_raw):
        program_errors: list[str] = []
        program = _mapping(item, f"programs[{index}]", program_errors)
        program_id = _str(program.get("id"), f"programs[{index}].id", program_errors)
        kind = _str(program.get("kind"), f"programs[{index}].kind", program_errors)
        if program_id is not None:
            if program_id in seen_ids:
                program_errors.append("program id must be unique")
            seen_ids.add(program_id)

        if kind == "fee_gated_identity_reward":
            report = _validate_fee_gated_identity_reward(program, index, program_errors)
        elif kind == "pro_rata_budget":
            report = _validate_pro_rata_budget(program, index, program_errors)
        elif kind == "activity_mined_distribution":
            report = _validate_activity_mined_distribution(program, index, program_errors)
        else:
            report = {"facts": {}}
            if kind is not None:
                program_errors.append("kind must be fee_gated_identity_reward, pro_rata_budget, or activity_mined_distribution")

        report.update(
            {
                "id": program_id,
                "kind": kind,
                "ok": not program_errors,
                "status": "accepted" if not program_errors else "rejected",
                "errors": program_errors,
            }
        )
        program_reports.append(report)

    rejected_count = sum(1 for report in program_reports if not report["ok"])
    if rejected_count:
        errors.append("one or more reward programs rejected")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "program_count": len(program_reports),
        "accepted_program_count": len(program_reports) - rejected_count,
        "rejected_program_count": rejected_count,
        "programs": program_reports,
    }


def _validate_fee_gated_identity_reward(
    program: Mapping[str, Any],
    index: int,
    errors: list[str],
) -> dict[str, Any]:
    params = _mapping(program.get("params"), f"programs[{index}].params", errors)
    base = _base_params(params, f"programs[{index}].params", errors)
    pol_share_bps = _int_between(params.get("pol_share_bps"), "pol_share_bps", errors, 0, 10_000)
    min_usage_quote = _int_ge(params.get("min_usage_quote"), "min_usage_quote", errors, 0)
    base_reward_quote = _int_ge(
        params.get("base_reward_per_identity_quote"),
        "base_reward_per_identity_quote",
        errors,
        0,
    )
    max_identities = _int_ge(params.get("max_identities"), "max_identities", errors, 1)
    funded_budget_quote = _int_ge(params.get("funded_budget_quote"), "funded_budget_quote", errors, 0)
    local_search_window = _int_ge(params.get("local_search_window", 64), "local_search_window", errors, 0)
    if (
        base is None
        or pol_share_bps is None
        or min_usage_quote is None
        or base_reward_quote is None
        or max_identities is None
        or funded_budget_quote is None
        or local_search_window is None
    ):
        return {"facts": {}}

    spend_cap_quote = int(base_reward_quote) * int(max_identities)
    if spend_cap_quote > int(funded_budget_quote):
        errors.append("identity reward spend cap exceeds funded_budget_quote")

    attacker_lp_share_bps = 10_000 - int(pol_share_bps)
    result = min_cost_to_reach_usage_fee_gated(
        reserve_base=base["reserve_base"],
        reserve_quote=base["reserve_quote"],
        fee_bps=base["fee_bps"],
        protocol_fee_share_bps=base["protocol_fee_share_bps"],
        min_usage_quote=int(min_usage_quote),
        attacker_lp_share_bps=attacker_lp_share_bps,
        max_trade_in_quote=base["max_trade_in_quote"],
        local_search_window=int(local_search_window),
    )
    safe_reward_max_int = None
    cost = result.best_cost_quote_at_p0
    if result.found and cost is not None:
        safe_reward_max_int = int(cost.numerator // cost.denominator)
        if Fraction(int(base_reward_quote), 1) > cost:
            errors.append("base_reward_per_identity_quote exceeds bounded wash-trade cost")

    return {
        "facts": {
            "attacker_lp_share_bps": attacker_lp_share_bps,
            "reward_spend_cap_quote": spend_cap_quote,
            "funded_budget_quote": int(funded_budget_quote),
            "wash_trade_reachable": bool(result.found),
            "best_trade_in_quote": result.best_trade_in_quote,
            "best_cost_quote_at_p0": _fraction_str(cost),
            "safe_base_reward_max_int": safe_reward_max_int,
        }
    }


def _validate_pro_rata_budget(
    program: Mapping[str, Any],
    index: int,
    errors: list[str],
) -> dict[str, Any]:
    params = _mapping(program.get("params"), f"programs[{index}].params", errors)
    base = _base_params(params, f"programs[{index}].params", errors)
    pol_share_bps = _int_between(params.get("pol_share_bps"), "pol_share_bps", errors, 0, 10_000)
    other_usage_quote = _int_ge(params.get("other_usage_quote"), "other_usage_quote", errors, 0)
    budget_quote = _int_ge(params.get("budget_quote"), "budget_quote", errors, 0)
    funded_budget_quote = _int_ge(params.get("funded_budget_quote"), "funded_budget_quote", errors, 0)
    scan_step = _int_ge(params.get("scan_step", 1), "scan_step", errors, 1)
    max_cycles = _int_ge(params.get("max_cycles", 1), "max_cycles", errors, 1)
    if (
        base is None
        or pol_share_bps is None
        or other_usage_quote is None
        or budget_quote is None
        or funded_budget_quote is None
        or scan_step is None
        or max_cycles is None
    ):
        return {"facts": {}}

    if int(budget_quote) > int(funded_budget_quote):
        errors.append("pro-rata budget_quote exceeds funded_budget_quote")

    safe_budget, _at0, at_budget = max_safe_budget_quote_pro_rata_budget(
        reserve_base=base["reserve_base"],
        reserve_quote=base["reserve_quote"],
        fee_bps=base["fee_bps"],
        protocol_fee_share_bps=base["protocol_fee_share_bps"],
        pol_share_bps=int(pol_share_bps),
        other_usage_quote=int(other_usage_quote),
        max_trade_in_quote=base["max_trade_in_quote"],
        budget_hi_quote=int(budget_quote),
        scan_step=int(scan_step),
        max_cycles=int(max_cycles),
    )
    if int(budget_quote) > int(safe_budget):
        errors.append("budget_quote exceeds bounded max_safe_budget_quote")

    return {
        "facts": {
            "attacker_lp_share_bps": 10_000 - int(pol_share_bps),
            "budget_quote": int(budget_quote),
            "funded_budget_quote": int(funded_budget_quote),
            "max_safe_budget_quote": int(safe_budget),
            "best_trade_in_quote_at_budget": at_budget.best_trade_in_quote,
            "best_cycles_at_budget": at_budget.best_cycles,
            "best_usage_quote_at_budget": at_budget.best_usage_quote,
            "best_reward_quote_at_budget": at_budget.best_reward_quote,
            "best_cost_quote_at_budget": _fraction_str(at_budget.best_cost_quote_at_p0),
            "best_profit_quote_at_budget": _fraction_str(at_budget.best_profit_quote_at_p0),
        }
    }


def _validate_activity_mined_distribution(
    program: Mapping[str, Any],
    index: int,
    errors: list[str],
) -> dict[str, Any]:
    params = _mapping(program.get("params"), f"programs[{index}].params", errors)
    source_bucket_id = _str(params.get("source_bucket_id"), "source_bucket_id", errors)
    source_bucket_amount_token = _int_ge(
        params.get("source_bucket_amount_token"),
        "source_bucket_amount_token",
        errors,
        1,
    )
    campaign_budget_token = _int_ge(params.get("campaign_budget_token"), "campaign_budget_token", errors, 1)
    funded_campaign_budget_token = _int_ge(
        params.get("funded_campaign_budget_token"),
        "funded_campaign_budget_token",
        errors,
        1,
    )
    max_epoch_distribution_token = _int_ge(
        params.get("max_epoch_distribution_token"),
        "max_epoch_distribution_token",
        errors,
        1,
    )
    max_user_distribution_token_per_epoch = _int_ge(
        params.get("max_user_distribution_token_per_epoch"),
        "max_user_distribution_token_per_epoch",
        errors,
        1,
    )
    reward_per_activity_token = _int_ge(
        params.get("reward_per_activity_token"),
        "reward_per_activity_token",
        errors,
        1,
    )
    max_rewardable_activities_per_user_per_epoch = _int_ge(
        params.get("max_rewardable_activities_per_user_per_epoch"),
        "max_rewardable_activities_per_user_per_epoch",
        errors,
        1,
    )
    xp_entitlement = _bool(params.get("xp_entitlement"), "xp_entitlement", errors)
    non_transferable_xp_required = _bool(
        params.get("non_transferable_xp_required"),
        "non_transferable_xp_required",
        errors,
    )
    eligible_activity_receipt_required = _bool(
        params.get("eligible_activity_receipt_required"),
        "eligible_activity_receipt_required",
        errors,
    )
    non_wash_receipt_required = _bool(
        params.get("non_wash_receipt_required"),
        "non_wash_receipt_required",
        errors,
    )
    covered_user_interface_gate_required = _bool(
        params.get("covered_user_interface_gate_required"),
        "covered_user_interface_gate_required",
        errors,
    )
    activation_allowed = _bool(params.get("activation_allowed"), "activation_allowed", errors)
    counsel_review_status = _str(params.get("counsel_review_status"), "counsel_review_status", errors)

    if (
        source_bucket_id is None
        or source_bucket_amount_token is None
        or campaign_budget_token is None
        or funded_campaign_budget_token is None
        or max_epoch_distribution_token is None
        or max_user_distribution_token_per_epoch is None
        or reward_per_activity_token is None
        or max_rewardable_activities_per_user_per_epoch is None
        or xp_entitlement is None
        or non_transferable_xp_required is None
        or eligible_activity_receipt_required is None
        or non_wash_receipt_required is None
        or covered_user_interface_gate_required is None
        or activation_allowed is None
        or counsel_review_status is None
    ):
        return {"facts": {}}

    if campaign_budget_token > source_bucket_amount_token:
        errors.append("campaign_budget_token exceeds source_bucket_amount_token")
    if campaign_budget_token > funded_campaign_budget_token:
        errors.append("campaign_budget_token exceeds funded_campaign_budget_token")
    if max_epoch_distribution_token > campaign_budget_token:
        errors.append("max_epoch_distribution_token exceeds campaign_budget_token")

    max_user_activity_distribution = reward_per_activity_token * max_rewardable_activities_per_user_per_epoch
    if max_user_activity_distribution > max_user_distribution_token_per_epoch:
        errors.append("per-user activity distribution exceeds max_user_distribution_token_per_epoch")

    if xp_entitlement is not False:
        errors.append("xp_entitlement must be false")
    if non_transferable_xp_required is not True:
        errors.append("non_transferable_xp_required must be true")
    if eligible_activity_receipt_required is not True:
        errors.append("eligible_activity_receipt_required must be true")
    if non_wash_receipt_required is not True:
        errors.append("non_wash_receipt_required must be true")
    if covered_user_interface_gate_required is not True:
        errors.append("covered_user_interface_gate_required must be true")
    if counsel_review_status not in {"required_not_complete", "complete"}:
        errors.append("counsel_review_status must be required_not_complete or complete")
    if activation_allowed is True and counsel_review_status != "complete":
        errors.append("activation requires complete counsel review")

    return {
        "facts": {
            "source_bucket_id": source_bucket_id,
            "source_bucket_amount_token": int(source_bucket_amount_token),
            "campaign_budget_token": int(campaign_budget_token),
            "funded_campaign_budget_token": int(funded_campaign_budget_token),
            "max_epoch_distribution_token": int(max_epoch_distribution_token),
            "max_user_distribution_token_per_epoch": int(max_user_distribution_token_per_epoch),
            "reward_per_activity_token": int(reward_per_activity_token),
            "max_rewardable_activities_per_user_per_epoch": int(max_rewardable_activities_per_user_per_epoch),
            "max_user_activity_distribution_token": int(max_user_activity_distribution),
            "xp_entitlement": xp_entitlement,
            "non_transferable_xp_required": non_transferable_xp_required,
            "eligible_activity_receipt_required": eligible_activity_receipt_required,
            "non_wash_receipt_required": non_wash_receipt_required,
            "covered_user_interface_gate_required": covered_user_interface_gate_required,
            "activation_allowed": activation_allowed,
            "counsel_review_status": counsel_review_status,
        }
    }


def _base_params(
    params: Mapping[str, Any],
    label: str,
    errors: list[str],
) -> dict[str, int] | None:
    reserve_base = _int_ge(params.get("reserve_base"), f"{label}.reserve_base", errors, 1)
    reserve_quote = _int_ge(params.get("reserve_quote"), f"{label}.reserve_quote", errors, 1)
    fee_bps = _int_between(params.get("fee_bps"), f"{label}.fee_bps", errors, 0, 10_000)
    protocol_fee_share_bps = _int_between(
        params.get("protocol_fee_share_bps"),
        f"{label}.protocol_fee_share_bps",
        errors,
        0,
        10_000,
    )
    max_trade_in_quote = _int_ge(params.get("max_trade_in_quote"), f"{label}.max_trade_in_quote", errors, 1)
    if (
        reserve_base is None
        or reserve_quote is None
        or fee_bps is None
        or protocol_fee_share_bps is None
        or max_trade_in_quote is None
    ):
        return None
    return {
        "reserve_base": int(reserve_base),
        "reserve_quote": int(reserve_quote),
        "fee_bps": int(fee_bps),
        "protocol_fee_share_bps": int(protocol_fee_share_bps),
        "max_trade_in_quote": int(max_trade_in_quote),
    }


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or value == "":
        errors.append(f"{name} must be a non-empty string")
        return None
    return value


def _int_ge(value: Any, name: str, errors: list[str], minimum: int) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{name} must be an int")
        return None
    if value < minimum:
        errors.append(f"{name} must be >= {minimum}")
        return None
    return int(value)


def _int_between(value: Any, name: str, errors: list[str], minimum: int, maximum: int) -> int | None:
    parsed = _int_ge(value, name, errors, minimum)
    if parsed is not None and parsed > maximum:
        errors.append(f"{name} must be <= {maximum}")
        return None
    return parsed


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if not isinstance(value, bool):
        errors.append(f"{name} must be a bool")
        return None
    return value


def _fraction_str(value: Fraction | None) -> str | None:
    if value is None:
        return None
    return f"{int(value.numerator)}/{int(value.denominator)}"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args(argv)

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    report = validate_reward_safety_envelope_v0(manifest)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
