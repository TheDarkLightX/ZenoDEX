#!/usr/bin/env python3
"""Validate the internal gamification evidence manifest."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Mapping

MANIFEST_SCHEMA = "zenodex.gamification_manifest.v0"
REPORT_SCHEMA = "zenodex.gamification_manifest_report.v0"

ALLOWED_STATUSES = {"internal_research_only", "testnet_only"}
ALLOWED_REWARD_UNITS = {
    "non_transferable_points",
    "non_transferable_badges",
    "non_transferable_reputation",
    "capped_testnet_credits",
}
REQUIRED_ABUSE_CONTROLS = {
    "per_identity_cap",
    "duplicate_rejection",
    "quality_gate",
    "sybil_review",
    "wash_activity_filter",
    "benefit_value_gate",
    "interface_non_solicitation_gate",
}
REQUIRED_ATTACK_QUERIES = {
    "sybil_split",
    "wash_activity",
    "duplicate_claim",
    "low_quality_submission",
    "xp_token_conversion",
    "economic_benefit_without_gate",
    "benefit_steering_specific_transaction",
}
ALLOWED_BENEFIT_TYPES = {
    "fee_discount_or_rebate",
    "paid_feature_access_waiver",
}
REQUIRED_BENEFIT_PROGRAM_TYPES = {
    "fee_discount_or_rebate",
    "paid_feature_access_waiver",
}
ALLOWED_GATE_STATUSES = {"required_not_complete", "complete"}
REQUIRED_NON_ECONOMIC_BENEFITS = {
    "level_display",
    "league_display",
    "og_status",
    "cosmetic_badges",
    "educational_or_beta_access",
}
REQUIRED_FORBIDDEN_WITHOUT_SEPARATE_GATE = {
    "token_airdrop_or_distribution",
    "fee_discount_or_rebate",
    "yield_or_staking_boost",
    "governance_weight",
    "revenue_share",
    "priority_execution",
}
REQUIRED_NON_CLAIMS = {
    "no_cash_value",
    "non_transferable",
    "no_public_launch",
    "no_investment_return",
    "xp_not_token_entitlement",
    "token_distribution_separate_program",
    "no_specific_transaction_solicitation",
    "no_investment_advice",
    "counsel_review_required",
}


def validate_gamification_manifest_v0(manifest: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)

    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    status = _str(obj.get("status"), "status", errors)
    reward_unit = _str(obj.get("reward_unit"), "reward_unit", errors)
    cash_value = _bool(obj.get("cash_value"), "cash_value", errors)
    transferable = _bool(obj.get("transferable"), "transferable", errors)
    public_claims_allowed = _bool(obj.get("public_claims_allowed"), "public_claims_allowed", errors)
    counsel_review_required = _bool(obj.get("counsel_review_required"), "counsel_review_required", errors)
    counsel_review_status = _str(obj.get("counsel_review_status"), "counsel_review_status", errors)

    if status is not None and status not in ALLOWED_STATUSES:
        errors.append("status must be internal_research_only or testnet_only")
    if reward_unit is not None and reward_unit not in ALLOWED_REWARD_UNITS:
        errors.append("reward_unit must be non-transferable or capped testnet-only")
    if cash_value is not False:
        errors.append("cash_value must be false")
    if transferable is not False:
        errors.append("transferable must be false")
    if public_claims_allowed is not False:
        errors.append("public_claims_allowed must be false")
    if counsel_review_required is not True:
        errors.append("counsel_review_required must be true")
    if counsel_review_status == "complete" and status != "testnet_only":
        errors.append("complete counsel review cannot promote an internal-only manifest by itself")

    caps = _validate_caps(obj.get("caps"))
    eligible_actions = _validate_actions(
        obj.get("eligible_actions"),
        max_reward_per_user=caps["facts"].get("max_reward_per_user"),
    )
    abuse_controls = _required_string_set(
        obj.get("abuse_controls"),
        "abuse_controls",
        required=REQUIRED_ABUSE_CONTROLS,
        allow_extra=False,
    )
    attack_queries = _validate_attack_queries(obj.get("attack_queries"))
    benefit_boundary = _validate_benefit_boundary(obj.get("benefit_boundary"))
    benefit_programs = _validate_benefit_programs(obj.get("benefit_programs"), manifest_status=status)
    promotion_boundary = _validate_promotion_boundary(obj.get("promotion_boundary"))

    sections = (
        ("caps", caps),
        ("eligible_actions", eligible_actions),
        ("abuse_controls", abuse_controls),
        ("attack_queries", attack_queries),
        ("benefit_boundary", benefit_boundary),
        ("benefit_programs", benefit_programs),
        ("promotion_boundary", promotion_boundary),
    )
    for name, section in sections:
        if not section["ok"]:
            errors.append(f"{name} rejected")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "facts": {
            "status": status,
            "reward_unit": reward_unit,
            "cash_value": cash_value,
            "transferable": transferable,
            "public_claims_allowed": public_claims_allowed,
            "counsel_review_required": counsel_review_required,
            "counsel_review_status": counsel_review_status,
            "action_count": eligible_actions["facts"].get("action_count"),
            "per_epoch_action_spend_cap": eligible_actions["facts"].get("per_epoch_action_spend_cap"),
        },
        "caps": caps,
        "eligible_actions": eligible_actions,
        "abuse_controls": abuse_controls,
        "attack_queries": attack_queries,
        "benefit_boundary": benefit_boundary,
        "benefit_programs": benefit_programs,
        "promotion_boundary": promotion_boundary,
    }


def _validate_caps(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "caps", errors)
    max_reward_per_user = _int_ge(obj.get("max_reward_per_user"), "caps.max_reward_per_user", errors, 1)
    max_reward_per_epoch = _int_ge(obj.get("max_reward_per_epoch"), "caps.max_reward_per_epoch", errors, 1)
    max_total_campaign = _int_ge(obj.get("max_total_campaign"), "caps.max_total_campaign", errors, 1)

    if max_reward_per_user is not None and max_reward_per_epoch is not None:
        if max_reward_per_user > max_reward_per_epoch:
            errors.append("caps.max_reward_per_user must be <= caps.max_reward_per_epoch")
    if max_reward_per_epoch is not None and max_total_campaign is not None:
        if max_reward_per_epoch > max_total_campaign:
            errors.append("caps.max_reward_per_epoch must be <= caps.max_total_campaign")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "max_reward_per_user": max_reward_per_user,
            "max_reward_per_epoch": max_reward_per_epoch,
            "max_total_campaign": max_total_campaign,
        },
    }


def _validate_actions(value: Any, *, max_reward_per_user: Any) -> dict[str, Any]:
    errors: list[str] = []
    if not isinstance(value, list) or not value:
        errors.append("eligible_actions must be a non-empty list")
        value = []

    seen_ids: set[str] = set()
    reports: list[dict[str, Any]] = []
    per_epoch_action_spend_cap = 0
    for index, item in enumerate(value):
        action_errors: list[str] = []
        action = _mapping(item, f"eligible_actions[{index}]", action_errors)
        action_id = _str(action.get("id"), f"eligible_actions[{index}].id", action_errors)
        description = _str(action.get("description"), f"eligible_actions[{index}].description", action_errors)
        reward_amount = _int_ge(
            action.get("reward_amount"),
            f"eligible_actions[{index}].reward_amount",
            action_errors,
            0,
        )
        max_per_user_per_epoch = _int_ge(
            action.get("max_per_user_per_epoch"),
            f"eligible_actions[{index}].max_per_user_per_epoch",
            action_errors,
            1,
        )
        eligibility = _str(action.get("eligibility"), f"eligible_actions[{index}].eligibility", action_errors)
        quality_gate = _str(action.get("quality_gate"), f"eligible_actions[{index}].quality_gate", action_errors)
        duplicate_key = _str(action.get("duplicate_key"), f"eligible_actions[{index}].duplicate_key", action_errors)

        if action_id is not None:
            if action_id in seen_ids:
                action_errors.append("eligible action id must be unique")
            seen_ids.add(action_id)
        if reward_amount is not None and max_per_user_per_epoch is not None:
            per_epoch_action_spend_cap += reward_amount * max_per_user_per_epoch

        reports.append(
            {
                "id": action_id,
                "ok": not action_errors,
                "status": "accepted" if not action_errors else "rejected",
                "errors": action_errors,
                "facts": {
                    "description": description,
                    "reward_amount": reward_amount,
                    "max_per_user_per_epoch": max_per_user_per_epoch,
                    "eligibility": eligibility,
                    "quality_gate": quality_gate,
                    "duplicate_key": duplicate_key,
                },
            }
        )

    max_per_user = _optional_int(max_reward_per_user)
    if max_per_user is not None and per_epoch_action_spend_cap > max_per_user:
        errors.append("eligible action per-user epoch spend cap exceeds caps.max_reward_per_user")
    if any(not report["ok"] for report in reports):
        errors.append("one or more eligible actions rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "action_count": len(reports),
            "per_epoch_action_spend_cap": per_epoch_action_spend_cap,
            "max_reward_per_user": max_per_user,
        },
        "items": reports,
    }


def _validate_attack_queries(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    if not isinstance(value, list):
        errors.append("attack_queries must be a list")
        value = []

    seen_ids: set[str] = set()
    reports: list[dict[str, Any]] = []
    for index, item in enumerate(value):
        query_errors: list[str] = []
        query = _mapping(item, f"attack_queries[{index}]", query_errors)
        query_id = _str(query.get("id"), f"attack_queries[{index}].id", query_errors)
        condition = _str(query.get("condition"), f"attack_queries[{index}].condition", query_errors)
        mitigation = _str(query.get("mitigation"), f"attack_queries[{index}].mitigation", query_errors)
        expected_result = _str(query.get("expected_result"), f"attack_queries[{index}].expected_result", query_errors)

        if query_id is not None:
            if query_id in seen_ids:
                query_errors.append("attack query id must be unique")
            seen_ids.add(query_id)
        if expected_result is not None and expected_result not in {"rejected", "bounded"}:
            query_errors.append("attack query expected_result must be rejected or bounded")

        reports.append(
            {
                "id": query_id,
                "ok": not query_errors,
                "status": "accepted" if not query_errors else "rejected",
                "errors": query_errors,
                "facts": {
                    "condition": condition,
                    "mitigation": mitigation,
                    "expected_result": expected_result,
                },
            }
        )

    missing = sorted(REQUIRED_ATTACK_QUERIES - seen_ids)
    if missing:
        errors.append("missing required attack queries")
    if any(not report["ok"] for report in reports):
        errors.append("one or more attack queries rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "missing_required_attack_queries": missing,
            "attack_query_count": len(reports),
        },
        "items": reports,
    }


def _validate_benefit_boundary(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "benefit_boundary", errors)
    xp_transferable = _bool(obj.get("xp_transferable"), "benefit_boundary.xp_transferable", errors)
    xp_cash_value = _bool(obj.get("xp_cash_value"), "benefit_boundary.xp_cash_value", errors)
    xp_redeemable_for_tokens = _bool(
        obj.get("xp_redeemable_for_tokens"),
        "benefit_boundary.xp_redeemable_for_tokens",
        errors,
    )
    xp_entitles_token_distribution = _bool(
        obj.get("xp_entitles_token_distribution"),
        "benefit_boundary.xp_entitles_token_distribution",
        errors,
    )
    separate_token_distribution_allowed = _bool(
        obj.get("separate_token_distribution_allowed"),
        "benefit_boundary.separate_token_distribution_allowed",
        errors,
    )
    economic_benefits_require_separate_tokenomics_gate = _bool(
        obj.get("economic_benefits_require_separate_tokenomics_gate"),
        "benefit_boundary.economic_benefits_require_separate_tokenomics_gate",
        errors,
    )
    economic_benefits_require_counsel_review = _bool(
        obj.get("economic_benefits_require_counsel_review"),
        "benefit_boundary.economic_benefits_require_counsel_review",
        errors,
    )
    covered_user_interface_boundary_gate_id = _str(
        obj.get("covered_user_interface_boundary_gate_id"),
        "benefit_boundary.covered_user_interface_boundary_gate_id",
        errors,
    )

    if xp_transferable is not False:
        errors.append("benefit_boundary.xp_transferable must be false")
    if xp_cash_value is not False:
        errors.append("benefit_boundary.xp_cash_value must be false")
    if xp_redeemable_for_tokens is not False:
        errors.append("benefit_boundary.xp_redeemable_for_tokens must be false")
    if xp_entitles_token_distribution is not False:
        errors.append("benefit_boundary.xp_entitles_token_distribution must be false")
    if separate_token_distribution_allowed is not True:
        errors.append("benefit_boundary.separate_token_distribution_allowed must be true")
    if economic_benefits_require_separate_tokenomics_gate is not True:
        errors.append("benefit_boundary.economic_benefits_require_separate_tokenomics_gate must be true")
    if economic_benefits_require_counsel_review is not True:
        errors.append("benefit_boundary.economic_benefits_require_counsel_review must be true")

    allowed_non_economic = _required_string_set(
        obj.get("allowed_non_economic_benefits"),
        "benefit_boundary.allowed_non_economic_benefits",
        required=REQUIRED_NON_ECONOMIC_BENEFITS,
        allow_extra=False,
    )
    forbidden_without_gate = _required_string_set(
        obj.get("forbidden_without_separate_gate"),
        "benefit_boundary.forbidden_without_separate_gate",
        required=REQUIRED_FORBIDDEN_WITHOUT_SEPARATE_GATE,
        allow_extra=False,
    )
    if not allowed_non_economic["ok"]:
        errors.append("benefit boundary missing required non-economic benefit classes")
    if not forbidden_without_gate["ok"]:
        errors.append("benefit boundary missing required gated economic benefit classes")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "xp_transferable": xp_transferable,
            "xp_cash_value": xp_cash_value,
            "xp_redeemable_for_tokens": xp_redeemable_for_tokens,
            "xp_entitles_token_distribution": xp_entitles_token_distribution,
            "separate_token_distribution_allowed": separate_token_distribution_allowed,
            "economic_benefits_require_separate_tokenomics_gate": economic_benefits_require_separate_tokenomics_gate,
            "economic_benefits_require_counsel_review": economic_benefits_require_counsel_review,
            "covered_user_interface_boundary_gate_id": covered_user_interface_boundary_gate_id,
            "missing_allowed_non_economic_benefits": allowed_non_economic["facts"].get("missing_required"),
            "missing_forbidden_without_gate": forbidden_without_gate["facts"].get("missing_required"),
        },
        "allowed_non_economic_benefits": allowed_non_economic,
        "forbidden_without_separate_gate": forbidden_without_gate,
    }


def _validate_benefit_programs(value: Any, *, manifest_status: str | None) -> dict[str, Any]:
    errors: list[str] = []
    if not isinstance(value, list):
        errors.append("benefit_programs must be a list")
        value = []

    seen_ids: set[str] = set()
    seen_types: set[str] = set()
    reports: list[dict[str, Any]] = []
    total_epoch_cap = 0
    for index, item in enumerate(value):
        program_errors: list[str] = []
        program = _mapping(item, f"benefit_programs[{index}]", program_errors)
        program_id = _str(program.get("id"), f"benefit_programs[{index}].id", program_errors)
        benefit_type = _str(program.get("benefit_type"), f"benefit_programs[{index}].benefit_type", program_errors)
        description = _str(program.get("description"), f"benefit_programs[{index}].description", program_errors)
        eligibility = _str(program.get("eligibility"), f"benefit_programs[{index}].eligibility", program_errors)
        league_min = _int_ge(program.get("league_min"), f"benefit_programs[{index}].league_min", program_errors, 1)
        per_user_cap = _int_ge(
            program.get("max_benefit_value_per_user_per_epoch"),
            f"benefit_programs[{index}].max_benefit_value_per_user_per_epoch",
            program_errors,
            1,
        )
        per_epoch_cap = _int_ge(
            program.get("max_benefit_value_per_epoch"),
            f"benefit_programs[{index}].max_benefit_value_per_epoch",
            program_errors,
            1,
        )
        value_unit = _str(program.get("value_unit"), f"benefit_programs[{index}].value_unit", program_errors)
        funding_or_accounting_source = _str(
            program.get("funding_or_accounting_source"),
            f"benefit_programs[{index}].funding_or_accounting_source",
            program_errors,
        )
        separate_tokenomics_gate_id = _str(
            program.get("separate_tokenomics_gate_id"),
            f"benefit_programs[{index}].separate_tokenomics_gate_id",
            program_errors,
        )
        separate_gate_status = _str(
            program.get("separate_gate_status"),
            f"benefit_programs[{index}].separate_gate_status",
            program_errors,
        )
        counsel_review_status = _str(
            program.get("counsel_review_status"),
            f"benefit_programs[{index}].counsel_review_status",
            program_errors,
        )
        activation_allowed = _bool(
            program.get("activation_allowed"),
            f"benefit_programs[{index}].activation_allowed",
            program_errors,
        )
        abuse_gate = _str(program.get("abuse_gate"), f"benefit_programs[{index}].abuse_gate", program_errors)
        terms_disclosed = _bool(
            program.get("terms_disclosed"),
            f"benefit_programs[{index}].terms_disclosed",
            program_errors,
        )
        benefit_liability_accounted = _bool(
            program.get("benefit_liability_accounted"),
            f"benefit_programs[{index}].benefit_liability_accounted",
            program_errors,
        )

        if program_id is not None:
            if program_id in seen_ids:
                program_errors.append("benefit program id must be unique")
            seen_ids.add(program_id)
        if benefit_type is not None:
            seen_types.add(benefit_type)
            if benefit_type not in ALLOWED_BENEFIT_TYPES:
                program_errors.append("benefit_type is unsupported")
        if separate_gate_status is not None and separate_gate_status not in ALLOWED_GATE_STATUSES:
            program_errors.append("separate_gate_status must be required_not_complete or complete")
        if counsel_review_status is not None and counsel_review_status not in ALLOWED_GATE_STATUSES:
            program_errors.append("counsel_review_status must be required_not_complete or complete")
        if per_user_cap is not None and per_epoch_cap is not None:
            total_epoch_cap += per_epoch_cap
            if per_user_cap > per_epoch_cap:
                program_errors.append("benefit per-user cap must be <= per-epoch cap")
        if activation_allowed is True:
            if manifest_status != "testnet_only" or separate_gate_status != "complete" or counsel_review_status != "complete":
                program_errors.append("activation requires testnet status plus complete tokenomics gate and counsel review")
        if terms_disclosed is not True:
            program_errors.append("terms_disclosed must be true")
        if benefit_liability_accounted is not True:
            program_errors.append("benefit_liability_accounted must be true")

        reports.append(
            {
                "id": program_id,
                "ok": not program_errors,
                "status": "accepted" if not program_errors else "rejected",
                "errors": program_errors,
                "facts": {
                    "benefit_type": benefit_type,
                    "description": description,
                    "eligibility": eligibility,
                    "league_min": league_min,
                    "max_benefit_value_per_user_per_epoch": per_user_cap,
                    "max_benefit_value_per_epoch": per_epoch_cap,
                    "value_unit": value_unit,
                    "funding_or_accounting_source": funding_or_accounting_source,
                    "separate_tokenomics_gate_id": separate_tokenomics_gate_id,
                    "separate_gate_status": separate_gate_status,
                    "counsel_review_status": counsel_review_status,
                    "activation_allowed": activation_allowed,
                    "abuse_gate": abuse_gate,
                    "terms_disclosed": terms_disclosed,
                    "benefit_liability_accounted": benefit_liability_accounted,
                },
            }
        )

    missing_types = sorted(REQUIRED_BENEFIT_PROGRAM_TYPES - seen_types)
    if missing_types:
        errors.append("missing required benefit program types")
    if any(not report["ok"] for report in reports):
        errors.append("one or more benefit programs rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "benefit_program_count": len(reports),
            "missing_required_benefit_program_types": missing_types,
            "total_epoch_benefit_cap": total_epoch_cap,
        },
        "items": reports,
    }


def _validate_promotion_boundary(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "promotion_boundary", errors)
    public_claim_allowed = _bool(
        obj.get("public_claim_allowed"),
        "promotion_boundary.public_claim_allowed",
        errors,
    )
    claim_registry_entry_allowed = _bool(
        obj.get("claim_registry_entry_allowed"),
        "promotion_boundary.claim_registry_entry_allowed",
        errors,
    )
    if public_claim_allowed is not False:
        errors.append("promotion_boundary.public_claim_allowed must be false")
    if claim_registry_entry_allowed is not False:
        errors.append("promotion_boundary.claim_registry_entry_allowed must be false")

    non_claims = _required_string_set(
        obj.get("non_claims"),
        "promotion_boundary.non_claims",
        required=REQUIRED_NON_CLAIMS,
        allow_extra=False,
    )
    if not non_claims["ok"]:
        errors.append("promotion boundary missing required non-claims")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "public_claim_allowed": public_claim_allowed,
            "claim_registry_entry_allowed": claim_registry_entry_allowed,
            "missing_required_non_claims": non_claims["facts"].get("missing_required"),
        },
        "non_claims": non_claims,
    }


def _required_string_set(
    value: Any,
    field: str,
    *,
    required: set[str],
    allow_extra: bool,
) -> dict[str, Any]:
    errors: list[str] = []
    if not isinstance(value, list):
        errors.append(f"{field} must be a list")
        value = []
    items: set[str] = set()
    for index, item in enumerate(value):
        parsed = _str(item, f"{field}[{index}]", errors)
        if parsed is not None:
            items.add(parsed)

    missing = sorted(required - items)
    unknown = sorted(items - required)
    if missing:
        errors.append(f"{field} missing required values")
    if unknown and not allow_extra:
        errors.append(f"{field} contains unknown values")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "items": sorted(items),
            "missing_required": missing,
            "unknown": unknown,
        },
    }


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if isinstance(value, str) and value.strip():
        return value.strip()
    errors.append(f"{name} must be a non-empty string")
    return None


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if isinstance(value, bool):
        return value
    errors.append(f"{name} must be a bool")
    return None


def _int_ge(value: Any, name: str, errors: list[str], minimum: int) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{name} must be an int")
        return None
    if value < minimum:
        errors.append(f"{name} must be >= {minimum}")
        return None
    return int(value)


def _optional_int(value: Any) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    return None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args(argv)

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    report = validate_gamification_manifest_v0(manifest)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
