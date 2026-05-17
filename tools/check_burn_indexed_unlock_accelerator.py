#!/usr/bin/env python3
"""Validate the internal burn-indexed unlock accelerator model."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping

MANIFEST_SCHEMA = "zenodex.burn_indexed_unlock_accelerator.v0"
REPORT_SCHEMA = "zenodex.burn_indexed_unlock_accelerator_report.v0"
BPS_SCALE = 10_000

ALLOWED_STATUSES = {"internal_research_only", "testnet_only"}
ALLOWED_REVIEW_STATUS = {"required_not_complete", "complete"}
ALLOWED_EPOCH_UNITS = {"month", "week"}
ALLOWED_ALLOCATION_SHARE_BASIS = {"base_epoch_release_share"}
ALLOWED_EXPECTED_RESULTS = {"rejected", "bounded"}

REQUIRED_CONTROLS = frozenset(
    {
        "cliff_preserved",
        "lagged_trailing_burn_window",
        "eligible_burn_receipts",
        "protocol_fee_burn_only",
        "anti_wash_filter",
        "related_party_exclusion",
        "treasury_funded_self_unlock_exclusion",
        "manual_burn_exclusion",
        "route_pool_venue_steering_exclusion",
        "per_epoch_extra_release_cap",
        "total_accelerated_release_cap",
        "audit_log",
        "emergency_freeze",
        "counsel_governance_activation_gate",
    }
)

REQUIRED_EXCLUSIONS = frozenset(
    {
        "wash_volume",
        "related_party_round_trip",
        "insider_funded_round_trip",
        "treasury_funded_self_unlock",
        "subsidized_market_maker_churn",
        "manual_burn",
        "route_pool_venue_specific_steering",
    }
)

REQUIRED_ATTACK_SCENARIOS = frozenset(
    {
        "wash_burn_roundtrip",
        "treasury_funded_self_unlock",
        "related_party_roundtrip",
        "non_excluded_manipulation_bound",
    }
)

REQUIRED_NON_CLAIMS = frozenset(
    {
        "no_automatic_sale_right",
        "no_legal_clearance",
        "no_tax_clearance",
        "no_market_price_support",
        "no_lockup_override",
        "no_insider_trading_clearance",
    }
)


def validate_burn_indexed_unlock_accelerator_v0(manifest: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    status = _str(obj.get("status"), "status", errors)
    activation_allowed = _bool(obj.get("activation_allowed"), "activation_allowed", errors)
    public_claims_allowed = _bool(obj.get("public_claims_allowed"), "public_claims_allowed", errors)
    counsel_review_required = _bool(obj.get("counsel_review_required"), "counsel_review_required", errors)
    counsel_review_status = _str(obj.get("counsel_review_status"), "counsel_review_status", errors)
    governance_review_status = _str(obj.get("governance_review_status"), "governance_review_status", errors)

    if status is not None and status not in ALLOWED_STATUSES:
        errors.append("status must be internal_research_only or testnet_only")
    if status == "internal_research_only" and activation_allowed is not False:
        errors.append("internal research accelerator must set activation_allowed=false")
    if public_claims_allowed is not False:
        errors.append("public_claims_allowed must be false")
    if counsel_review_required is not True:
        errors.append("counsel_review_required must be true")
    if counsel_review_status is not None and counsel_review_status not in ALLOWED_REVIEW_STATUS:
        errors.append("counsel_review_status is unsupported")
    if governance_review_status is not None and governance_review_status not in ALLOWED_REVIEW_STATUS:
        errors.append("governance_review_status is unsupported")
    if activation_allowed is True and (
        counsel_review_status != "complete" or governance_review_status != "complete"
    ):
        errors.append("activation requires complete counsel and governance review")

    controls = _validate_required_string_set(obj.get("controls"), field="controls", required=REQUIRED_CONTROLS)
    formula = _validate_formula(obj.get("formula"))
    allocations = _validate_allocations(
        obj.get("insider_allocations"),
        formula_facts=formula["facts"],
    )
    eligible_burn = _validate_eligible_burn(obj.get("eligible_burn"))
    attack_scenarios = _validate_attack_scenarios(
        obj.get("attack_scenarios"),
        formula_facts=formula["facts"],
        controls=set(controls["facts"].get("items", [])),
        exclusions=set(eligible_burn["required_exclusions"]["facts"].get("items", [])),
    )
    promotion_boundary = _validate_promotion_boundary(obj.get("promotion_boundary"))

    if formula["ok"] and allocations["ok"]:
        formula_cross_errors = _cross_check_formula_and_allocations(formula["facts"], allocations["facts"])
        if formula_cross_errors:
            formula["errors"].extend(formula_cross_errors)
            formula["ok"] = False

    for section_name, section in (
        ("controls", controls),
        ("formula", formula),
        ("insider_allocations", allocations),
        ("eligible_burn", eligible_burn),
        ("attack_scenarios", attack_scenarios),
        ("promotion_boundary", promotion_boundary),
    ):
        if not section["ok"]:
            errors.append(f"{section_name} rejected")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "facts": {
            "status": status,
            "activation_allowed": activation_allowed,
            "public_claims_allowed": public_claims_allowed,
            "counsel_review_required": counsel_review_required,
            "counsel_review_status": counsel_review_status,
            "governance_review_status": governance_review_status,
            "burn_share_bps": formula["facts"].get("burn_share_bps"),
            "per_epoch_extra_release_cap_token": formula["facts"].get(
                "per_epoch_extra_release_cap_token"
            ),
            "max_total_extra_release_token": formula["facts"].get(
                "max_total_extra_release_token"
            ),
            "minimum_effective_duration_months": formula["facts"].get(
                "minimum_effective_duration_months"
            ),
            "total_subject_token": allocations["facts"].get("total_subject_token"),
            "total_base_epoch_release_token": allocations["facts"].get(
                "total_base_epoch_release_token"
            ),
        },
        "controls": controls,
        "formula": formula,
        "insider_allocations": allocations,
        "eligible_burn": eligible_burn,
        "attack_scenarios": attack_scenarios,
        "promotion_boundary": promotion_boundary,
    }


def _validate_formula(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "formula", errors)
    epoch_unit = _str(obj.get("epoch_unit"), "formula.epoch_unit", errors)
    cliff_months = _int_ge(obj.get("cliff_months"), "formula.cliff_months", errors, 0)
    scheduled_duration_months = _int_ge(
        obj.get("scheduled_duration_months"),
        "formula.scheduled_duration_months",
        errors,
        1,
    )
    minimum_effective_duration_months = _int_ge(
        obj.get("minimum_effective_duration_months"),
        "formula.minimum_effective_duration_months",
        errors,
        1,
    )
    measurement_window_days = _int_ge(
        obj.get("measurement_window_days"),
        "formula.measurement_window_days",
        errors,
        30,
    )
    lag_days = _int_ge(obj.get("lag_days"), "formula.lag_days", errors, 7)
    burn_share_bps = _int_between(
        obj.get("burn_share_bps"),
        "formula.burn_share_bps",
        errors,
        0,
        2_500,
    )
    per_epoch_extra_release_cap_token = _int_ge(
        obj.get("per_epoch_extra_release_cap_token"),
        "formula.per_epoch_extra_release_cap_token",
        errors,
        1,
    )
    max_total_extra_release_token = _int_ge(
        obj.get("max_total_extra_release_token"),
        "formula.max_total_extra_release_token",
        errors,
        1,
    )
    total_subject_token = _int_ge(
        obj.get("total_subject_token"),
        "formula.total_subject_token",
        errors,
        1,
    )
    allocation_share_basis = _str(
        obj.get("allocation_share_basis"),
        "formula.allocation_share_basis",
        errors,
    )

    if epoch_unit is not None and epoch_unit not in ALLOWED_EPOCH_UNITS:
        errors.append("formula.epoch_unit is unsupported")
    if cliff_months is not None and cliff_months < 12:
        errors.append("formula.cliff_months must be >= 12")
    if (
        scheduled_duration_months is not None
        and minimum_effective_duration_months is not None
    ):
        if minimum_effective_duration_months > scheduled_duration_months:
            errors.append("formula.minimum_effective_duration_months exceeds scheduled duration")
        if minimum_effective_duration_months < 48:
            errors.append("formula.minimum_effective_duration_months must be >= 48")
    if (
        lag_days is not None
        and measurement_window_days is not None
        and lag_days > measurement_window_days
    ):
        errors.append("formula.lag_days must be <= measurement_window_days")
    if allocation_share_basis is not None and allocation_share_basis not in ALLOWED_ALLOCATION_SHARE_BASIS:
        errors.append("formula.allocation_share_basis is unsupported")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "epoch_unit": epoch_unit,
            "cliff_months": cliff_months,
            "scheduled_duration_months": scheduled_duration_months,
            "minimum_effective_duration_months": minimum_effective_duration_months,
            "measurement_window_days": measurement_window_days,
            "lag_days": lag_days,
            "burn_share_bps": burn_share_bps,
            "per_epoch_extra_release_cap_token": per_epoch_extra_release_cap_token,
            "max_total_extra_release_token": max_total_extra_release_token,
            "total_subject_token": total_subject_token,
            "allocation_share_basis": allocation_share_basis,
        },
    }


def _validate_allocations(value: Any, *, formula_facts: Mapping[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    raw = value
    if not isinstance(raw, list):
        errors.append("insider_allocations must be a list")
        raw = []

    scheduled_duration = _optional_int(formula_facts.get("scheduled_duration_months"))
    cliff_months_expected = _optional_int(formula_facts.get("cliff_months"))
    minimum_duration = _optional_int(formula_facts.get("minimum_effective_duration_months"))
    accelerated_month_limit = None
    if scheduled_duration is not None and minimum_duration is not None:
        accelerated_month_limit = scheduled_duration - minimum_duration

    reports: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    total_subject = 0
    total_base_epoch_release = 0
    total_max_extra = 0
    for index, item in enumerate(raw):
        item_errors: list[str] = []
        allocation = _mapping(item, f"insider_allocations[{index}]", item_errors)
        allocation_id = _str(allocation.get("id"), f"insider_allocations[{index}].id", item_errors)
        category = _str(
            allocation.get("category"),
            f"insider_allocations[{index}].category",
            item_errors,
        )
        amount = _int_ge(allocation.get("amount"), f"insider_allocations[{index}].amount", item_errors, 1)
        cliff_months = _int_ge(
            allocation.get("cliff_months"),
            f"insider_allocations[{index}].cliff_months",
            item_errors,
            0,
        )
        scheduled_duration_months = _int_ge(
            allocation.get("scheduled_duration_months"),
            f"insider_allocations[{index}].scheduled_duration_months",
            item_errors,
            1,
        )
        base_epoch_release_token = _int_ge(
            allocation.get("base_epoch_release_token"),
            f"insider_allocations[{index}].base_epoch_release_token",
            item_errors,
            1,
        )
        max_total_extra_release_token = _int_ge(
            allocation.get("max_total_extra_release_token"),
            f"insider_allocations[{index}].max_total_extra_release_token",
            item_errors,
            0,
        )

        if allocation_id is not None:
            if allocation_id in seen_ids:
                item_errors.append("insider allocation id must be unique")
            seen_ids.add(allocation_id)
        if category is not None and category not in {"founder", "team", "investor"}:
            item_errors.append("insider allocation category is unsupported")
        if (
            cliff_months_expected is not None
            and cliff_months is not None
            and cliff_months != cliff_months_expected
        ):
            item_errors.append("insider allocation cliff_months must match formula")
        if (
            scheduled_duration is not None
            and scheduled_duration_months is not None
            and scheduled_duration_months != scheduled_duration
        ):
            item_errors.append("insider allocation scheduled_duration_months must match formula")
        if (
            amount is not None
            and scheduled_duration_months is not None
            and base_epoch_release_token is not None
        ):
            if amount % scheduled_duration_months != 0:
                item_errors.append("insider allocation amount must divide evenly by scheduled duration")
            elif amount // scheduled_duration_months != base_epoch_release_token:
                item_errors.append("base_epoch_release_token must equal amount / scheduled_duration_months")
            total_subject += amount
            total_base_epoch_release += base_epoch_release_token
        if (
            accelerated_month_limit is not None
            and base_epoch_release_token is not None
            and max_total_extra_release_token is not None
            and max_total_extra_release_token > base_epoch_release_token * accelerated_month_limit
        ):
            item_errors.append("max_total_extra_release_token would reduce effective duration below minimum")
        if max_total_extra_release_token is not None:
            total_max_extra += max_total_extra_release_token

        reports.append(
            {
                "id": allocation_id,
                "ok": not item_errors,
                "status": "accepted" if not item_errors else "rejected",
                "errors": item_errors,
                "facts": {
                    "category": category,
                    "amount": amount,
                    "cliff_months": cliff_months,
                    "scheduled_duration_months": scheduled_duration_months,
                    "base_epoch_release_token": base_epoch_release_token,
                    "max_total_extra_release_token": max_total_extra_release_token,
                },
            }
        )

    required_ids = {"founder_original_rd", "core_team_future_contributors", "strategic_partners_investors_chain_partners"}
    missing = sorted(required_ids - seen_ids)
    if missing:
        errors.append("missing required insider allocations")
    if any(not report["ok"] for report in reports):
        errors.append("one or more insider allocations rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "allocation_count": len(reports),
            "missing_required_allocations": missing,
            "total_subject_token": total_subject,
            "total_base_epoch_release_token": total_base_epoch_release,
            "total_max_extra_release_token": total_max_extra,
        },
        "items": reports,
    }


def _cross_check_formula_and_allocations(
    formula_facts: Mapping[str, Any],
    allocation_facts: Mapping[str, Any],
) -> list[str]:
    errors: list[str] = []
    total_subject_formula = _optional_int(formula_facts.get("total_subject_token"))
    total_subject_allocations = _optional_int(allocation_facts.get("total_subject_token"))
    max_total_formula = _optional_int(formula_facts.get("max_total_extra_release_token"))
    total_max_extra_allocations = _optional_int(allocation_facts.get("total_max_extra_release_token"))
    total_base_epoch_release = _optional_int(allocation_facts.get("total_base_epoch_release_token"))
    scheduled_duration = _optional_int(formula_facts.get("scheduled_duration_months"))
    minimum_duration = _optional_int(formula_facts.get("minimum_effective_duration_months"))
    per_epoch_cap = _optional_int(formula_facts.get("per_epoch_extra_release_cap_token"))
    if (
        total_subject_formula is not None
        and total_subject_allocations is not None
        and total_subject_formula != total_subject_allocations
    ):
        errors.append("formula.total_subject_token must equal insider allocation total")
    if (
        max_total_formula is not None
        and total_max_extra_allocations is not None
        and max_total_formula != total_max_extra_allocations
    ):
        errors.append("formula.max_total_extra_release_token must equal allocation extra-release total")
    if (
        total_base_epoch_release is not None
        and scheduled_duration is not None
        and minimum_duration is not None
        and max_total_formula is not None
    ):
        max_allowed = total_base_epoch_release * (scheduled_duration - minimum_duration)
        if max_total_formula > max_allowed:
            errors.append("max_total_extra_release_token would reduce aggregate effective duration below minimum")
    if per_epoch_cap is not None and total_base_epoch_release is not None and per_epoch_cap > total_base_epoch_release:
        errors.append("per_epoch_extra_release_cap_token exceeds total base epoch release")
    return errors


def _validate_eligible_burn(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "eligible_burn", errors)
    sources = _validate_required_string_set(
        obj.get("sources"),
        field="eligible_burn.sources",
        required=frozenset({"protocol_fee_buy_and_burn"}),
    )
    exclusions = _validate_required_string_set(
        obj.get("required_exclusions"),
        field="eligible_burn.required_exclusions",
        required=REQUIRED_EXCLUSIONS,
    )
    requires_receipt_root = _bool(obj.get("requires_receipt_root"), "eligible_burn.requires_receipt_root", errors)
    manual_burn_counts = _bool(obj.get("manual_burn_counts"), "eligible_burn.manual_burn_counts", errors)
    treasury_funded_burn_counts = _bool(
        obj.get("treasury_funded_burn_counts"),
        "eligible_burn.treasury_funded_burn_counts",
        errors,
    )
    related_party_burn_counts = _bool(
        obj.get("related_party_burn_counts"),
        "eligible_burn.related_party_burn_counts",
        errors,
    )
    route_pool_venue_specific_burn_counts = _bool(
        obj.get("route_pool_venue_specific_burn_counts"),
        "eligible_burn.route_pool_venue_specific_burn_counts",
        errors,
    )
    if requires_receipt_root is not True:
        errors.append("eligible_burn.requires_receipt_root must be true")
    if manual_burn_counts is not False:
        errors.append("eligible_burn.manual_burn_counts must be false")
    if treasury_funded_burn_counts is not False:
        errors.append("eligible_burn.treasury_funded_burn_counts must be false")
    if related_party_burn_counts is not False:
        errors.append("eligible_burn.related_party_burn_counts must be false")
    if route_pool_venue_specific_burn_counts is not False:
        errors.append("eligible_burn.route_pool_venue_specific_burn_counts must be false")
    if not sources["ok"]:
        errors.append("eligible burn missing required source")
    if not exclusions["ok"]:
        errors.append("eligible burn missing required exclusions")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "requires_receipt_root": requires_receipt_root,
            "manual_burn_counts": manual_burn_counts,
            "treasury_funded_burn_counts": treasury_funded_burn_counts,
            "related_party_burn_counts": related_party_burn_counts,
            "route_pool_venue_specific_burn_counts": route_pool_venue_specific_burn_counts,
        },
        "sources": sources,
        "required_exclusions": exclusions,
    }


def _validate_attack_scenarios(
    value: Any,
    *,
    formula_facts: Mapping[str, Any],
    controls: set[str],
    exclusions: set[str],
) -> dict[str, Any]:
    errors: list[str] = []
    raw = value
    if not isinstance(raw, list):
        errors.append("attack_scenarios must be a list")
        raw = []

    seen_ids: set[str] = set()
    reports: list[dict[str, Any]] = []
    burn_share_bps = _optional_int(formula_facts.get("burn_share_bps"))
    per_epoch_cap = _optional_int(formula_facts.get("per_epoch_extra_release_cap_token"))
    for index, item in enumerate(raw):
        item_errors: list[str] = []
        scenario = _mapping(item, f"attack_scenarios[{index}]", item_errors)
        scenario_id = _str(scenario.get("id"), f"attack_scenarios[{index}].id", item_errors)
        condition = _str(scenario.get("condition"), f"attack_scenarios[{index}].condition", item_errors)
        expected_result = _str(
            scenario.get("expected_result"),
            f"attack_scenarios[{index}].expected_result",
            item_errors,
        )
        excluded_by_controls = _bool(
            scenario.get("excluded_by_controls"),
            f"attack_scenarios[{index}].excluded_by_controls",
            item_errors,
        )
        exclusion_control = _str(
            scenario.get("exclusion_control"),
            f"attack_scenarios[{index}].exclusion_control",
            item_errors,
        )
        facts: dict[str, Any] = {
            "condition": condition,
            "expected_result": expected_result,
            "excluded_by_controls": excluded_by_controls,
            "exclusion_control": exclusion_control,
        }
        if scenario_id is not None:
            if scenario_id in seen_ids:
                item_errors.append("attack scenario id must be unique")
            seen_ids.add(scenario_id)
        if expected_result is not None and expected_result not in ALLOWED_EXPECTED_RESULTS:
            item_errors.append("attack scenario expected_result is unsupported")
        if expected_result == "rejected":
            if excluded_by_controls is not True:
                item_errors.append("rejected attack scenarios must set excluded_by_controls=true")
            if exclusion_control is not None and exclusion_control not in controls and exclusion_control not in exclusions:
                item_errors.append("attack scenario exclusion_control is not a declared control or exclusion")
        if expected_result == "bounded":
            _validate_bounded_attack_scenario(
                scenario,
                index=index,
                errors=item_errors,
                facts=facts,
                burn_share_bps=burn_share_bps,
                per_epoch_cap=per_epoch_cap,
            )
        reports.append(
            {
                "id": scenario_id,
                "ok": not item_errors,
                "status": "accepted" if not item_errors else "rejected",
                "errors": item_errors,
                "facts": facts,
            }
        )

    missing = sorted(REQUIRED_ATTACK_SCENARIOS - seen_ids)
    if missing:
        errors.append("missing required attack scenarios")
    if any(not report["ok"] for report in reports):
        errors.append("one or more attack scenarios rejected")
    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "attack_scenario_count": len(reports),
            "missing_required_attack_scenarios": missing,
        },
        "items": reports,
    }


def _validate_bounded_attack_scenario(
    scenario: Mapping[str, Any],
    *,
    index: int,
    errors: list[str],
    facts: dict[str, Any],
    burn_share_bps: int | None,
    per_epoch_cap: int | None,
) -> None:
    manipulated_burn_token_bound = _int_ge(
        scenario.get("manipulated_burn_token_bound"),
        f"attack_scenarios[{index}].manipulated_burn_token_bound",
        errors,
        0,
    )
    attacker_allocation_share_bps = _int_between(
        scenario.get("attacker_allocation_share_bps"),
        f"attack_scenarios[{index}].attacker_allocation_share_bps",
        errors,
        0,
        BPS_SCALE,
    )
    exit_value = _fraction_obj(
        scenario.get("exit_value_per_extra_unlocked_token_quote"),
        f"attack_scenarios[{index}].exit_value_per_extra_unlocked_token_quote",
        errors,
    )
    min_cost = _fraction_obj(
        scenario.get("min_cost_per_eligible_burn_token_quote"),
        f"attack_scenarios[{index}].min_cost_per_eligible_burn_token_quote",
        errors,
    )
    detection_probability_bps = _int_between(
        scenario.get("detection_probability_bps"),
        f"attack_scenarios[{index}].detection_probability_bps",
        errors,
        0,
        BPS_SCALE,
    )
    slash_amount_quote = _int_ge(
        scenario.get("slash_amount_quote"),
        f"attack_scenarios[{index}].slash_amount_quote",
        errors,
        0,
    )
    future_value_lost_quote = _int_ge(
        scenario.get("future_value_lost_quote"),
        f"attack_scenarios[{index}].future_value_lost_quote",
        errors,
        0,
    )
    if None in (
        manipulated_burn_token_bound,
        attacker_allocation_share_bps,
        burn_share_bps,
        per_epoch_cap,
        detection_probability_bps,
        slash_amount_quote,
        future_value_lost_quote,
    ) or exit_value is None or min_cost is None:
        return

    extra_unlocked = min(
        int(per_epoch_cap),
        (int(manipulated_burn_token_bound) * int(burn_share_bps)) // BPS_SCALE,
    )
    attacker_extra = Fraction(extra_unlocked * int(attacker_allocation_share_bps), BPS_SCALE)
    benefit = attacker_extra * exit_value
    burn_cost = Fraction(int(manipulated_burn_token_bound), 1) * min_cost
    expected_penalty = Fraction(int(detection_probability_bps), BPS_SCALE) * int(slash_amount_quote)
    downside = burn_cost + expected_penalty + int(future_value_lost_quote)
    profit = benefit - downside
    if profit > 0:
        errors.append("manipulated burn unlock attack is profitable in bounded model")
    facts.update(
        {
            "manipulated_burn_token_bound": int(manipulated_burn_token_bound),
            "attacker_allocation_share_bps": int(attacker_allocation_share_bps),
            "extra_unlocked_token": extra_unlocked,
            "attacker_extra_unlocked_token": _fraction_str(attacker_extra),
            "benefit_quote": _fraction_str(benefit),
            "burn_cost_quote": _fraction_str(burn_cost),
            "expected_penalty_quote": _fraction_str(expected_penalty),
            "future_value_lost_quote": int(future_value_lost_quote),
            "downside_quote": _fraction_str(downside),
            "profit_quote": _fraction_str(profit),
        }
    )


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
    non_claims = _validate_required_string_set(
        obj.get("non_claims"),
        field="promotion_boundary.non_claims",
        required=REQUIRED_NON_CLAIMS,
    )
    if public_claim_allowed is not False:
        errors.append("promotion_boundary.public_claim_allowed must be false")
    if claim_registry_entry_allowed is not False:
        errors.append("promotion_boundary.claim_registry_entry_allowed must be false")
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


def _validate_required_string_set(value: Any, *, field: str, required: frozenset[str]) -> dict[str, Any]:
    errors: list[str] = []
    raw = value
    if not isinstance(raw, list):
        errors.append(f"{field} must be a list")
        raw = []
    items: set[str] = set()
    for index, item in enumerate(raw):
        if not isinstance(item, str) or not item:
            errors.append(f"{field}[{index}] must be a non-empty string")
            continue
        items.add(item)
    missing = sorted(required - items)
    if missing:
        errors.append(f"{field} missing required items")
    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "items": sorted(items),
            "missing_required": missing,
        },
    }


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if isinstance(value, str) and value:
        return value
    errors.append(f"{name} must be a non-empty string")
    return None


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if isinstance(value, bool):
        return value
    errors.append(f"{name} must be a boolean")
    return None


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
    if parsed is None:
        return None
    if parsed > maximum:
        errors.append(f"{name} must be <= {maximum}")
        return None
    return parsed


def _optional_int(value: Any) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool):
        return int(value)
    return None


def _fraction_obj(value: Any, name: str, errors: list[str]) -> Fraction | None:
    obj = _mapping(value, name, errors)
    numerator = _int_ge(obj.get("numerator"), f"{name}.numerator", errors, 0)
    denominator = _int_ge(obj.get("denominator"), f"{name}.denominator", errors, 1)
    if numerator is None or denominator is None:
        return None
    return Fraction(numerator, denominator)


def _fraction_str(value: Fraction | None) -> str | None:
    if value is None:
        return None
    return f"{value.numerator}/{value.denominator}"


def _load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = validate_burn_indexed_unlock_accelerator_v0(_load_json(args.manifest))
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
