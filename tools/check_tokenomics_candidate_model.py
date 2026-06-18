#!/usr/bin/env python3
"""Validate an internal ZENO tokenomics candidate model."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Mapping

MANIFEST_SCHEMA = "zenodex.tokenomics.candidate_model.v0"
REPORT_SCHEMA = "zenodex.tokenomics.candidate_model_report.v0"
TOTAL_SUPPLY = 1_000_000_000
BPS_SCALE = 10_000

REQUIRED_LAUNCH_GATES = {
    "covered_user_interface_boundary_gate",
    "burn_indexed_unlock_accelerator_gate",
    "economic_games_boundary_gate",
    "production_boundary_gate",
    "claims_scope_gate",
    "proof_coverage_matrix_gate",
    "reward_safety_envelope_gate",
    "treasury_custody_boundary_gate",
    "tokenomics_counsel_review",
}
REQUIRED_VALUE_ROLES = {"oracle_reporter", "operator", "proof_miner"}
INSIDER_CATEGORIES = {"advisor", "founder", "investor", "team"}
REQUIRED_ALLOCATIONS = {
    "founder_original_rd": {"category": "founder", "amount": 150_000_000},
    "core_team_future_contributors": {"category": "team", "amount": 100_000_000},
    "dao_protocol_treasury": {"category": "treasury", "amount": 250_000_000},
    "ecosystem_lp_solver_operator_proof_incentives": {"category": "ecosystem", "amount": 250_000_000},
    "community_retroactive_airdrop_testnet_users": {"category": "community", "amount": 100_000_000},
    "security_audits_bounties_insurance_reserve": {"category": "security", "amount": 50_000_000},
    "liquidity_bootstrap_market_making": {"category": "liquidity", "amount": 50_000_000},
    "strategic_partners_investors_chain_partners": {"category": "investor", "amount": 50_000_000},
}
REQUIRED_GAMIFICATION_CONTROLS = {
    "objective_rules",
    "eligible_activity_receipts",
    "non_wash_receipts",
    "sybil_abuse_gate",
    "covered_user_interface_boundary",
    "terms_disclosure",
    "no_specific_transaction_inducement",
    "no_passive_yield_marketing",
}
REQUIRED_NON_CLAIMS = {
    "economic_security_complete",
    "legal_clearance",
    "public_launch_readiness",
    "secondary_market_value",
}


def validate_candidate_model_v0(manifest: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    total_supply = _int_ge(obj.get("total_supply"), "total_supply", errors, 1)
    if total_supply is not None and total_supply != TOTAL_SUPPLY:
        errors.append("total_supply must equal 1000000000")

    vesting_policy = _validate_vesting_policy(obj.get("vesting_policy"))
    allocations = _validate_allocations(
        obj.get("allocations"),
        expected_supply=total_supply,
        vesting_policy=vesting_policy,
    )
    gamification_policy = _validate_gamification_policy(obj.get("gamification_policy"))
    launch = _validate_launch(obj.get("launch"))
    value_capture = _validate_value_capture(obj.get("value_capture"))
    roles = _validate_roles(
        obj.get("roles"),
        max_reward_spend_quote=value_capture["facts"].get("max_reward_spend_quote"),
    )
    promotion_boundary = _validate_promotion_boundary(obj.get("promotion_boundary"))

    for section_name, section in (
        ("vesting_policy", vesting_policy),
        ("allocations", allocations),
        ("gamification_policy", gamification_policy),
        ("launch", launch),
        ("value_capture", value_capture),
        ("roles", roles),
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
            "total_supply": total_supply,
            "allocation_total": allocations["facts"].get("allocation_total"),
            "circulating_at_launch": allocations["facts"].get("circulating_at_launch"),
            "epoch_spend_cap_quote": value_capture["facts"].get("epoch_spend_cap_quote"),
            "role_max_reward_per_epoch_quote": roles["facts"].get(
                "role_max_reward_per_epoch_quote"
            ),
        },
        "required_tokenomics_fields": _required_tokenomics_fields(
            total_supply=total_supply,
            allocations=allocations,
            gamification_policy=gamification_policy,
            launch=launch,
            value_capture=value_capture,
            roles=roles,
            promotion_boundary=promotion_boundary,
        ),
        "vesting_policy": vesting_policy,
        "allocations": allocations,
        "gamification_policy": gamification_policy,
        "launch": launch,
        "value_capture": value_capture,
        "roles": roles,
        "promotion_boundary": promotion_boundary,
    }


def _validate_vesting_policy(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "vesting_policy", errors)
    max_initial_unlock_bps = _int_between(
        obj.get("max_initial_unlock_bps"),
        "vesting_policy.max_initial_unlock_bps",
        errors,
        0,
        BPS_SCALE,
    )
    max_launch_circulation_bps = _int_between(
        obj.get("max_launch_circulation_bps"),
        "vesting_policy.max_launch_circulation_bps",
        errors,
        0,
        BPS_SCALE,
    )
    min_insider_cliff_months = _int_ge(
        obj.get("min_insider_cliff_months"),
        "vesting_policy.min_insider_cliff_months",
        errors,
        0,
    )
    min_insider_duration_months = _int_ge(
        obj.get("min_insider_duration_months"),
        "vesting_policy.min_insider_duration_months",
        errors,
        1,
    )
    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "max_initial_unlock_bps": max_initial_unlock_bps,
            "max_launch_circulation_bps": max_launch_circulation_bps,
            "min_insider_cliff_months": min_insider_cliff_months,
            "min_insider_duration_months": min_insider_duration_months,
        },
    }


def _validate_allocations(
    value: Any,
    *,
    expected_supply: int | None,
    vesting_policy: Mapping[str, Any],
) -> dict[str, Any]:
    errors: list[str] = []
    allocations_raw = value
    if not isinstance(allocations_raw, list):
        errors.append("allocations must be a list")
        allocations_raw = []

    policy = vesting_policy.get("facts", {})
    max_initial_unlock_bps = _optional_int(policy.get("max_initial_unlock_bps"))
    max_launch_circulation_bps = _optional_int(policy.get("max_launch_circulation_bps"))
    min_insider_cliff_months = _optional_int(policy.get("min_insider_cliff_months"))
    min_insider_duration_months = _optional_int(policy.get("min_insider_duration_months"))

    allocation_reports: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    required_allocation_mismatches: list[str] = []
    allocation_total = 0
    circulating_at_launch = 0
    for index, item in enumerate(allocations_raw):
        item_errors: list[str] = []
        allocation = _mapping(item, f"allocations[{index}]", item_errors)
        allocation_id = _str(allocation.get("id"), f"allocations[{index}].id", item_errors)
        category = _str(allocation.get("category"), f"allocations[{index}].category", item_errors)
        amount = _int_ge(allocation.get("amount"), f"allocations[{index}].amount", item_errors, 1)
        if allocation_id is not None:
            if allocation_id in seen_ids:
                item_errors.append("allocation id must be unique")
            seen_ids.add(allocation_id)
            expected = REQUIRED_ALLOCATIONS.get(allocation_id)
            if expected is not None:
                if category is not None and category != expected["category"]:
                    item_errors.append("allocation category does not match required distribution")
                    required_allocation_mismatches.append(allocation_id)
                if amount is not None and amount != expected["amount"]:
                    item_errors.append("allocation amount does not match required distribution")
                    required_allocation_mismatches.append(allocation_id)

        vesting = _mapping(allocation.get("vesting"), f"allocations[{index}].vesting", item_errors)
        cliff_months = _int_ge(
            vesting.get("cliff_months"),
            f"allocations[{index}].vesting.cliff_months",
            item_errors,
            0,
        )
        duration_months = _int_ge(
            vesting.get("duration_months"),
            f"allocations[{index}].vesting.duration_months",
            item_errors,
            1,
        )
        initial_unlock_bps = _int_between(
            vesting.get("initial_unlock_bps"),
            f"allocations[{index}].vesting.initial_unlock_bps",
            item_errors,
            0,
            BPS_SCALE,
        )

        initial_unlocked = None
        monthly_release = None
        if (
            amount is not None
            and cliff_months is not None
            and duration_months is not None
            and initial_unlock_bps is not None
        ):
            allocation_total += amount
            if cliff_months > duration_months:
                item_errors.append("vesting cliff_months must be <= duration_months")
            if max_initial_unlock_bps is not None and initial_unlock_bps > max_initial_unlock_bps:
                item_errors.append("initial_unlock_bps exceeds vesting policy cap")
            if category in INSIDER_CATEGORIES:
                if (
                    min_insider_cliff_months is not None
                    and cliff_months < min_insider_cliff_months
                ):
                    item_errors.append("insider allocation cliff below policy minimum")
                if (
                    min_insider_duration_months is not None
                    and duration_months < min_insider_duration_months
                ):
                    item_errors.append("insider allocation duration below policy minimum")

            initial_numerator = amount * initial_unlock_bps
            if initial_numerator % BPS_SCALE != 0:
                item_errors.append("initial unlock is not an integer token amount")
            else:
                initial_unlocked = initial_numerator // BPS_SCALE
                circulating_at_launch += initial_unlocked

            remaining = amount - (initial_unlocked or 0)
            if remaining % duration_months != 0:
                item_errors.append("linear monthly vesting is not an integer token amount")
            else:
                monthly_release = remaining // duration_months

        allocation_reports.append(
            {
                "id": allocation_id,
                "category": category,
                "ok": not item_errors,
                "status": "accepted" if not item_errors else "rejected",
                "errors": item_errors,
                "facts": {
                    "amount": amount,
                    "initial_unlocked": initial_unlocked,
                    "monthly_release": monthly_release,
                },
            }
        )

    if expected_supply is not None and allocation_total != expected_supply:
        errors.append("allocation amounts must sum to total_supply")
    missing_required_allocations = sorted(set(REQUIRED_ALLOCATIONS) - seen_ids)
    if missing_required_allocations:
        errors.append("missing required allocation buckets")
    launch_circulation_bps_within_cap = None
    if expected_supply is not None and max_launch_circulation_bps is not None:
        launch_circulation_bps_within_cap = (
            circulating_at_launch * BPS_SCALE <= expected_supply * max_launch_circulation_bps
        )
        if not launch_circulation_bps_within_cap:
            errors.append("circulating_at_launch exceeds vesting_policy.max_launch_circulation_bps")
    if any(not report["ok"] for report in allocation_reports):
        errors.append("one or more allocations rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "allocation_total": allocation_total,
            "circulating_at_launch": circulating_at_launch,
            "allocation_count": len(allocation_reports),
            "allocation_ids": sorted(seen_ids),
            "missing_required_allocations": missing_required_allocations,
            "required_allocation_mismatches": sorted(set(required_allocation_mismatches)),
            "launch_circulation_bps_within_cap": launch_circulation_bps_within_cap,
        },
        "items": allocation_reports,
    }


def _validate_gamification_policy(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "gamification_policy", errors)
    xp_transferable = _bool(obj.get("xp_transferable"), "gamification_policy.xp_transferable", errors)
    xp_redeemable_for_tokens = _bool(
        obj.get("xp_redeemable_for_tokens"),
        "gamification_policy.xp_redeemable_for_tokens",
        errors,
    )
    xp_cash_value = _bool(obj.get("xp_cash_value"), "gamification_policy.xp_cash_value", errors)
    xp_secondary_market_allowed = _bool(
        obj.get("xp_secondary_market_allowed"),
        "gamification_policy.xp_secondary_market_allowed",
        errors,
    )
    xp_entitlement_to_discount_or_feature_waiver = _bool(
        obj.get("xp_entitlement_to_discount_or_feature_waiver"),
        "gamification_policy.xp_entitlement_to_discount_or_feature_waiver",
        errors,
    )
    economic_benefits_require_separate_budget = _bool(
        obj.get("economic_benefits_require_separate_budget"),
        "gamification_policy.economic_benefits_require_separate_budget",
        errors,
    )
    economic_benefits_require_counsel_review = _bool(
        obj.get("economic_benefits_require_counsel_review"),
        "gamification_policy.economic_benefits_require_counsel_review",
        errors,
    )
    token_distribution_uses_separate_program = _bool(
        obj.get("token_distribution_uses_separate_program"),
        "gamification_policy.token_distribution_uses_separate_program",
        errors,
    )
    controls = _validate_required_string_set(
        obj.get("controls"),
        field="gamification_policy.controls",
        required=REQUIRED_GAMIFICATION_CONTROLS,
    )

    if xp_transferable is not False:
        errors.append("gamification_policy.xp_transferable must be false")
    if xp_redeemable_for_tokens is not False:
        errors.append("gamification_policy.xp_redeemable_for_tokens must be false")
    if xp_cash_value is not False:
        errors.append("gamification_policy.xp_cash_value must be false")
    if xp_secondary_market_allowed is not False:
        errors.append("gamification_policy.xp_secondary_market_allowed must be false")
    if xp_entitlement_to_discount_or_feature_waiver is not False:
        errors.append("gamification_policy.xp_entitlement_to_discount_or_feature_waiver must be false")
    if economic_benefits_require_separate_budget is not True:
        errors.append("gamification_policy.economic_benefits_require_separate_budget must be true")
    if economic_benefits_require_counsel_review is not True:
        errors.append("gamification_policy.economic_benefits_require_counsel_review must be true")
    if token_distribution_uses_separate_program is not True:
        errors.append("gamification_policy.token_distribution_uses_separate_program must be true")
    if not controls["ok"]:
        errors.append("gamification policy missing required controls")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "xp_transferable": xp_transferable,
            "xp_redeemable_for_tokens": xp_redeemable_for_tokens,
            "xp_cash_value": xp_cash_value,
            "xp_secondary_market_allowed": xp_secondary_market_allowed,
            "xp_entitlement_to_discount_or_feature_waiver": xp_entitlement_to_discount_or_feature_waiver,
            "economic_benefits_require_separate_budget": economic_benefits_require_separate_budget,
            "economic_benefits_require_counsel_review": economic_benefits_require_counsel_review,
            "token_distribution_uses_separate_program": token_distribution_uses_separate_program,
        },
        "controls": controls,
    }


def _validate_launch(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "launch", errors)
    public_launch_allowed = _bool(obj.get("public_launch_allowed"), "launch.public_launch_allowed", errors)
    counsel_review_required = _bool(
        obj.get("counsel_review_required"),
        "launch.counsel_review_required",
        errors,
    )
    counsel_review_status = _str(
        obj.get("counsel_review_status"),
        "launch.counsel_review_status",
        errors,
    )

    if public_launch_allowed is True:
        errors.append("public_launch_allowed must be false for internal candidate model")
    if counsel_review_required is not True:
        errors.append("counsel_review_required must be true")

    gates_raw = obj.get("preconditions")
    if not isinstance(gates_raw, list):
        errors.append("launch.preconditions must be a list")
        gates_raw = []

    gate_reports: list[dict[str, Any]] = []
    seen_gates: set[str] = set()
    for index, item in enumerate(gates_raw):
        gate_errors: list[str] = []
        gate = _mapping(item, f"launch.preconditions[{index}]", gate_errors)
        gate_id = _str(gate.get("id"), f"launch.preconditions[{index}].id", gate_errors)
        status = _str(gate.get("status"), f"launch.preconditions[{index}].status", gate_errors)
        evidence = _str(
            gate.get("evidence"),
            f"launch.preconditions[{index}].evidence",
            gate_errors,
        )
        if gate_id is not None:
            if gate_id in seen_gates:
                gate_errors.append("launch precondition id must be unique")
            seen_gates.add(gate_id)
        if status is not None and status not in {"blocked", "passed", "required_not_complete"}:
            gate_errors.append("launch precondition status is unsupported")
        if (
            gate_id == "tokenomics_counsel_review"
            and status == "passed"
            and counsel_review_status != "complete"
        ):
            gate_errors.append("counsel gate cannot pass before counsel review complete")
        gate_reports.append(
            {
                "id": gate_id,
                "status": status,
                "evidence": evidence,
                "ok": not gate_errors,
                "errors": gate_errors,
            }
        )

    missing_gates = sorted(REQUIRED_LAUNCH_GATES - seen_gates)
    if missing_gates:
        errors.append("missing required launch preconditions")
    if any(not report["ok"] for report in gate_reports):
        errors.append("one or more launch preconditions rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "public_launch_allowed": public_launch_allowed,
            "counsel_review_required": counsel_review_required,
            "counsel_review_status": counsel_review_status,
            "missing_required_preconditions": missing_gates,
            "precondition_ids": sorted(seen_gates),
        },
        "preconditions": gate_reports,
    }


def _validate_value_capture(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "value_capture", errors)
    funded_epoch_budget_quote = _int_ge(
        obj.get("funded_epoch_budget_quote"),
        "value_capture.funded_epoch_budget_quote",
        errors,
        0,
    )
    max_reward_spend_quote = _int_ge(
        obj.get("max_reward_spend_quote"),
        "value_capture.max_reward_spend_quote",
        errors,
        0,
    )
    max_rebate_spend_quote = _int_ge(
        obj.get("max_rebate_spend_quote"),
        "value_capture.max_rebate_spend_quote",
        errors,
        0,
    )
    max_buyback_spend_quote = _int_ge(
        obj.get("max_buyback_spend_quote"),
        "value_capture.max_buyback_spend_quote",
        errors,
        0,
    )
    max_cover_spend_quote = _int_ge(
        obj.get("max_cover_spend_quote"),
        "value_capture.max_cover_spend_quote",
        errors,
        0,
    )

    spend_cap = None
    if None not in (
        funded_epoch_budget_quote,
        max_reward_spend_quote,
        max_rebate_spend_quote,
        max_buyback_spend_quote,
        max_cover_spend_quote,
    ):
        spend_cap = (
            int(max_reward_spend_quote)
            + int(max_rebate_spend_quote)
            + int(max_buyback_spend_quote)
            + int(max_cover_spend_quote)
        )
        if spend_cap > int(funded_epoch_budget_quote):
            errors.append("epoch spend caps exceed funded_epoch_budget_quote")

    fee_split_bps = _mapping(obj.get("fee_split_bps"), "value_capture.fee_split_bps", errors)
    split_total = 0
    split_reports: dict[str, int | None] = {}
    for split_id, split_value in fee_split_bps.items():
        if not isinstance(split_id, str) or split_id == "":
            errors.append("value_capture.fee_split_bps keys must be non-empty strings")
            continue
        parsed = _int_between(
            split_value,
            f"value_capture.fee_split_bps.{split_id}",
            errors,
            0,
            BPS_SCALE,
        )
        split_reports[split_id] = parsed
        if parsed is not None:
            split_total += parsed
    if split_total > BPS_SCALE:
        errors.append("fee_split_bps total must be <= 10000")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "funded_epoch_budget_quote": funded_epoch_budget_quote,
            "max_reward_spend_quote": max_reward_spend_quote,
            "epoch_spend_cap_quote": spend_cap,
            "fee_split_total_bps": split_total,
        },
        "fee_split_bps": split_reports,
    }


def _validate_roles(value: Any, *, max_reward_spend_quote: Any) -> dict[str, Any]:
    errors: list[str] = []
    roles_raw = value
    if not isinstance(roles_raw, list):
        errors.append("roles must be a list")
        roles_raw = []

    role_reports: list[dict[str, Any]] = []
    seen_roles: set[str] = set()
    total_max_reward = 0
    for index, item in enumerate(roles_raw):
        role_errors: list[str] = []
        role = _mapping(item, f"roles[{index}]", role_errors)
        role_id = _str(role.get("id"), f"roles[{index}].id", role_errors)
        value_moving = _bool(role.get("value_moving"), f"roles[{index}].value_moving", role_errors)
        bond_amount_quote = _int_ge(
            role.get("bond_amount_quote"),
            f"roles[{index}].bond_amount_quote",
            role_errors,
            0,
        )
        slash_amount_quote = _int_ge(
            role.get("slash_amount_quote"),
            f"roles[{index}].slash_amount_quote",
            role_errors,
            0,
        )
        max_defect_gain_quote = _int_ge(
            role.get("max_defect_gain_quote"),
            f"roles[{index}].max_defect_gain_quote",
            role_errors,
            0,
        )
        future_value_lost_quote = _int_ge(
            role.get("future_value_lost_quote"),
            f"roles[{index}].future_value_lost_quote",
            role_errors,
            0,
        )
        max_reward_per_epoch_quote = _int_ge(
            role.get("max_reward_per_epoch_quote"),
            f"roles[{index}].max_reward_per_epoch_quote",
            role_errors,
            0,
        )
        withdrawal_delay_epochs = _int_ge(
            role.get("withdrawal_delay_epochs"),
            f"roles[{index}].withdrawal_delay_epochs",
            role_errors,
            1,
        )
        if role_id is not None:
            if role_id in seen_roles:
                role_errors.append("role id must be unique")
            seen_roles.add(role_id)
        if max_reward_per_epoch_quote is not None:
            total_max_reward += max_reward_per_epoch_quote

        if (
            value_moving is not None
            and bond_amount_quote is not None
            and slash_amount_quote is not None
            and max_defect_gain_quote is not None
            and future_value_lost_quote is not None
            and max_reward_per_epoch_quote is not None
            and withdrawal_delay_epochs is not None
        ):
            if role_id in REQUIRED_VALUE_ROLES and value_moving is not True:
                role_errors.append("required value role must be marked value_moving")
            if value_moving:
                if bond_amount_quote <= 0:
                    role_errors.append("value-moving role must have positive bond")
                if slash_amount_quote <= 0:
                    role_errors.append("value-moving role must have positive slash amount")
                if slash_amount_quote > bond_amount_quote:
                    role_errors.append("slash_amount_quote exceeds bond_amount_quote")
                if bond_amount_quote < max_reward_per_epoch_quote:
                    role_errors.append("bond_amount_quote below max_reward_per_epoch_quote")
                if max_defect_gain_quote > slash_amount_quote + future_value_lost_quote:
                    role_errors.append("max_defect_gain_quote exceeds bonded downside")
                if withdrawal_delay_epochs <= 0:
                    role_errors.append("withdrawal delay must be positive for value-moving role")

        role_reports.append(
            {
                "id": role_id,
                "ok": not role_errors,
                "status": "accepted" if not role_errors else "rejected",
                "errors": role_errors,
                "facts": {
                    "value_moving": value_moving,
                    "bond_amount_quote": bond_amount_quote,
                    "slash_amount_quote": slash_amount_quote,
                    "max_defect_gain_quote": max_defect_gain_quote,
                    "future_value_lost_quote": future_value_lost_quote,
                    "max_reward_per_epoch_quote": max_reward_per_epoch_quote,
                },
            }
        )

    missing_roles = sorted(REQUIRED_VALUE_ROLES - seen_roles)
    if missing_roles:
        errors.append("missing required value-moving roles")
    max_reward_budget = _optional_int(max_reward_spend_quote)
    if max_reward_budget is not None and total_max_reward > max_reward_budget:
        errors.append("role max_reward_per_epoch total exceeds value_capture.max_reward_spend_quote")
    if any(not report["ok"] for report in role_reports):
        errors.append("one or more roles rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "missing_required_roles": missing_roles,
            "role_max_reward_per_epoch_quote": total_max_reward,
            "max_reward_spend_quote": max_reward_budget,
        },
        "items": role_reports,
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
    if public_claim_allowed is True:
        errors.append("public_claim_allowed must be false")
    if claim_registry_entry_allowed is True:
        errors.append("claim_registry_entry_allowed must be false")

    non_claims_raw = obj.get("non_claims")
    if not isinstance(non_claims_raw, list):
        errors.append("promotion_boundary.non_claims must be a list")
        non_claims_raw = []
    non_claims: set[str] = set()
    for index, item in enumerate(non_claims_raw):
        parsed = _str(item, f"promotion_boundary.non_claims[{index}]", errors)
        if parsed is not None:
            non_claims.add(parsed)
    missing_non_claims = sorted(REQUIRED_NON_CLAIMS - non_claims)
    if missing_non_claims:
        errors.append("promotion boundary missing required non-claims")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "public_claim_allowed": public_claim_allowed,
            "claim_registry_entry_allowed": claim_registry_entry_allowed,
            "missing_required_non_claims": missing_non_claims,
        },
        "non_claims": sorted(non_claims),
    }


def _required_tokenomics_fields(
    *,
    total_supply: int | None,
    allocations: Mapping[str, Any],
    gamification_policy: Mapping[str, Any],
    launch: Mapping[str, Any],
    value_capture: Mapping[str, Any],
    roles: Mapping[str, Any],
    promotion_boundary: Mapping[str, Any],
) -> dict[str, bool]:
    allocation_facts = _mapping(allocations.get("facts"), "allocations.facts", [])
    allocation_ids = set(allocation_facts.get("allocation_ids", []))
    required_allocation_mismatches = set(
        allocation_facts.get("required_allocation_mismatches", [])
    )
    precondition_ids = set(launch.get("facts", {}).get("precondition_ids", []))
    role_ids = {item.get("id") for item in roles.get("items", []) if isinstance(item, Mapping)}
    fields = {
        "total_supply_1b": total_supply == TOTAL_SUPPLY,
        "allocation_total_1b": allocation_facts.get("allocation_total") == TOTAL_SUPPLY,
        "launch_circulation_cap": allocation_facts.get("launch_circulation_bps_within_cap") is True,
        "gamification_policy": gamification_policy.get("ok") is True,
        "value_capture_budget": value_capture.get("ok") is True,
        "bonded_value_roles": REQUIRED_VALUE_ROLES <= role_ids,
        "internal_promotion_boundary": promotion_boundary.get("ok") is True,
    }
    for allocation_id in sorted(REQUIRED_ALLOCATIONS):
        fields[f"allocation_{allocation_id}"] = (
            allocation_id in allocation_ids and allocation_id not in required_allocation_mismatches
        )
    for gate_id in sorted(REQUIRED_LAUNCH_GATES):
        fields[f"launch_gate_{gate_id}"] = gate_id in precondition_ids
    return fields


def _validate_required_string_set(value: Any, *, field: str, required: set[str]) -> dict[str, Any]:
    errors: list[str] = []
    raw = value
    if not isinstance(raw, list):
        errors.append(f"{field} must be a list")
        raw = []
    items: set[str] = set()
    for index, item in enumerate(raw):
        if not isinstance(item, str) or item == "":
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
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or value == "":
        errors.append(f"{name} must be a non-empty string")
        return None
    return value


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if not isinstance(value, bool):
        errors.append(f"{name} must be a bool")
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


def _optional_int(value: Any) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    return None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args(argv)

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    report = validate_candidate_model_v0(manifest)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
