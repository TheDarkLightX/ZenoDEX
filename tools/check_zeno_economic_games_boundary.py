#!/usr/bin/env python3
"""Validate the internal ZENO economic-games boundary manifest."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Mapping

MANIFEST_SCHEMA = "zenodex.economic_games_boundary.v0"
REPORT_SCHEMA = "zenodex.economic_games_boundary_report.v0"

ALLOWED_STATUSES = {"internal_research_only", "testnet_only"}
ALLOWED_CATEGORIES = {
    "non_economic_status",
    "counsel_gated_economic_benefit",
    "counsel_gated_token_distribution",
    "bonded_work_reward",
    "high_risk_separate_gate",
    "forbidden",
}
ALLOWED_LEGAL_POSTURES = {"allowed_internal", "counsel_gated", "forbidden"}

REQUIRED_GLOBAL_CONTROLS = {
    "covered_user_interface_boundary_gate",
    "non_transferable_xp_boundary",
    "token_distribution_separate_program",
    "counsel_review_required",
    "benefit_value_accounting",
    "anti_wash_sybil_controls",
    "no_specific_transaction_solicitation",
    "no_investment_advice",
    "no_passive_yield_marketing",
}

REQUIRED_GAME_IDS = {
    "xp_level_og_status",
    "league_fee_discount",
    "feature_waiver",
    "activity_mined_token_distribution",
    "proof_mining_rewards",
    "oracle_reporter_rewards",
    "lp_duration_incentives",
    "retroactive_activity_airdrop",
    "lock_weighted_governance",
    "referral_rewards",
    "burn_indexed_unlock_accelerator",
    "route_or_token_specific_boost",
    "revenue_share_or_yield_boost",
}

REQUIRED_PROMOTION_NON_CLAIMS = {
    "no_legal_clearance",
    "no_public_launch_readiness",
    "no_broker_dealer_registration_clearance",
    "no_exchange_registration_clearance",
    "no_investment_return",
    "no_specific_transaction_solicitation",
}


def validate_economic_games_boundary_v0(manifest: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    status = _str(obj.get("status"), "status", errors)
    public_claims_allowed = _bool(obj.get("public_claims_allowed"), "public_claims_allowed", errors)
    counsel_review_required = _bool(obj.get("counsel_review_required"), "counsel_review_required", errors)
    if status is not None and status not in ALLOWED_STATUSES:
        errors.append("status must be internal_research_only or testnet_only")
    if public_claims_allowed is not False:
        errors.append("public_claims_allowed must be false")
    if counsel_review_required is not True:
        errors.append("counsel_review_required must be true")

    global_controls = _validate_required_string_set(
        obj.get("global_controls"),
        field="global_controls",
        required=REQUIRED_GLOBAL_CONTROLS,
    )
    games = _validate_games(obj.get("games"), manifest_status=status)
    promotion_boundary = _validate_promotion_boundary(obj.get("promotion_boundary"))

    for section_name, section in (
        ("global_controls", global_controls),
        ("games", games),
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
            "public_claims_allowed": public_claims_allowed,
            "counsel_review_required": counsel_review_required,
            "game_count": games["facts"].get("game_count"),
            "forbidden_game_count": games["facts"].get("forbidden_game_count"),
            "transferable_reward_game_count": games["facts"].get("transferable_reward_game_count"),
        },
        "global_controls": global_controls,
        "games": games,
        "promotion_boundary": promotion_boundary,
    }


def _validate_games(value: Any, *, manifest_status: str | None) -> dict[str, Any]:
    errors: list[str] = []
    games_raw = value
    if not isinstance(games_raw, list):
        errors.append("games must be a list")
        games_raw = []

    seen_ids: set[str] = set()
    reports: list[dict[str, Any]] = []
    forbidden_count = 0
    transferable_count = 0
    for index, item in enumerate(games_raw):
        game_errors: list[str] = []
        game = _mapping(item, f"games[{index}]", game_errors)
        game_id = _str(game.get("id"), f"games[{index}].id", game_errors)
        category = _str(game.get("category"), f"games[{index}].category", game_errors)
        legal_posture = _str(game.get("legal_posture"), f"games[{index}].legal_posture", game_errors)
        participant_action = _str(game.get("participant_action"), f"games[{index}].participant_action", game_errors)
        value_source = _str(game.get("value_source"), f"games[{index}].value_source", game_errors)
        activation_allowed = _bool(game.get("activation_allowed"), f"games[{index}].activation_allowed", game_errors)
        transferable_reward = _bool(game.get("transferable_reward"), f"games[{index}].transferable_reward", game_errors)
        xp_entitlement = _bool(game.get("xp_entitlement"), f"games[{index}].xp_entitlement", game_errors)
        xp_transferable = _bool(game.get("xp_transferable"), f"games[{index}].xp_transferable", game_errors)
        specific_transaction_inducement = _bool(
            game.get("specific_transaction_inducement"),
            f"games[{index}].specific_transaction_inducement",
            game_errors,
        )
        requires_separate_tokenomics_gate = _bool(
            game.get("requires_separate_tokenomics_gate"),
            f"games[{index}].requires_separate_tokenomics_gate",
            game_errors,
        )
        requires_counsel_review = _bool(
            game.get("requires_counsel_review"),
            f"games[{index}].requires_counsel_review",
            game_errors,
        )
        budgeted = _bool(game.get("budgeted"), f"games[{index}].budgeted", game_errors)
        user_terms_disclosed = _bool(
            game.get("user_terms_disclosed"),
            f"games[{index}].user_terms_disclosed",
            game_errors,
        )
        controls = _validate_required_string_set(
            game.get("controls"),
            field=f"games[{index}].controls",
            required=frozenset({"objective_rules", "abuse_gate", "covered_user_interface_boundary"}),
        )

        if game_id is not None:
            if game_id in seen_ids:
                game_errors.append("game id must be unique")
            seen_ids.add(game_id)
        if category is not None and category not in ALLOWED_CATEGORIES:
            game_errors.append("category is unsupported")
        if legal_posture is not None and legal_posture not in ALLOWED_LEGAL_POSTURES:
            game_errors.append("legal_posture is unsupported")
        if manifest_status == "internal_research_only" and activation_allowed is not False:
            game_errors.append("internal research games must set activation_allowed=false")
        if specific_transaction_inducement is not False:
            game_errors.append("specific_transaction_inducement must be false")
        if xp_entitlement is not False:
            game_errors.append("xp_entitlement must be false")
        if xp_transferable is not False:
            game_errors.append("xp_transferable must be false")
        if user_terms_disclosed is not True:
            game_errors.append("user_terms_disclosed must be true")
        if category == "forbidden":
            forbidden_count += 1
            if legal_posture != "forbidden":
                game_errors.append("forbidden category must use legal_posture=forbidden")
            if activation_allowed is not False:
                game_errors.append("forbidden game must set activation_allowed=false")
        if category in {
            "counsel_gated_economic_benefit",
            "counsel_gated_token_distribution",
            "bonded_work_reward",
            "high_risk_separate_gate",
        }:
            if legal_posture != "counsel_gated":
                game_errors.append("economic or token game must use legal_posture=counsel_gated")
            if requires_counsel_review is not True:
                game_errors.append("economic or token game must require counsel review")
            if requires_separate_tokenomics_gate is not True:
                game_errors.append("economic or token game must require a separate tokenomics gate")
            if budgeted is not True:
                game_errors.append("economic or token game must be budgeted")
        if transferable_reward is True:
            transferable_count += 1
            if requires_counsel_review is not True or requires_separate_tokenomics_gate is not True or budgeted is not True:
                game_errors.append("transferable reward requires counsel review, tokenomics gate, and budget")
        if not controls["ok"]:
            game_errors.append("game missing required controls")

        reports.append(
            {
                "id": game_id,
                "ok": not game_errors,
                "status": "accepted" if not game_errors else "rejected",
                "errors": game_errors,
                "facts": {
                    "category": category,
                    "legal_posture": legal_posture,
                    "participant_action": participant_action,
                    "value_source": value_source,
                    "activation_allowed": activation_allowed,
                    "transferable_reward": transferable_reward,
                    "xp_entitlement": xp_entitlement,
                    "xp_transferable": xp_transferable,
                    "specific_transaction_inducement": specific_transaction_inducement,
                    "requires_separate_tokenomics_gate": requires_separate_tokenomics_gate,
                    "requires_counsel_review": requires_counsel_review,
                    "budgeted": budgeted,
                    "user_terms_disclosed": user_terms_disclosed,
                },
                "controls": controls,
            }
        )

    missing = sorted(REQUIRED_GAME_IDS - seen_ids)
    if missing:
        errors.append("missing required economic games")
    if any(not report["ok"] for report in reports):
        errors.append("one or more economic games rejected")
    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "game_count": len(reports),
            "missing_required_game_ids": missing,
            "forbidden_game_count": forbidden_count,
            "transferable_reward_game_count": transferable_count,
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
    non_claims = _validate_required_string_set(
        obj.get("non_claims"),
        field="promotion_boundary.non_claims",
        required=REQUIRED_PROMOTION_NON_CLAIMS,
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


def _validate_required_string_set(value: Any, *, field: str, required: frozenset[str]) -> dict[str, Any]:
    errors: list[str] = []
    items_raw = value
    if not isinstance(items_raw, list):
        errors.append(f"{field} must be a list")
        items_raw = []
    items: set[str] = set()
    for index, item in enumerate(items_raw):
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
            "item_count": len(items),
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


def _load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = validate_economic_games_boundary_v0(_load_json(args.manifest))
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
