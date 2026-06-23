from __future__ import annotations

import copy
import json

from tools.check_gamification_manifest import (
    MANIFEST_SCHEMA,
    main,
    validate_gamification_manifest_v0,
)


def _manifest() -> dict[str, object]:
    return {
        "schema": MANIFEST_SCHEMA,
        "status": "internal_research_only",
        "reward_unit": "non_transferable_points",
        "cash_value": False,
        "transferable": False,
        "public_claims_allowed": False,
        "counsel_review_required": True,
        "counsel_review_status": "required_not_complete",
        "caps": {
            "max_reward_per_user": 1_200,
            "max_reward_per_epoch": 10_000,
            "max_total_campaign": 100_000,
        },
        "eligible_actions": [
            {
                "id": "valid_proof_submission",
                "description": "Accepted proof submission with unique proof binding.",
                "reward_amount": 100,
                "max_per_user_per_epoch": 5,
                "eligibility": "accepted proof, unique proof hash, eligible identity",
                "quality_gate": "proof_verifier_accepts_and_claim_scope_matches",
                "duplicate_key": "proof_hash",
            },
            {
                "id": "watcher_attestation",
                "description": "Accepted watcher attestation for a configured range.",
                "reward_amount": 50,
                "max_per_user_per_epoch": 5,
                "eligibility": "valid watcher attestation, unique watcher/range tuple",
                "quality_gate": "two_machine_evidence_checker_accepts_attestation",
                "duplicate_key": "watcher_id:from_height:to_height:last_header_hash",
            },
            {
                "id": "sustained_lp_participation",
                "description": "Sustained LP participation over a completed epoch.",
                "reward_amount": 100,
                "max_per_user_per_epoch": 2,
                "eligibility": "self-directed LP position, completed epoch, active liquidity above dust floor",
                "quality_gate": "lp_position_age_gate_and_wash_activity_filter_accept",
                "duplicate_key": "identity:pool_id:epoch:lp_position_hash",
            },
            {
                "id": "sustained_non_wash_trading_activity",
                "description": "Sustained self-directed DEX trading activity.",
                "reward_amount": 50,
                "max_per_user_per_epoch": 4,
                "eligibility": "self-directed executed trades, non-wash receipt set",
                "quality_gate": "trade_receipt_duplicate_rejection_and_wash_activity_filter_accept",
                "duplicate_key": "identity:epoch:trading_activity_receipt_root",
            },
        ],
        "abuse_controls": [
            "per_identity_cap",
            "duplicate_rejection",
            "quality_gate",
            "sybil_review",
            "wash_activity_filter",
            "benefit_value_gate",
            "interface_non_solicitation_gate",
        ],
        "attack_queries": [
            {
                "id": "sybil_split",
                "condition": "one operator splits submissions across identities to exceed the cap",
                "mitigation": "per_identity_cap plus sybil_review",
                "expected_result": "bounded",
            },
            {
                "id": "wash_activity",
                "condition": "self-generated activity tries to farm points",
                "mitigation": "rewardable actions must pass quality gates and duplicate rejection",
                "expected_result": "rejected",
            },
            {
                "id": "duplicate_claim",
                "condition": "same proof or watcher range is submitted twice",
                "mitigation": "duplicate_key is unique per action family",
                "expected_result": "rejected",
            },
            {
                "id": "low_quality_submission",
                "condition": "invalid proof or malformed attestation asks for points",
                "mitigation": "quality_gate rejects before reward accounting",
                "expected_result": "rejected",
            },
            {
                "id": "xp_token_conversion",
                "condition": "a user tries to redeem XP for a transferable token",
                "mitigation": "XP is a separate non-transferable reputation ledger",
                "expected_result": "rejected",
            },
            {
                "id": "economic_benefit_without_gate",
                "condition": "a high league attempts to receive economic benefits without the tokenomics gate",
                "mitigation": "economic benefits require a separate tokenomics manifest and counsel review",
                "expected_result": "rejected",
            },
            {
                "id": "benefit_steering_specific_transaction",
                "condition": "XP benefits steer a user toward a specific trade",
                "mitigation": "benefits must pass the covered user interface non-solicitation gate",
                "expected_result": "rejected",
            },
        ],
        "benefit_boundary": {
            "xp_transferable": False,
            "xp_cash_value": False,
            "xp_redeemable_for_tokens": False,
            "xp_entitles_token_distribution": False,
            "separate_token_distribution_allowed": True,
            "economic_benefits_require_separate_tokenomics_gate": True,
            "economic_benefits_require_counsel_review": True,
            "covered_user_interface_boundary_gate_id": "covered_user_interface_boundary_v0",
            "allowed_non_economic_benefits": [
                "level_display",
                "league_display",
                "og_status",
                "cosmetic_badges",
                "educational_or_beta_access",
            ],
            "forbidden_without_separate_gate": [
                "token_airdrop_or_distribution",
                "fee_discount_or_rebate",
                "yield_or_staking_boost",
                "governance_weight",
                "revenue_share",
                "priority_execution",
            ],
        },
        "benefit_programs": [
            {
                "id": "high_league_fee_discount_v0",
                "benefit_type": "fee_discount_or_rebate",
                "description": "High-league accounts may qualify for capped protocol-fee discounts.",
                "eligibility": "league >= 4, non-transferable XP threshold met, non-wash activity receipts",
                "league_min": 4,
                "max_benefit_value_per_user_per_epoch": 500,
                "max_benefit_value_per_epoch": 5_000,
                "value_unit": "zUSD_fee_equivalent",
                "funding_or_accounting_source": "protocol_fee_discount_budget",
                "separate_tokenomics_gate_id": "tokenomics_reward_safety_envelope_v0",
                "separate_gate_status": "required_not_complete",
                "counsel_review_status": "required_not_complete",
                "activation_allowed": False,
                "abuse_gate": "benefit_value_gate_and_wash_activity_filter_accept",
                "terms_disclosed": True,
                "benefit_liability_accounted": True,
            },
            {
                "id": "advanced_privacy_feature_waiver_v0",
                "benefit_type": "paid_feature_access_waiver",
                "description": "High-league accounts may qualify for capped free access to advanced privacy features.",
                "eligibility": "league >= 5, non-transferable XP threshold met, feature-use rate limit",
                "league_min": 5,
                "max_benefit_value_per_user_per_epoch": 1_000,
                "max_benefit_value_per_epoch": 10_000,
                "value_unit": "zUSD_feature_fee_equivalent",
                "funding_or_accounting_source": "privacy_feature_waiver_budget",
                "separate_tokenomics_gate_id": "feature_waiver_benefit_budget_v0",
                "separate_gate_status": "required_not_complete",
                "counsel_review_status": "required_not_complete",
                "activation_allowed": False,
                "abuse_gate": "benefit_value_gate_and_feature_use_rate_limit_accept",
                "terms_disclosed": True,
                "benefit_liability_accounted": True,
            },
        ],
        "promotion_boundary": {
            "public_claim_allowed": False,
            "claim_registry_entry_allowed": False,
            "non_claims": [
                "no_cash_value",
                "non_transferable",
                "no_public_launch",
                "no_investment_return",
                "xp_not_token_entitlement",
                "token_distribution_separate_program",
                "no_specific_transaction_solicitation",
                "no_investment_advice",
                "counsel_review_required",
            ],
        },
    }


def test_gamification_manifest_accepts_internal_nontransferable_points() -> None:
    report = validate_gamification_manifest_v0(_manifest())

    assert report["ok"] is True
    assert report["facts"]["reward_unit"] == "non_transferable_points"
    assert report["facts"]["cash_value"] is False
    assert report["facts"]["transferable"] is False
    assert report["facts"]["per_epoch_action_spend_cap"] == 1_150
    assert report["benefit_programs"]["facts"]["benefit_program_count"] == 2
    assert report["benefit_programs"]["facts"]["total_epoch_benefit_cap"] == 15_000


def test_gamification_manifest_rejects_cash_value() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["cash_value"] = True

    report = validate_gamification_manifest_v0(manifest)

    assert report["ok"] is False
    assert "cash_value must be false" in report["errors"]


def test_gamification_manifest_rejects_transferable_reward_unit() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["reward_unit"] = "token"
    manifest["transferable"] = True

    report = validate_gamification_manifest_v0(manifest)

    assert report["ok"] is False
    assert "reward_unit must be non-transferable or capped testnet-only" in report["errors"]
    assert "transferable must be false" in report["errors"]


def test_gamification_manifest_rejects_missing_abuse_control() -> None:
    manifest = copy.deepcopy(_manifest())
    abuse_controls = manifest["abuse_controls"]
    assert isinstance(abuse_controls, list)
    abuse_controls.remove("sybil_review")

    report = validate_gamification_manifest_v0(manifest)

    assert report["ok"] is False
    assert "abuse_controls rejected" in report["errors"]
    assert report["abuse_controls"]["facts"]["missing_required"] == ["sybil_review"]


def test_gamification_manifest_rejects_uncapped_action_spend() -> None:
    manifest = copy.deepcopy(_manifest())
    actions = manifest["eligible_actions"]
    assert isinstance(actions, list)
    actions[0]["reward_amount"] = 1_000

    report = validate_gamification_manifest_v0(manifest)

    assert report["ok"] is False
    assert "eligible action per-user epoch spend cap exceeds caps.max_reward_per_user" in report["eligible_actions"]["errors"]


def test_gamification_manifest_rejects_missing_attack_query() -> None:
    manifest = copy.deepcopy(_manifest())
    queries = manifest["attack_queries"]
    assert isinstance(queries, list)
    queries[:] = [query for query in queries if query["id"] != "wash_activity"]

    report = validate_gamification_manifest_v0(manifest)

    assert report["ok"] is False
    assert "attack_queries rejected" in report["errors"]
    assert report["attack_queries"]["facts"]["missing_required_attack_queries"] == ["wash_activity"]


def test_gamification_manifest_rejects_public_promotion() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["public_claims_allowed"] = True
    promotion_boundary = manifest["promotion_boundary"]
    assert isinstance(promotion_boundary, dict)
    promotion_boundary["public_claim_allowed"] = True

    report = validate_gamification_manifest_v0(manifest)

    assert report["ok"] is False
    assert "public_claims_allowed must be false" in report["errors"]
    assert "promotion_boundary.public_claim_allowed must be false" in report["promotion_boundary"]["errors"]


def test_gamification_manifest_rejects_xp_token_entitlement() -> None:
    manifest = copy.deepcopy(_manifest())
    benefit_boundary = manifest["benefit_boundary"]
    assert isinstance(benefit_boundary, dict)
    benefit_boundary["xp_entitles_token_distribution"] = True

    report = validate_gamification_manifest_v0(manifest)

    assert report["ok"] is False
    assert "benefit_boundary rejected" in report["errors"]
    assert "benefit_boundary.xp_entitles_token_distribution must be false" in report["benefit_boundary"]["errors"]


def test_gamification_manifest_rejects_missing_fee_benefit_program_type() -> None:
    manifest = copy.deepcopy(_manifest())
    programs = manifest["benefit_programs"]
    assert isinstance(programs, list)
    programs[:] = [program for program in programs if program["benefit_type"] != "fee_discount_or_rebate"]

    report = validate_gamification_manifest_v0(manifest)

    assert report["ok"] is False
    assert "benefit_programs rejected" in report["errors"]
    assert report["benefit_programs"]["facts"]["missing_required_benefit_program_types"] == [
        "fee_discount_or_rebate"
    ]


def test_gamification_manifest_rejects_activating_incomplete_benefit_program() -> None:
    manifest = copy.deepcopy(_manifest())
    programs = manifest["benefit_programs"]
    assert isinstance(programs, list)
    programs[0]["activation_allowed"] = True

    report = validate_gamification_manifest_v0(manifest)

    assert report["ok"] is False
    assert "one or more benefit programs rejected" in report["benefit_programs"]["errors"]
    assert (
        "activation requires testnet status plus complete tokenomics gate and counsel review"
        in report["benefit_programs"]["items"][0]["errors"]
    )


def test_gamification_manifest_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "gamification.json"
    manifest_path.write_text(json.dumps(_manifest()), encoding="utf-8")

    code = main([str(manifest_path)])
    report = json.loads(capsys.readouterr().out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.gamification_manifest_report.v0"
