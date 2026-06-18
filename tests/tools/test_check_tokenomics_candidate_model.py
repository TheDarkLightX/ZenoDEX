from __future__ import annotations

import copy
import json

from tools.check_tokenomics_candidate_model import (
    MANIFEST_SCHEMA,
    _required_tokenomics_fields,
    main,
    validate_candidate_model_v0,
)


def _manifest() -> dict[str, object]:
    return {
        "schema": MANIFEST_SCHEMA,
        "total_supply": 1_000_000_000,
        "vesting_policy": {
            "max_initial_unlock_bps": 1_000,
            "max_launch_circulation_bps": 800,
            "min_insider_cliff_months": 12,
            "min_insider_duration_months": 48,
        },
        "allocations": [
            {
                "id": "founder_original_rd",
                "category": "founder",
                "amount": 150_000_000,
                "vesting": {"cliff_months": 12, "duration_months": 50, "initial_unlock_bps": 0},
            },
            {
                "id": "core_team_future_contributors",
                "category": "team",
                "amount": 100_000_000,
                "vesting": {"cliff_months": 12, "duration_months": 50, "initial_unlock_bps": 0},
            },
            {
                "id": "dao_protocol_treasury",
                "category": "treasury",
                "amount": 250_000_000,
                "vesting": {"cliff_months": 0, "duration_months": 45, "initial_unlock_bps": 1_000},
            },
            {
                "id": "ecosystem_lp_solver_operator_proof_incentives",
                "category": "ecosystem",
                "amount": 250_000_000,
                "vesting": {"cliff_months": 0, "duration_months": 45, "initial_unlock_bps": 1_000},
            },
            {
                "id": "community_retroactive_airdrop_testnet_users",
                "category": "community",
                "amount": 100_000_000,
                "vesting": {"cliff_months": 0, "duration_months": 45, "initial_unlock_bps": 1_000},
            },
            {
                "id": "security_audits_bounties_insurance_reserve",
                "category": "security",
                "amount": 50_000_000,
                "vesting": {"cliff_months": 0, "duration_months": 45, "initial_unlock_bps": 1_000},
            },
            {
                "id": "liquidity_bootstrap_market_making",
                "category": "liquidity",
                "amount": 50_000_000,
                "vesting": {"cliff_months": 0, "duration_months": 45, "initial_unlock_bps": 1_000},
            },
            {
                "id": "strategic_partners_investors_chain_partners",
                "category": "investor",
                "amount": 50_000_000,
                "vesting": {"cliff_months": 12, "duration_months": 50, "initial_unlock_bps": 0},
            },
        ],
        "launch": {
            "public_launch_allowed": False,
            "counsel_review_required": True,
            "counsel_review_status": "required_not_complete",
            "preconditions": [
                {
                    "id": "production_boundary_gate",
                    "status": "passed",
                    "evidence": "tools/check_production_boundary.py",
                },
                {
                    "id": "claims_scope_gate",
                    "status": "passed",
                    "evidence": "tools/check_public_claim_scope.py",
                },
                {
                    "id": "proof_coverage_matrix_gate",
                    "status": "passed",
                    "evidence": "tools/check_zeno_ledger_proof_coverage_matrix.py",
                },
                {
                    "id": "covered_user_interface_boundary_gate",
                    "status": "passed",
                    "evidence": "tools/check_covered_user_interface_boundary.py",
                },
                {
                    "id": "reward_safety_envelope_gate",
                    "status": "passed",
                    "evidence": "tools/check_tokenomics_reward_safety_envelope.py",
                },
                {
                    "id": "economic_games_boundary_gate",
                    "status": "passed",
                    "evidence": "tools/check_zeno_economic_games_boundary.py",
                },
                {
                    "id": "treasury_custody_boundary_gate",
                    "status": "passed",
                    "evidence": "tools/check_zeno_treasury_custody_boundary.py",
                },
                {
                    "id": "burn_indexed_unlock_accelerator_gate",
                    "status": "passed",
                    "evidence": "tools/check_burn_indexed_unlock_accelerator.py",
                },
                {
                    "id": "tokenomics_counsel_review",
                    "status": "required_not_complete",
                    "evidence": "internal/tokenomics/us_tokenomics_posture_2026-03-18.md",
                },
            ],
        },
        "gamification_policy": {
            "xp_transferable": False,
            "xp_redeemable_for_tokens": False,
            "xp_cash_value": False,
            "xp_secondary_market_allowed": False,
            "xp_entitlement_to_discount_or_feature_waiver": False,
            "economic_benefits_require_separate_budget": True,
            "economic_benefits_require_counsel_review": True,
            "token_distribution_uses_separate_program": True,
            "controls": [
                "objective_rules",
                "eligible_activity_receipts",
                "non_wash_receipts",
                "sybil_abuse_gate",
                "covered_user_interface_boundary",
                "terms_disclosure",
                "no_specific_transaction_inducement",
                "no_passive_yield_marketing",
            ],
        },
        "value_capture": {
            "funded_epoch_budget_quote": 1_000_000,
            "max_reward_spend_quote": 300_000,
            "max_rebate_spend_quote": 100_000,
            "max_buyback_spend_quote": 250_000,
            "max_cover_spend_quote": 100_000,
            "fee_split_bps": {
                "treasury": 3_000,
                "proof_rewards": 1_000,
                "buyback": 2_000,
                "cover_reserve": 1_000,
                "lp_rebates": 500,
            },
        },
        "roles": [
            {
                "id": "oracle_reporter",
                "value_moving": True,
                "bond_amount_quote": 100_000,
                "slash_amount_quote": 50_000,
                "max_defect_gain_quote": 50_000,
                "future_value_lost_quote": 0,
                "max_reward_per_epoch_quote": 25_000,
                "withdrawal_delay_epochs": 2,
            },
            {
                "id": "proof_miner",
                "value_moving": True,
                "bond_amount_quote": 200_000,
                "slash_amount_quote": 100_000,
                "max_defect_gain_quote": 75_000,
                "future_value_lost_quote": 0,
                "max_reward_per_epoch_quote": 50_000,
                "withdrawal_delay_epochs": 2,
            },
            {
                "id": "operator",
                "value_moving": True,
                "bond_amount_quote": 300_000,
                "slash_amount_quote": 150_000,
                "max_defect_gain_quote": 150_000,
                "future_value_lost_quote": 50_000,
                "max_reward_per_epoch_quote": 75_000,
                "withdrawal_delay_epochs": 4,
            },
        ],
        "promotion_boundary": {
            "public_claim_allowed": False,
            "claim_registry_entry_allowed": False,
            "non_claims": [
                "economic_security_complete",
                "legal_clearance",
                "public_launch_readiness",
                "secondary_market_value",
            ],
        },
    }


def test_candidate_model_accepts_internal_1b_model() -> None:
    report = validate_candidate_model_v0(_manifest())

    assert report["ok"] is True
    assert report["facts"]["total_supply"] == 1_000_000_000
    assert report["facts"]["allocation_total"] == 1_000_000_000
    assert report["facts"]["circulating_at_launch"] == 70_000_000
    assert report["allocations"]["facts"]["allocation_count"] == 8
    assert report["launch"]["facts"]["public_launch_allowed"] is False
    assert report["roles"]["facts"]["role_max_reward_per_epoch_quote"] == 150_000
    assert all(report["required_tokenomics_fields"].values())


def test_candidate_model_rejects_allocation_sum_mismatch() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["allocations"][0]["amount"] = 399_999_999  # type: ignore[index]

    report = validate_candidate_model_v0(manifest)

    assert report["ok"] is False
    assert "allocation amounts must sum to total_supply" in report["allocations"]["errors"]


def test_candidate_model_rejects_public_launch_before_counsel_review() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["launch"]["public_launch_allowed"] = True  # type: ignore[index]

    report = validate_candidate_model_v0(manifest)

    assert report["ok"] is False
    assert "public_launch_allowed must be false for internal candidate model" in report["launch"]["errors"]


def test_candidate_model_rejects_unbonded_value_moving_role() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["roles"][0]["bond_amount_quote"] = 0  # type: ignore[index]

    report = validate_candidate_model_v0(manifest)

    assert report["ok"] is False
    assert "value-moving role must have positive bond" in report["roles"]["items"][0]["errors"]


def test_candidate_model_rejects_role_rewards_above_budget() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["value_capture"]["max_reward_spend_quote"] = 100_000  # type: ignore[index]

    report = validate_candidate_model_v0(manifest)

    assert report["ok"] is False
    assert "role max_reward_per_epoch total exceeds value_capture.max_reward_spend_quote" in report["roles"]["errors"]


def test_candidate_model_rejects_short_insider_vesting() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["allocations"][0]["vesting"]["cliff_months"] = 6  # type: ignore[index]

    report = validate_candidate_model_v0(manifest)

    assert report["ok"] is False
    assert "insider allocation cliff below policy minimum" in report["allocations"]["items"][0]["errors"]


def test_candidate_model_rejects_launch_float_above_policy_cap() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["vesting_policy"]["max_launch_circulation_bps"] = 600  # type: ignore[index]

    report = validate_candidate_model_v0(manifest)

    assert report["ok"] is False
    assert (
        "circulating_at_launch exceeds vesting_policy.max_launch_circulation_bps"
        in report["allocations"]["errors"]
    )


def test_candidate_model_rejects_transferable_xp_policy() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["gamification_policy"]["xp_transferable"] = True  # type: ignore[index]

    report = validate_candidate_model_v0(manifest)

    assert report["ok"] is False
    assert (
        "gamification_policy.xp_transferable must be false"
        in report["gamification_policy"]["errors"]
    )


def test_required_tokenomics_fields_reject_truthy_string_subreport_ok() -> None:
    fields = _required_tokenomics_fields(
        total_supply=1_000_000_000,
        allocations={
            "facts": {
                "allocation_ids": [
                    "founder_original_rd",
                    "core_team_future_contributors",
                    "dao_protocol_treasury",
                    "ecosystem_lp_solver_operator_proof_incentives",
                    "community_retroactive_airdrop_testnet_users",
                    "security_audits_bounties_insurance_reserve",
                    "liquidity_bootstrap_market_making",
                    "strategic_partners_investors_chain_partners",
                ],
                "required_allocation_mismatches": [],
                "allocation_total": 1_000_000_000,
                "launch_circulation_bps_within_cap": True,
            }
        },
        gamification_policy={"ok": "true"},
        launch={"facts": {"precondition_ids": list({"production_boundary_gate"})}},
        value_capture={"ok": 1},
        roles={
            "items": [
                {"id": "oracle_reporter"},
                {"id": "proof_miner"},
                {"id": "operator"},
            ]
        },
        promotion_boundary={"ok": "yes"},
    )

    assert fields["gamification_policy"] is False
    assert fields["value_capture_budget"] is False
    assert fields["internal_promotion_boundary"] is False


def test_candidate_model_rejects_missing_reward_safety_gate() -> None:
    manifest = copy.deepcopy(_manifest())
    preconditions = manifest["launch"]["preconditions"]  # type: ignore[index]
    assert isinstance(preconditions, list)
    preconditions[:] = [
        item for item in preconditions if item["id"] != "reward_safety_envelope_gate"
    ]

    report = validate_candidate_model_v0(manifest)

    assert report["ok"] is False
    assert "missing required launch preconditions" in report["launch"]["errors"]
    assert report["launch"]["facts"]["missing_required_preconditions"] == [
        "reward_safety_envelope_gate"
    ]


def test_candidate_model_rejects_public_claim_promotion() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["promotion_boundary"]["public_claim_allowed"] = True  # type: ignore[index]

    report = validate_candidate_model_v0(manifest)

    assert report["ok"] is False
    assert "public_claim_allowed must be false" in report["promotion_boundary"]["errors"]


def test_candidate_model_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "candidate-model.json"
    manifest_path.write_text(json.dumps(_manifest()), encoding="utf-8")

    code = main([str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"].endswith("candidate_model_report.v0")
