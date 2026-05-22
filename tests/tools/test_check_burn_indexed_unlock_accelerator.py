from __future__ import annotations

import copy
import json

from tools.check_burn_indexed_unlock_accelerator import (
    MANIFEST_SCHEMA,
    main,
    validate_burn_indexed_unlock_accelerator_v0,
)


def _manifest() -> dict[str, object]:
    return {
        "schema": MANIFEST_SCHEMA,
        "status": "internal_research_only",
        "activation_allowed": False,
        "public_claims_allowed": False,
        "counsel_review_required": True,
        "counsel_review_status": "required_not_complete",
        "governance_review_status": "required_not_complete",
        "formula": {
            "epoch_unit": "month",
            "cliff_months": 12,
            "scheduled_duration_months": 50,
            "minimum_effective_duration_months": 48,
            "measurement_window_days": 90,
            "lag_days": 30,
            "burn_share_bps": 2_500,
            "per_epoch_extra_release_cap_token": 500_000,
            "max_total_extra_release_token": 12_000_000,
            "total_subject_token": 300_000_000,
            "allocation_share_basis": "base_epoch_release_share",
        },
        "insider_allocations": [
            {
                "id": "founder_original_rd",
                "category": "founder",
                "amount": 150_000_000,
                "cliff_months": 12,
                "scheduled_duration_months": 50,
                "base_epoch_release_token": 3_000_000,
                "max_total_extra_release_token": 6_000_000,
            },
            {
                "id": "core_team_future_contributors",
                "category": "team",
                "amount": 100_000_000,
                "cliff_months": 12,
                "scheduled_duration_months": 50,
                "base_epoch_release_token": 2_000_000,
                "max_total_extra_release_token": 4_000_000,
            },
            {
                "id": "strategic_partners_investors_chain_partners",
                "category": "investor",
                "amount": 50_000_000,
                "cliff_months": 12,
                "scheduled_duration_months": 50,
                "base_epoch_release_token": 1_000_000,
                "max_total_extra_release_token": 2_000_000,
            },
        ],
        "eligible_burn": {
            "sources": ["protocol_fee_buy_and_burn"],
            "required_exclusions": [
                "wash_volume",
                "related_party_round_trip",
                "insider_funded_round_trip",
                "treasury_funded_self_unlock",
                "subsidized_market_maker_churn",
                "manual_burn",
                "route_pool_venue_specific_steering",
            ],
            "requires_receipt_root": True,
            "manual_burn_counts": False,
            "treasury_funded_burn_counts": False,
            "related_party_burn_counts": False,
            "route_pool_venue_specific_burn_counts": False,
        },
        "controls": [
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
        ],
        "attack_scenarios": [
            {
                "id": "wash_burn_roundtrip",
                "condition": "wash volume produces burns that try to accelerate insider unlocks",
                "expected_result": "rejected",
                "excluded_by_controls": True,
                "exclusion_control": "wash_volume",
            },
            {
                "id": "treasury_funded_self_unlock",
                "condition": "treasury buys and burns ZENO mainly to unlock insider allocations",
                "expected_result": "rejected",
                "excluded_by_controls": True,
                "exclusion_control": "treasury_funded_self_unlock",
            },
            {
                "id": "related_party_roundtrip",
                "condition": "an insider or related party round-trips volume to create eligible burns",
                "expected_result": "rejected",
                "excluded_by_controls": True,
                "exclusion_control": "related_party_round_trip",
            },
            {
                "id": "non_excluded_manipulation_bound",
                "condition": "an attacker finds a non-excluded way to generate eligible burns and owns all accelerated insider benefit",
                "expected_result": "bounded",
                "excluded_by_controls": False,
                "exclusion_control": "per_epoch_extra_release_cap",
                "manipulated_burn_token_bound": 1_000_000,
                "attacker_allocation_share_bps": 10_000,
                "exit_value_per_extra_unlocked_token_quote": {"numerator": 1, "denominator": 1},
                "min_cost_per_eligible_burn_token_quote": {"numerator": 1, "denominator": 1},
                "detection_probability_bps": 0,
                "slash_amount_quote": 0,
                "future_value_lost_quote": 0,
            },
        ],
        "promotion_boundary": {
            "public_claim_allowed": False,
            "claim_registry_entry_allowed": False,
            "non_claims": [
                "no_automatic_sale_right",
                "no_legal_clearance",
                "no_tax_clearance",
                "no_market_price_support",
                "no_lockup_override",
                "no_insider_trading_clearance",
            ],
        },
    }


def test_burn_indexed_unlock_accelerator_accepts_conservative_model() -> None:
    report = validate_burn_indexed_unlock_accelerator_v0(_manifest())

    assert report["ok"] is True
    assert report["facts"]["burn_share_bps"] == 2_500
    assert report["facts"]["minimum_effective_duration_months"] == 48
    assert report["facts"]["total_subject_token"] == 300_000_000
    bounded = report["attack_scenarios"]["items"][3]
    assert bounded["facts"]["extra_unlocked_token"] == 250_000
    assert bounded["facts"]["profit_quote"] == "-750000/1"


def test_burn_indexed_unlock_accelerator_rejects_burn_share_above_25_percent() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["formula"]["burn_share_bps"] = 2_501  # type: ignore[index]

    report = validate_burn_indexed_unlock_accelerator_v0(manifest)

    assert report["ok"] is False
    assert "formula.burn_share_bps must be <= 2500" in report["formula"]["errors"]


def test_burn_indexed_unlock_accelerator_rejects_effective_duration_below_floor() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["formula"]["max_total_extra_release_token"] = 12_000_001  # type: ignore[index]
    manifest["insider_allocations"][0]["max_total_extra_release_token"] = 6_000_001  # type: ignore[index]

    report = validate_burn_indexed_unlock_accelerator_v0(manifest)

    assert report["ok"] is False
    assert (
        "max_total_extra_release_token would reduce effective duration below minimum"
        in report["insider_allocations"]["items"][0]["errors"]
    )


def test_burn_indexed_unlock_accelerator_rejects_missing_wash_exclusion() -> None:
    manifest = copy.deepcopy(_manifest())
    exclusions = manifest["eligible_burn"]["required_exclusions"]  # type: ignore[index]
    assert isinstance(exclusions, list)
    exclusions.remove("wash_volume")

    report = validate_burn_indexed_unlock_accelerator_v0(manifest)

    assert report["ok"] is False
    assert "eligible burn missing required exclusions" in report["eligible_burn"]["errors"]


def test_burn_indexed_unlock_accelerator_rejects_profitable_manipulated_burn() -> None:
    manifest = copy.deepcopy(_manifest())
    scenario = manifest["attack_scenarios"][3]  # type: ignore[index]
    scenario["min_cost_per_eligible_burn_token_quote"] = {"numerator": 1, "denominator": 10}

    report = validate_burn_indexed_unlock_accelerator_v0(manifest)

    assert report["ok"] is False
    assert (
        "manipulated burn unlock attack is profitable in bounded model"
        in report["attack_scenarios"]["items"][3]["errors"]
    )


def test_burn_indexed_unlock_accelerator_rejects_activation_before_reviews() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["status"] = "testnet_only"
    manifest["activation_allowed"] = True

    report = validate_burn_indexed_unlock_accelerator_v0(manifest)

    assert report["ok"] is False
    assert "activation requires complete counsel and governance review" in report["errors"]


def test_burn_indexed_unlock_accelerator_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "burn-indexed-unlock.json"
    manifest_path.write_text(json.dumps(_manifest()), encoding="utf-8")

    code = main([str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"].endswith("burn_indexed_unlock_accelerator_report.v0")
