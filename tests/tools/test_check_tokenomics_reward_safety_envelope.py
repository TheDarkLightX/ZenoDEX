from __future__ import annotations

import json

from tools.check_tokenomics_reward_safety_envelope import (
    MANIFEST_SCHEMA,
    main,
    validate_reward_safety_envelope_v0,
)


def _fee_gated_program(**overrides: object) -> dict[str, object]:
    params: dict[str, object] = {
        "reserve_base": 10_000,
        "reserve_quote": 10_000,
        "fee_bps": 10,
        "protocol_fee_share_bps": 10_000,
        "pol_share_bps": 0,
        "min_usage_quote": 10,
        "base_reward_per_identity_quote": 10,
        "max_identities": 10,
        "funded_budget_quote": 100,
        "max_trade_in_quote": 20_000,
    }
    params.update(overrides)
    return {
        "id": "fee-gated-identity",
        "kind": "fee_gated_identity_reward",
        "params": params,
    }


def _pro_rata_program(**overrides: object) -> dict[str, object]:
    params: dict[str, object] = {
        "reserve_base": 10_000,
        "reserve_quote": 10_000,
        "fee_bps": 10,
        "protocol_fee_share_bps": 10_000,
        "pol_share_bps": 0,
        "other_usage_quote": 0,
        "budget_quote": 2,
        "funded_budget_quote": 2,
        "max_trade_in_quote": 20_000,
        "scan_step": 1,
        "max_cycles": 3,
    }
    params.update(overrides)
    return {
        "id": "pro-rata-budget",
        "kind": "pro_rata_budget",
        "params": params,
    }


def _activity_mined_program(**overrides: object) -> dict[str, object]:
    params: dict[str, object] = {
        "source_bucket_id": "ecosystem_lp_solver_operator_proof_incentives",
        "source_bucket_amount_token": 250_000_000,
        "campaign_budget_token": 25_000_000,
        "funded_campaign_budget_token": 25_000_000,
        "max_epoch_distribution_token": 1_000_000,
        "max_user_distribution_token_per_epoch": 500,
        "reward_per_activity_token": 10,
        "max_rewardable_activities_per_user_per_epoch": 25,
        "xp_entitlement": False,
        "non_transferable_xp_required": True,
        "eligible_activity_receipt_required": True,
        "non_wash_receipt_required": True,
        "covered_user_interface_gate_required": True,
        "activation_allowed": False,
        "counsel_review_status": "required_not_complete",
    }
    params.update(overrides)
    return {
        "id": "active-use-distribution-v0",
        "kind": "activity_mined_distribution",
        "params": params,
    }


def _manifest(*programs: dict[str, object]) -> dict[str, object]:
    return {
        "schema": MANIFEST_SCHEMA,
        "programs": list(programs),
    }


def test_reward_safety_envelope_accepts_bounded_safe_programs() -> None:
    report = validate_reward_safety_envelope_v0(
        _manifest(_fee_gated_program(), _pro_rata_program(), _activity_mined_program())
    )

    assert report["ok"] is True
    assert report["accepted_program_count"] == 3
    fee_gated, pro_rata, activity_mined = report["programs"]
    assert fee_gated["facts"]["best_cost_quote_at_p0"] == "10/1"
    assert fee_gated["facts"]["safe_base_reward_max_int"] == 10
    assert pro_rata["facts"]["max_safe_budget_quote"] == 2
    assert pro_rata["facts"]["best_profit_quote_at_budget"] == "0/1"
    assert activity_mined["facts"]["source_bucket_id"] == "ecosystem_lp_solver_operator_proof_incentives"
    assert activity_mined["facts"]["max_user_activity_distribution_token"] == 250
    assert activity_mined["facts"]["xp_entitlement"] is False


def test_reward_safety_envelope_rejects_fee_gated_reward_above_wash_cost() -> None:
    report = validate_reward_safety_envelope_v0(
        _manifest(_fee_gated_program(base_reward_per_identity_quote=11, funded_budget_quote=110))
    )

    assert report["ok"] is False
    assert report["rejected_program_count"] == 1
    assert "base_reward_per_identity_quote exceeds bounded wash-trade cost" in report["programs"][0]["errors"]


def test_reward_safety_envelope_rejects_pro_rata_budget_above_bounded_safe_budget() -> None:
    report = validate_reward_safety_envelope_v0(_manifest(_pro_rata_program(budget_quote=3, funded_budget_quote=3)))

    assert report["ok"] is False
    assert report["programs"][0]["facts"]["max_safe_budget_quote"] == 2
    assert "budget_quote exceeds bounded max_safe_budget_quote" in report["programs"][0]["errors"]


def test_reward_safety_envelope_rejects_unfunded_reward_spend_cap() -> None:
    report = validate_reward_safety_envelope_v0(_manifest(_fee_gated_program(max_identities=11)))

    assert report["ok"] is False
    assert "identity reward spend cap exceeds funded_budget_quote" in report["programs"][0]["errors"]


def test_reward_safety_envelope_rejects_duplicate_program_ids() -> None:
    report = validate_reward_safety_envelope_v0(_manifest(_pro_rata_program(), _pro_rata_program()))

    assert report["ok"] is False
    assert "program id must be unique" in report["programs"][1]["errors"]


def test_reward_safety_envelope_rejects_activity_mined_xp_entitlement() -> None:
    report = validate_reward_safety_envelope_v0(_manifest(_activity_mined_program(xp_entitlement=True)))

    assert report["ok"] is False
    assert "xp_entitlement must be false" in report["programs"][0]["errors"]


def test_reward_safety_envelope_rejects_activity_mined_budget_above_bucket() -> None:
    report = validate_reward_safety_envelope_v0(
        _manifest(_activity_mined_program(campaign_budget_token=250_000_001))
    )

    assert report["ok"] is False
    assert "campaign_budget_token exceeds source_bucket_amount_token" in report["programs"][0]["errors"]


def test_reward_safety_envelope_rejects_activity_mined_activation_before_counsel() -> None:
    report = validate_reward_safety_envelope_v0(_manifest(_activity_mined_program(activation_allowed=True)))

    assert report["ok"] is False
    assert "activation requires complete counsel review" in report["programs"][0]["errors"]


def test_reward_safety_envelope_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "reward-envelope.json"
    manifest_path.write_text(json.dumps(_manifest(_fee_gated_program())), encoding="utf-8")

    code = main([str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["program_count"] == 1
