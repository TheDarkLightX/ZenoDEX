from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools import check_production_readiness_g1_partial_policy_v2 as checker
from tools import production_readiness_g1_partial_policy_contract_v2 as contract


def test_partial_policy_is_exact_and_keeps_launch_blocked() -> None:
    document = checker.build_document()
    report = checker.check_artifact(checker.DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["launch_allowed"] is False
    assert report["whole_token_supply"] == 2_000_000_000
    assert report["participant_count"] == 22
    assert report["open_participant_count"] == 22
    assert report["genesis_distribution_selected"] is False
    assert document["production_promotion"] is False


def test_selected_supply_and_zeno_floor_use_exact_integer_atoms() -> None:
    selected = checker.build_document()["selected_parameters"]

    assert selected["decimals"] == 18
    assert selected["unit_scale"] == 10**18
    assert selected["genesis_supply_atoms"] == 2_000_000_000 * 10**18
    assert selected["supply_ceiling_atoms"] == selected["genesis_supply_atoms"]
    assert selected["absolute_floor_atoms"] == 1
    assert selected["launch_active_floor_atoms"] == 200_000_000 * 10**18
    assert selected["issue_authority"] == "GENESIS_ONLY"
    assert selected["post_genesis_mint"] == "FORBIDDEN"
    assert selected["burn_rule"]["zeno_cap_atoms"] == "floor(excess_atoms / 2)"
    assert selected["implicit_buyburn_or_treasury_sweep"] == "FORBIDDEN"


def test_scaled_allocation_is_modeling_only_and_reconciles() -> None:
    gate = checker.build_document()["genesis_distribution_gate"]
    allocations = gate["scaled_modeling_allocations"]

    assert gate["modeling_baseline_status"] == (
        "APPROVED_SCALED_2X_FOR_ECONOMIC_MODELING"
    )
    assert sum(entry["allocation_bps"] for entry in allocations) == 10_000
    assert sum(entry["whole_tokens"] for entry in allocations) == 2_000_000_000
    assert gate["selected_distribution_release"] is None
    assert gate["genesis_mint_allowed"] is False
    assert gate["transfer_activation_allowed"] is False
    assert gate["counsel_review_complete"] is False
    assert gate["legal_clearance_claim"] is False


def test_every_participant_policy_is_open_and_every_command_is_covered() -> None:
    gate = checker.build_document()["participant_compensation_gate"]
    participants = gate["participants"]
    covered_commands = {
        command for entry in participants for command in entry["affected_commands"]
    }

    assert gate["covered_command_count"] == 33
    assert len(gate["covered_profile_decisions"]) == 9
    assert len(covered_commands) == 33
    for entry in participants:
        assert entry["status"] == "OPEN_UNSELECTED_COMPENSATION_POLICY"
        assert entry["production_authority"] == "NONE"
        assert entry["default_if_unselected"] == "AFFECTED_FEATURE_DISABLED"
        assert set(entry["selected_policy"]) == set(
            contract.COMPENSATION_SELECTION_FIELDS
        )
        assert all(value is None for value in entry["selected_policy"].values())


def test_waterfall_closes_old_fee_gap_and_protects_participant_priority() -> None:
    document = checker.build_document()
    review = document["mechanism_review"]
    tiers = review["payment_priority_tiers"]
    improvements = {
        entry["id"]: entry for entry in review["mechanism_improvements"]
    }

    assert [entry["priority"] for entry in tiers] == list(range(6))
    assert tiers[0]["id"] == "exact_user_property_and_accrued_liabilities"
    assert tiers[4]["id"] == "eligible_surplus_buy_and_burn"
    assert improvements["close_unnamed_fee_remainder"]["closure"] == (
        "REJECT_GLOBAL_SPLIT_AND_REQUIRE_COMPLETE_PER_LANE_PRIORITY_WATERFALL"
    )
    assert improvements["disable_burn_indexed_insider_acceleration"][
        "closure"
    ].startswith("HELD_FOR_LAUNCH")
    assert document["genesis_distribution_gate"][
        "burn_indexed_insider_unlock_accelerator"
    ] == "HELD_UNSELECTED_PENDING_MANIPULATION_AND_COUNSEL_GATES"
    candidate = review["burn_indexed_unlock_candidate"]
    assert candidate["status"] == "HELD_UNSELECTED"
    assert candidate["historical_candidate_unlock_bps_of_eligible_burn"] == 2_500
    assert len(candidate["required_gates"]) == 9
    bounded = review["bounded_model"]
    assert bounded["protocol_observable_liquid_delta"] == (
        "-burn_atoms - (locked_after_atoms - locked_before_atoms)"
    )
    assert bounded["strict_protocol_observable_float_deflation"] == (
        "burn_atoms > locked_before_atoms - locked_after_atoms"
    )


def test_historical_candidate_is_bound_as_unselected_conflict() -> None:
    conflict = checker.build_document()["historical_candidate_conflict"]

    assert conflict["historical_whole_supply"] == 1_000_000_000
    assert conflict["historical_allocation_total"] == 1_000_000_000
    assert conflict["historical_fee_split_declared_bps"] == 7_500
    assert conflict["historical_fee_split_status"] == (
        "INCOMPLETE_2500_BPS_UNNAMED"
    )
    assert conflict["current_selection_effect"] == "NONE"
    assert conflict["scaling_rule"] == (
        "SCALED_2X_AS_APPROVED_MODELING_BASELINE_ONLY"
    )


def test_volume_incentive_stack_rewards_costly_contribution_instead_of_volume() -> None:
    stack = checker.build_document()["mechanism_review"][
        "recommended_volume_incentive_stack"
    ]

    assert [entry["rank"] for entry in stack] == [1, 2, 3]
    assert all(entry["status"] == "PROPOSED_UNSELECTED" for entry in stack)
    assert stack[0]["id"] == "loss_bounded_future_fee_credit"
    assert "NONTRANSFERABLE" in stack[0]["instrument"]
    assert "selected_total_incentive_bps < 10000" in stack[0][
        "manipulation_bound"
    ]
    assert stack[1]["id"] == "executable_depth_reverse_auction"
    assert stack[2]["id"] == "net_surplus_performance_milestone"


def test_supply_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(checker.DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["selected_parameters"]["whole_token_supply"] = 10_000_000_000
    candidate = tmp_path / "wrong-supply.json"
    candidate.write_bytes(checker._encoded(artifact))

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False
    assert "artifact differs" in " ".join(report["errors"])


def test_selecting_unapproved_participant_payment_fails_closed(
    tmp_path: Path,
) -> None:
    artifact = json.loads(checker.DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["participant_compensation_gate"]["participants"][0][
        "selected_policy"
    ]["funding_source"] = "UNAPPROVED_FEE_LANE"
    candidate = tmp_path / "unapproved-payment.json"
    candidate.write_bytes(checker._encoded(artifact))

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert report["launch_allowed"] is False


def test_duplicate_json_key_fails_closed(tmp_path: Path) -> None:
    candidate = tmp_path / "duplicate.json"
    candidate.write_text(
        '{"schema":"first","schema":"second"}\n', encoding="utf-8"
    )

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert any("duplicate JSON keys" in error for error in report["errors"])


def test_missing_participant_obligation_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        contract,
        "PARTICIPANT_OBLIGATIONS",
        contract.PARTICIPANT_OBLIGATIONS[:-1],
    )

    with pytest.raises(ValueError, match="differs from exact inventory"):
        checker.build_document()


def test_malformed_scaled_allocation_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    malformed = [dict(entry) for entry in contract.SCALED_MODELING_ALLOCATIONS]
    malformed[0]["whole_tokens"] += 1
    monkeypatch.setattr(contract, "SCALED_MODELING_ALLOCATIONS", tuple(malformed))

    with pytest.raises(ValueError, match="differ from exact approval"):
        checker.build_document()


def test_same_sum_allocation_redistribution_fails_exact_approval(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    malformed = [dict(entry) for entry in contract.SCALED_MODELING_ALLOCATIONS]
    malformed[0]["allocation_bps"] -= 1
    malformed[0]["whole_tokens"] -= 200_000
    malformed[1]["allocation_bps"] += 1
    malformed[1]["whole_tokens"] += 200_000
    monkeypatch.setattr(contract, "SCALED_MODELING_ALLOCATIONS", tuple(malformed))

    with pytest.raises(ValueError, match="differ from exact approval"):
        checker.build_document()


def test_contract_supply_change_fails_exact_approval(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(contract, "ZDEX_WHOLE_SUPPLY", 10_000_000_000)

    with pytest.raises(ValueError, match="supply decision differs"):
        checker.build_document()


def test_volume_candidate_cannot_gain_activation_by_regeneration(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    stack = [
        dict(entry)
        for entry in contract.MECHANISM_REVIEW["recommended_volume_incentive_stack"]
    ]
    stack[0]["status"] = "ACTIVE"
    monkeypatch.setitem(
        contract.MECHANISM_REVIEW,
        "recommended_volume_incentive_stack",
        tuple(stack),
    )

    with pytest.raises(ValueError, match="gained activation status"):
        checker.build_document()


def test_frozen_research_source_byte_drift_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    real_git_bytes = checker._git_bytes

    def altered_git_bytes(repo_root: Path, *args: str) -> bytes:
        observed = real_git_bytes(repo_root, *args)
        if args and args[0] == "show":
            return observed + b"tampered"
        return observed

    monkeypatch.setattr(checker, "_git_bytes", altered_git_bytes)

    with pytest.raises(ValueError, match="research source drift"):
        checker.build_document()


def test_research_sources_are_exactly_pinned() -> None:
    document = checker.build_document()

    assert {pin["subject"] for pin in document["source_pins"]} == {
        checker.RESEARCH_SOURCE_SUBJECT
    }
    assert {pin["path"] for pin in document["source_pins"]} == set(
        contract.RESEARCH_SOURCE_PATHS
    )
    assert all(len(pin["sha256"]) == 64 for pin in document["source_pins"])
