from __future__ import annotations

import dataclasses

import pytest

from tools.proof_market_business_model_v1 import (
    BPS,
    AccessPolicyV1,
    ContributionBonusRequestV1,
    FundingScopeV1,
    MarketCandidateV1,
    MarketMonthScenarioV1,
    ProofAdmissionChecksV1,
    ProofJobTermsV1,
    ProofProductKindV1,
    SearchContributionV1,
    allocate_counterexample_pool,
    contribution_locked_bonus,
    dispute_bond_interval,
    evaluate_market_candidate,
    linked_assurance_pledge_dominates,
    maintenance_subscription_sustainable,
    minimum_external_gmv_for_break_even,
    minimum_sybil_bond_atoms,
    pareto_frontier,
    probabilistic_dispute_feasible,
    required_buyer_prefund,
    self_dealing_profit_atoms,
    settle_proof_job,
    simulate_market_month,
)


def _accepted_checks(**overrides: bool) -> ProofAdmissionChecksV1:
    values = {
        field.name: True for field in dataclasses.fields(ProofAdmissionChecksV1)
    }
    values.update(overrides)
    return ProofAdmissionChecksV1(**values)


def _external_terms() -> ProofJobTermsV1:
    return ProofJobTermsV1(
        product_kind=ProofProductKindV1.ASSIGNED_VALIDITY_PROOF,
        funding_scope=FundingScopeV1.EXTERNAL_BUYER,
        access_policy=AccessPolicyV1.PUBLIC_CONTENT_ADDRESSED,
        maximum_seller_payment_atoms=10_000,
        protocol_success_fee_bps=300,
        listing_fee_atoms=20,
        verifier_budget_atoms=500,
        publication_budget_atoms=200,
        seller_bond_atoms=5_000,
    )


def _base_scenarios() -> tuple[MarketMonthScenarioV1, ...]:
    return (
        MarketMonthScenarioV1(
            scenario_id="LOW",
            weight_bps=2_500,
            external_success_gmv_atoms=20_000_000,
            successful_external_jobs=80,
            external_listings=120,
            enterprise_accounts=2,
            catalog_service_events=100,
            public_good_gmv_atoms=2_000_000,
            anchor_user_fee_atoms=4_000_000,
            anchor_proof_cost_atoms=4_500_000,
            fixed_operations_cost_atoms=5_000_000,
            variable_cost_per_listing_atoms=500,
            variable_cost_per_success_atoms=1_000,
            variable_cost_per_catalog_event_atoms=100,
            enterprise_service_cost_per_account_atoms=50_000,
        ),
        MarketMonthScenarioV1(
            scenario_id="BASE",
            weight_bps=5_000,
            external_success_gmv_atoms=100_000_000,
            successful_external_jobs=400,
            external_listings=520,
            enterprise_accounts=10,
            catalog_service_events=2_000,
            public_good_gmv_atoms=10_000_000,
            anchor_user_fee_atoms=12_000_000,
            anchor_proof_cost_atoms=10_000_000,
            fixed_operations_cost_atoms=8_000_000,
            variable_cost_per_listing_atoms=500,
            variable_cost_per_success_atoms=1_000,
            variable_cost_per_catalog_event_atoms=100,
            enterprise_service_cost_per_account_atoms=50_000,
        ),
        MarketMonthScenarioV1(
            scenario_id="HIGH",
            weight_bps=2_500,
            external_success_gmv_atoms=500_000_000,
            successful_external_jobs=1_800,
            external_listings=2_200,
            enterprise_accounts=40,
            catalog_service_events=20_000,
            public_good_gmv_atoms=50_000_000,
            anchor_user_fee_atoms=50_000_000,
            anchor_proof_cost_atoms=35_000_000,
            fixed_operations_cost_atoms=15_000_000,
            variable_cost_per_listing_atoms=500,
            variable_cost_per_success_atoms=1_000,
            variable_cost_per_catalog_event_atoms=100,
            enterprise_service_cost_per_account_atoms=50_000,
        ),
    )


def _candidate(
    candidate_id: str,
    **overrides: int | bool,
) -> MarketCandidateV1:
    values: dict[str, int | bool | str] = {
        "candidate_id": candidate_id,
        "external_success_fee_bps": 300,
        "listing_fee_atoms": 1_000,
        "enterprise_subscription_atoms": 500_000,
        "catalog_service_fee_atoms": 1_000,
        "supports_enterprise_sla": True,
        "supports_catalog_reuse": True,
        "supports_linked_assurance": True,
        "raw_volume_bonus_bps": 0,
        "contribution_bonus_bps": 50,
        "complexity_units": 6,
    }
    values.update(overrides)
    return MarketCandidateV1(**values)


def test_job_prefund_and_accepted_settlement_conserve_every_atom() -> None:
    terms = _external_terms()
    result = settle_proof_job(
        terms,
        _accepted_checks(),
        requested_seller_payment_atoms=8_000,
        verifier_cost_atoms=300,
        publication_cost_atoms=100,
    )
    assert required_buyer_prefund(terms) == 11_020
    assert result.accepted
    assert result.protocol_revenue_atoms == 260
    assert result.seller_bond_return_atoms == 5_000
    assert result.seller_bond_restitution_atoms == 0
    assert (
        result.seller_payment_atoms
        + result.verifier_payment_atoms
        + result.publication_payment_atoms
        + result.protocol_revenue_atoms
        + result.buyer_refund_atoms
        == result.required_buyer_prefund_atoms
    )


@pytest.mark.parametrize(
    "failed_check",
    [field.name for field in dataclasses.fields(ProofAdmissionChecksV1)],
)
def test_every_admission_failure_blocks_seller_payment(failed_check: str) -> None:
    result = settle_proof_job(
        _external_terms(),
        _accepted_checks(**{failed_check: False}),
        requested_seller_payment_atoms=8_000,
        verifier_cost_atoms=300,
        publication_cost_atoms=100,
        seller_default_damage_atoms=2_000,
    )
    assert not result.accepted
    assert result.seller_payment_atoms == 0
    assert result.publication_payment_atoms == 0
    assert result.protocol_revenue_atoms == 20
    assert result.seller_bond_restitution_atoms == 2_000
    assert result.seller_bond_return_atoms == 3_000


def test_internal_zrpf_lane_cannot_manufacture_market_take_revenue() -> None:
    terms = dataclasses.replace(
        _external_terms(),
        product_kind=ProofProductKindV1.ZRPF_BATCH,
        funding_scope=FundingScopeV1.ZRPF_ANCHOR,
    )
    with pytest.raises(ValueError, match="cannot charge itself"):
        required_buyer_prefund(terms)


def test_contribution_bonus_is_bounded_by_external_value_and_schedule() -> None:
    result = contribution_locked_bonus(
        ContributionBonusRequestV1(
            verified_useful_value_atoms=10_000,
            irreversible_external_fee_atoms=600,
            verified_protocol_savings_atoms=1_000,
            scheduled_reserve_cap_atoms=500,
            useful_value_bonus_bps=1_000,
            external_fee_capture_cap_bps=5_000,
            savings_capture_cap_bps=2_000,
        )
    )
    assert result.value_cap_atoms == 1_000
    assert result.anti_self_dealing_cap_atoms == 500
    assert result.bonus_atoms == 500


def test_bonus_below_irreversible_cost_makes_self_dealing_unprofitable() -> None:
    assert (
        self_dealing_profit_atoms(
            bonus_atoms=300,
            fee_credit_atoms=0,
            irreversible_fee_atoms=600,
            verification_cost_atoms=100,
            computation_cost_atoms=200,
            expected_penalty_atoms=0,
        )
        == -600
    )


def test_equal_split_sybil_bond_matches_internal_lean_boundary() -> None:
    assert minimum_sybil_bond_atoms(100, 4) == 15
    assert minimum_sybil_bond_atoms(100, 1) == 0


def test_dispute_bond_interval_finds_feasible_and_infeasible_games() -> None:
    feasible = dispute_bond_interval(
        honest_reward_atoms=15,
        honest_external_gain_atoms=0,
        frivolous_external_gain_atoms=0,
    )
    assert feasible.feasible
    assert feasible.minimum_bond_atoms == 1
    assert feasible.maximum_bond_atoms == 14
    infeasible = dispute_bond_interval(
        honest_reward_atoms=10,
        honest_external_gain_atoms=0,
        frivolous_external_gain_atoms=10,
    )
    assert not infeasible.feasible


def test_probabilistic_dispute_requires_verifier_discrimination() -> None:
    assert probabilistic_dispute_feasible(
        bond_atoms=10,
        honest_reward_atoms=20,
        honest_external_gain_atoms=0,
        frivolous_external_gain_atoms=0,
        honest_accept_probability_bps=8_000,
        frivolous_accept_probability_bps=1_000,
    )
    assert not probabilistic_dispute_feasible(
        bond_atoms=10,
        honest_reward_atoms=20,
        honest_external_gain_atoms=0,
        frivolous_external_gain_atoms=0,
        honest_accept_probability_bps=5_000,
        frivolous_accept_probability_bps=5_000,
    )


def test_linked_assurance_reproduces_pledge_and_free_rider_witnesses() -> None:
    assert linked_assurance_pledge_dominates(
        buyer_value_atoms=100,
        pledge_atoms=30,
        delay_numerator=1,
        delay_denominator=2,
    )
    assert not linked_assurance_pledge_dominates(
        buyer_value_atoms=100,
        pledge_atoms=60,
        delay_numerator=1,
        delay_denominator=2,
    )


def test_maintenance_subscription_uses_exact_condition() -> None:
    assert maintenance_subscription_sustainable(
        maintenance_cost_atoms=1,
        period_payment_atoms=5,
        slash_atoms=3,
        discount_numerator=1,
        discount_denominator=2,
        continuation_surplus_numerator=1,
        continuation_surplus_denominator=1,
    )
    assert not maintenance_subscription_sustainable(
        maintenance_cost_atoms=10,
        period_payment_atoms=1,
        slash_atoms=1,
        discount_numerator=1,
        discount_denominator=2,
        continuation_surplus_numerator=1,
        continuation_surplus_denominator=1,
    )


def test_counterexample_pool_pays_unique_coverage_and_one_terminal_result() -> None:
    contributions = (
        SearchContributionV1("coverage-a", "partition-a", 1, 30, True, False),
        SearchContributionV1("coverage-b", "partition-b", 1, 70, True, False),
        SearchContributionV1("counterexample", "partition-c", 2, 0, True, True),
    )
    result = allocate_counterexample_pool(
        total_budget_atoms=1_000,
        milestone_budget_bps=2_000,
        contributions=contributions,
    )
    assert result.terminal_winner_id == "counterexample"
    assert dict(result.milestone_payments_atoms) == {
        "coverage-a": 60,
        "coverage-b": 140,
    }
    assert result.terminal_payment_atoms == 800
    assert result.carry_atoms == 0


def test_counterexample_pool_rejects_partition_splitting() -> None:
    contributions = (
        SearchContributionV1("alice-1", "same-partition", 1, 50, True, False),
        SearchContributionV1("alice-2", "same-partition", 2, 50, True, False),
    )
    with pytest.raises(ValueError, match="partition may appear at most once"):
        allocate_counterexample_pool(
            total_budget_atoms=1_000,
            milestone_budget_bps=2_000,
            contributions=contributions,
        )


def test_market_cash_flow_excludes_seller_gmv_from_protocol_revenue() -> None:
    scenario = _base_scenarios()[1]
    candidate = _candidate("HYBRID")
    result = simulate_market_month(candidate, scenario)
    assert result.external_protocol_revenue_atoms < scenario.external_success_gmv_atoms
    assert result.external_success_fee_revenue_atoms == 3_300_000
    assert result.anchor_net_contribution_atoms == 2_000_000
    assert result.raw_volume_self_dealing_safe


def test_raw_volume_reward_above_fee_is_fail_closed_as_manipulable() -> None:
    scenario = _base_scenarios()[1]
    candidate = _candidate(
        "RAW_VOLUME",
        raw_volume_bonus_bps=500,
        contribution_bonus_bps=0,
    )
    result = simulate_market_month(candidate, scenario)
    assert not result.raw_volume_self_dealing_safe
    evaluation = evaluate_market_candidate(candidate, _base_scenarios())
    assert not evaluation.manipulation_safe


def test_external_contribution_bonus_cannot_consume_zrpf_anchor_savings() -> None:
    scenario = dataclasses.replace(
        _base_scenarios()[1],
        anchor_user_fee_atoms=100_000_000,
        anchor_proof_cost_atoms=0,
    )
    candidate = _candidate("AGGRESSIVE_CONTRIBUTION", contribution_bonus_bps=BPS)
    result = simulate_market_month(candidate, scenario)
    assert result.proof_reserve_bonus_atoms == (
        result.external_success_fee_revenue_atoms // 2
    )
    assert result.proof_reserve_bonus_atoms < result.anchor_net_contribution_atoms


def test_candidate_evaluation_and_frontier_exclude_manipulable_candidate() -> None:
    scenarios = _base_scenarios()
    hybrid = evaluate_market_candidate(_candidate("HYBRID"), scenarios)
    simple = evaluate_market_candidate(
        _candidate(
            "SUCCESS_ONLY",
            listing_fee_atoms=0,
            enterprise_subscription_atoms=0,
            catalog_service_fee_atoms=0,
            supports_enterprise_sla=False,
            supports_catalog_reuse=False,
            supports_linked_assurance=False,
            contribution_bonus_bps=0,
            complexity_units=2,
            external_success_fee_bps=500,
        ),
        scenarios,
    )
    unsafe = evaluate_market_candidate(
        _candidate(
            "RAW_VOLUME",
            raw_volume_bonus_bps=500,
            contribution_bonus_bps=0,
        ),
        scenarios,
    )
    frontier = pareto_frontier((hybrid, simple, unsafe))
    assert {row.candidate_id for row in frontier} <= {"HYBRID", "SUCCESS_ONLY"}
    assert "RAW_VOLUME" not in {row.candidate_id for row in frontier}


def test_break_even_gmv_uses_exact_ceiling() -> None:
    assert minimum_external_gmv_for_break_even(
        monthly_fixed_gap_atoms=3_000_000,
        success_fee_bps=300,
    ) == 100_000_000


def test_scenario_weights_must_close_exactly() -> None:
    scenarios = list(_base_scenarios())
    scenarios[0] = dataclasses.replace(scenarios[0], weight_bps=2_499)
    with pytest.raises(ValueError, match="sum to 10000"):
        evaluate_market_candidate(_candidate("BAD_WEIGHTS"), tuple(scenarios))


def test_bool_is_rejected_as_an_amount() -> None:
    with pytest.raises(ValueError, match="exact integer"):
        minimum_sybil_bond_atoms(True, 4)


def test_bps_constant_is_exact() -> None:
    assert BPS == 10_000
