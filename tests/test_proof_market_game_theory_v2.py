from __future__ import annotations

from itertools import product

import pytest

from tools import proof_market_game_theory_v2 as model


def _independent_reverse_vickrey(
    bids: tuple[int, ...],
    reserve: int,
) -> tuple[int | None, int]:
    accepted = sorted((bid, index) for index, bid in enumerate(bids) if bid <= reserve)
    if not accepted:
        return None, 0
    _winning_bid, winner = accepted[0]
    losing = [bid for index, bid in enumerate(bids) if index != winner]
    threshold = min(losing) if losing else reserve
    return winner, min(reserve, threshold)


def test_exact_atoms_reject_bool_negative_and_result_overflow() -> None:
    with pytest.raises(ValueError, match="exact integer"):
        model.exact_natural(True, "amount")
    with pytest.raises(ValueError, match="exact integer"):
        model.exact_natural(-1, "amount")
    assert model.ceil_bps(model.MAX_ATOMS, model.BPS) == model.MAX_ATOMS
    with pytest.raises(ValueError, match="ceil_bps result"):
        model.ceil_bps(model.MAX_ATOMS, model.BPS + 1)


def test_critical_price_matches_independent_oracle_on_complete_small_cube() -> None:
    for bids in product(range(7), repeat=3):
        outcome = model.critical_price_procurement(bids, 5)
        expected_winner, expected_payment = _independent_reverse_vickrey(bids, 5)
        assert outcome.winner_index == expected_winner
        assert outcome.payment_atoms == expected_payment


def test_critical_price_is_bounded_unilaterally_truthful_and_ir() -> None:
    result = model.enumerate_critical_price_dominance(
        bidder_count=3,
        reserve_atoms=5,
    )
    assert result.deviation_queries == 7_203
    assert result.truthful_ir_queries == 1_029
    assert result.truthful_weakly_dominant
    assert result.truthful_ex_post_ir


def test_named_auction_counterexamples_remain_profitable() -> None:
    first_price = model.first_price_truthfulness_counterexample()
    coalition = model.critical_price_coalition_counterexample()
    address_count = model.address_count_diversity_counterexample()
    assert first_price["profitable_gain_atoms"] == 1
    assert coalition["profitable_gain_atoms"] == 2
    assert address_count == {
        "address_count": 3,
        "true_owner_count": 1,
        "address_gate_passes": True,
        "distinct_owner_gate_passes": False,
        "one_address_payment_atoms": 5,
        "alias_payment_atoms": 5,
        "one_address_utility_atoms": 4,
        "alias_utility_atoms": 4,
        "false_name_utility_gain_atoms": 0,
    }


def test_posted_price_is_capped_and_no_acceptance_cannot_ratchet_it() -> None:
    price = model.benchmark_indexed_posted_price(
        model.PostedPriceRequestV2(100, 2_000, 130, 125, 140)
    )
    assert price == 120
    for acceptance_count in (0, 1, 2**64):
        assert (
            model.next_posted_price_after_round(
                current_price_atoms=price,
                acceptance_count=acceptance_count,
            )
            == price
        )


def test_capacity_ticket_weight_is_split_invariant_over_full_seed_cycle() -> None:
    split = (
        model.ProviderV2("A1", "OWNER_A", "DOMAIN_A", 100, 3),
        model.ProviderV2("A2", "OWNER_A", "DOMAIN_A", 110, 2),
        model.ProviderV2("B", "OWNER_B", "DOMAIN_B", 119, 5),
    )
    merged = (
        model.ProviderV2("A", "OWNER_A", "DOMAIN_A", 110, 5),
        model.ProviderV2("B", "OWNER_B", "DOMAIN_B", 119, 5),
    )
    expected = (("OWNER_A", 5), ("OWNER_B", 5))
    assert model.owner_capacity_ticket_counts(split, 120) == expected
    assert model.owner_capacity_ticket_counts(merged, 120) == expected
    for providers in (split, merged):
        owner_wins = [
            model.select_capacity_ticket(providers, 120, seed).owner_id
            for seed in range(10)
        ]
        assert owner_wins.count("OWNER_A") == 5
        assert owner_wins.count("OWNER_B") == 5


def test_capacity_ticket_fixed_seed_split_invariance_is_refuted() -> None:
    split = (
        model.ProviderV2("A1", "OWNER_A", "D1", 1, 1),
        model.ProviderV2("Z1", "OWNER_A", "D1", 1, 1),
        model.ProviderV2("B1", "OWNER_B", "D2", 1, 1),
    )
    merged = (
        model.ProviderV2("A", "OWNER_A", "D1", 1, 2),
        model.ProviderV2("B1", "OWNER_B", "D2", 1, 1),
    )
    assert model.select_capacity_ticket(split, 1, 1).owner_id == "OWNER_B"
    assert model.select_capacity_ticket(merged, 1, 1).owner_id == "OWNER_A"


def test_capacity_ticket_inputs_reject_duplicate_ids_and_zero_capacity() -> None:
    duplicate = (
        model.ProviderV2("SAME", "A", "D1", 1, 1),
        model.ProviderV2("SAME", "B", "D2", 1, 1),
    )
    with pytest.raises(ValueError, match="provider IDs must be unique"):
        model.posted_price_acceptors(duplicate, 1)
    with pytest.raises(ValueError, match="must be positive"):
        model.posted_price_acceptors(
            (model.ProviderV2("A", "A", "D1", 1, 0),),
            1,
        )


def test_capacity_ticket_total_is_bounded_and_seed_mapping_is_unbiased() -> None:
    overflow = (
        model.ProviderV2("A", "A", "D1", 1, model.MAX_ATOMS),
        model.ProviderV2("B", "B", "D2", 1, model.MAX_ATOMS),
    )
    with pytest.raises(ValueError, match="total_measured_capacity_units"):
        model.select_capacity_ticket(overflow, 1, 0)
    assert model.rejection_sample_capacity_ticket(model.MAX_ATOMS, 3) is None
    assert model.rejection_sample_capacity_ticket(0, 3) == 0
    with pytest.raises(ValueError, match="less than total measured capacity"):
        model.select_capacity_ticket(
            (model.ProviderV2("A", "A", "D1", 1, 1),),
            1,
            1,
        )


def test_scarcity_is_pay_as_bid_then_direct_then_unfunded_reject() -> None:
    scarcity = model.scarcity_or_direct_award(
        sealed_bids=(115, 130),
        posted_price_atoms=120,
        job_cap_atoms=120,
        direct_execution_cost_atoms=119,
    )
    assert scarcity == model.FallbackAwardV2(
        model.AwardKindV2.SCARCITY_PROVER,
        0,
        115,
    )
    direct = model.scarcity_or_direct_award(
        sealed_bids=(),
        posted_price_atoms=120,
        job_cap_atoms=120,
        direct_execution_cost_atoms=118,
    )
    assert direct == model.FallbackAwardV2(
        model.AwardKindV2.DIRECT_EXECUTION,
        None,
        118,
    )
    unfunded = model.scarcity_or_direct_award(
        sealed_bids=(),
        posted_price_atoms=120,
        job_cap_atoms=120,
        direct_execution_cost_atoms=121,
    )
    assert unfunded.kind is model.AwardKindV2.UNFUNDED_REJECT
    assert unfunded.payment_atoms == 0


def test_fallback_selects_direct_outside_option_and_blocks_price_uplift() -> None:
    direct = model.scarcity_or_direct_award(
        sealed_bids=(119,),
        posted_price_atoms=120,
        job_cap_atoms=120,
        direct_execution_cost_atoms=100,
    )
    assert direct == model.FallbackAwardV2(
        model.AwardKindV2.DIRECT_EXECUTION,
        None,
        100,
    )
    with pytest.raises(ValueError, match="fallback cap exceeds posted price"):
        model.scarcity_or_direct_award(
            sealed_bids=(2,),
            posted_price_atoms=1,
            job_cap_atoms=2,
            direct_execution_cost_atoms=1,
        )
    with pytest.raises(ValueError, match="scarcity bids must be positive"):
        model.scarcity_or_direct_award(
            sealed_bids=(0,),
            posted_price_atoms=1,
            job_cap_atoms=1,
            direct_execution_cost_atoms=1,
        )


def test_single_provider_cannot_profit_by_same_occurrence_stage_withholding() -> None:
    search = model.enumerate_single_provider_stage_withholding(5)
    assert search.deviation_queries > 0
    assert search.no_profitable_deviation


def test_three_prover_stationary_equal_share_cartel_boundary_is_two_thirds() -> None:
    threshold = model.stationary_equal_share_cartel_threshold(3)
    assert threshold.numerator == 2
    assert threshold.denominator == 3
    below = model.stationary_equal_share_cartel(
        model.StationaryEqualShareCartelScenarioV2(3, 1, 2, 3, 0)
    )
    boundary = model.stationary_equal_share_cartel(
        model.StationaryEqualShareCartelScenarioV2(3, 2, 3, 3, 0)
    )
    assert not below.sustainable
    assert boundary.sustainable
    assert boundary.cooperate_present_value == boundary.deviate_present_value


def test_shared_full_slash_formula_covers_restitution_and_deterrence() -> None:
    loss = model.DefaultLossV2(10, 20, 3, 5)
    assert loss.restitution_atoms == 38
    bond = model.required_default_bond(
        model.DefaultBondRequestV2(loss, 20, 10, 5, 5_000)
    )
    assert bond == 50
    disposition = model.dispose_prover_fault_bond(bond, loss)
    assert disposition.total_atoms == bond
    assert disposition.seller_return_atoms == 0
    assert disposition.residual_penalty_insurance_atoms == 12
    assert model.verifier_fault_bond_return(bond) == bond
    with pytest.raises(ValueError, match="does not cover named restitution"):
        model.dispose_prover_fault_bond(37, loss)


def test_half_slash_mutant_fails_named_restitution() -> None:
    loss = model.DefaultLossV2(10, 20, 3, 5)
    required = model.required_default_bond(
        model.DefaultBondRequestV2(loss, 0, 0, 0, model.BPS)
    )
    half_slash_mutant = required // 2
    assert half_slash_mutant < loss.restitution_atoms
    with pytest.raises(ValueError, match="does not cover named restitution"):
        model.dispose_prover_fault_bond(half_slash_mutant, loss)


def test_finite_reserve_bonus_requires_funded_verified_unique_work() -> None:
    amounts = (30_000_000 * 100_000_000, 1_000 * 100_000_000, 500 * 100_000_000)
    assert (
        model.proof_reserve_bonus(
            model.ProofReserveRequestV2(
                *amounts,
                model.ProofReserveEligibilityV2.INDEPENDENTLY_BASE_FUNDED_VERIFIED_UNCLAIMED_UNRELATED,
            )
        )
        == 500 * 100_000_000
    )
    for ineligible in (
        model.ProofReserveEligibilityV2.BASE_PAYMENT_UNFUNDED,
        model.ProofReserveEligibilityV2.WORK_UNVERIFIED,
        model.ProofReserveEligibilityV2.WORK_KEY_ALREADY_CLAIMED,
        model.ProofReserveEligibilityV2.SELF_DEALING_OR_RELATED_PARTY,
        model.ProofReserveEligibilityV2.BENEFICIAL_OWNER_EVIDENCE_MISSING,
    ):
        assert (
            model.proof_reserve_bonus(
                model.ProofReserveRequestV2(*amounts, ineligible)
            )
            == 0
        )


def test_stateful_reserve_claim_consumes_each_economic_work_key_once() -> None:
    initial = model.ProofReserveClaimStateV2(
        reserve_remaining_atoms=100,
        owner_epoch_remaining_atoms=80,
        claimed_work_keys=frozenset(),
    )
    request_a = model.ProofReserveClaimRequestV2(
        economic_work_key="WORK_A",
        job_bonus_cap_atoms=60,
        eligibility=(
            model.ProofReserveEligibilityV2
            .INDEPENDENTLY_BASE_FUNDED_VERIFIED_UNCLAIMED_UNRELATED
        ),
    )
    first = model.claim_proof_reserve_bonus(initial, request_a)
    assert isinstance(first, model.ProofReserveClaimAcceptedV2)
    assert first.bonus_atoms == 60
    assert first.state == model.ProofReserveClaimStateV2(
        reserve_remaining_atoms=40,
        owner_epoch_remaining_atoms=20,
        claimed_work_keys=frozenset({"WORK_A"}),
    )

    duplicate = model.claim_proof_reserve_bonus(first.state, request_a)
    assert duplicate == model.ProofReserveClaimRejectedV2(
        model.ProofReserveClaimRejectV2.WORK_KEY_ALREADY_CLAIMED
    )

    request_b = model.ProofReserveClaimRequestV2(
        economic_work_key="WORK_B",
        job_bonus_cap_atoms=40,
        eligibility=request_a.eligibility,
    )
    second = model.claim_proof_reserve_bonus(first.state, request_b)
    assert isinstance(second, model.ProofReserveClaimAcceptedV2)
    assert second.bonus_atoms == 20
    assert second.state.reserve_remaining_atoms == 20
    assert second.state.owner_epoch_remaining_atoms == 0
    assert second.state.claimed_work_keys == frozenset({"WORK_A", "WORK_B"})


def test_stateful_reserve_claim_rejects_ineligible_work_without_state_change() -> None:
    state = model.ProofReserveClaimStateV2(100, 80, frozenset())
    request = model.ProofReserveClaimRequestV2(
        economic_work_key="WORK_UNFUNDED",
        job_bonus_cap_atoms=60,
        eligibility=model.ProofReserveEligibilityV2.BASE_PAYMENT_UNFUNDED,
    )
    result = model.claim_proof_reserve_bonus(state, request)
    assert result == model.ProofReserveClaimRejectedV2(
        model.ProofReserveClaimRejectV2.INELIGIBLE
    )
    assert state == model.ProofReserveClaimStateV2(100, 80, frozenset())


def test_stateful_reserve_claim_rejects_zero_capacity_without_claiming_key() -> None:
    state = model.ProofReserveClaimStateV2(0, 0, frozenset())
    request = model.ProofReserveClaimRequestV2(
        economic_work_key="WORK_ZERO",
        job_bonus_cap_atoms=10,
        eligibility=(
            model.ProofReserveEligibilityV2
            .INDEPENDENTLY_BASE_FUNDED_VERIFIED_UNCLAIMED_UNRELATED
        ),
    )
    result = model.claim_proof_reserve_bonus(state, request)
    assert result == model.ProofReserveClaimRejectedV2(
        model.ProofReserveClaimRejectV2.NO_BONUS_CAPACITY
    )
    assert state.claimed_work_keys == frozenset()


def test_dutch_delay_respects_competitor_and_remaining_window_boundaries() -> None:
    assert (
        model.maximum_safe_dutch_delay_price(
            model.DutchDelayContextV2(10, 30, 10, 10, 5, 18)
        )
        == 17
    )
    with pytest.raises(ValueError, match="no safe delay exists"):
        model.maximum_safe_dutch_delay_price(
            model.DutchDelayContextV2(10, 30, 10, 4, 5, None)
        )
    with pytest.raises(ValueError, match="no price below the next acceptance"):
        model.maximum_safe_dutch_delay_price(
            model.DutchDelayContextV2(10, 30, 10, 10, 5, 10)
        )


def test_posted_price_rejects_overflow_before_applying_small_caps() -> None:
    with pytest.raises(ValueError, match="benchmark_with_margin_atoms"):
        model.benchmark_indexed_posted_price(
            model.PostedPriceRequestV2(
                model.MAX_ATOMS,
                model.BPS,
                1,
                1,
                1,
            )
        )
