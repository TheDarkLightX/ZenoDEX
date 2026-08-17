from __future__ import annotations

import pytest

from tools import check_proof_market_calibration_v1 as checker
from tools import proof_market_calibration_v1 as model


def _recommended_auction_policy() -> model.AuctionPolicyV1:
    return model.AuctionPolicyV1(
        "LOSS_P40000_W25000_F2000_C2000",
        8_000,
        40_000,
        25_000,
        5_000,
        120,
        model.BondRuleV1.LOSS_BASED,
        0,
    )


def test_exact_money_and_probability_inputs_reject_bool_and_negative() -> None:
    with pytest.raises(ValueError, match="exact integer"):
        model.exact_nonnegative(True, "amount")
    with pytest.raises(ValueError, match="exact integer"):
        model.exact_nonnegative(-1, "amount")
    with pytest.raises(ValueError, match="combined failure probability"):
        prover = checker._provers()[0]
        model.assess_prover_bid(
            checker._workloads()[0],
            model.CostShockV1("TOTAL_FAILURE", 10_000, 10_000, 10_000, 9_600),
            prover,
            _recommended_auction_policy(),
            checker._provers()[1],
        )


def test_checked_integer_helpers_cover_maximum_neighbors_without_add_overflow() -> None:
    assert model.ceil_div(model.MAX_ATOMS, model.MAX_ATOMS) == 1
    assert model.floor_bps(model.MAX_ATOMS, model.BPS) == model.MAX_ATOMS
    assert model.ceil_bps(model.MAX_ATOMS, model.BPS) == model.MAX_ATOMS
    with pytest.raises(ValueError, match="amount_times_rate_bps"):
        model.floor_bps(model.MAX_ATOMS, model.BPS + 1)
    with pytest.raises(ValueError, match="amount_times_rate_bps"):
        model.ceil_bps(model.MAX_ATOMS, model.BPS + 1)


def test_basis_point_helpers_match_unbounded_integer_oracle_at_boundaries() -> None:
    amounts = (
        0,
        1,
        model.BPS - 1,
        model.BPS,
        model.BPS + 1,
        model.MAX_ATOMS // model.BPS,
        model.MAX_ATOMS - 1,
        model.MAX_ATOMS,
    )
    rates = (0, 1, model.BPS - 1, model.BPS, model.BPS + 1, model.MAX_ATOMS)

    for amount in amounts:
        for rate_bps in rates:
            product = amount * rate_bps
            expected_floor = product // model.BPS
            expected_ceil = (product + model.BPS - 1) // model.BPS
            if expected_floor <= model.MAX_ATOMS:
                assert model.floor_bps(amount, rate_bps) == expected_floor
            else:
                with pytest.raises(ValueError, match="amount_times_rate_bps"):
                    model.floor_bps(amount, rate_bps)
            if expected_ceil <= model.MAX_ATOMS:
                assert model.ceil_bps(amount, rate_bps) == expected_ceil
            else:
                with pytest.raises(ValueError, match="amount_times_rate_bps"):
                    model.ceil_bps(amount, rate_bps)


def test_effective_window_kills_headline_window_mutant_after_ramp_delay() -> None:
    provers = checker._provers()
    policy = model.AuctionPolicyV1(
        "SHORT_WINDOW",
        8_000,
        40_000,
        17_500,
        5_000,
        120,
        model.BondRuleV1.LOSS_BASED,
        0,
    )
    bid = model.assess_prover_bid(
        checker._workloads()[1],
        checker._shocks()[2],
        provers[1],
        policy,
        provers[1],
    )
    headline_work_seconds = 799
    assert headline_work_seconds >= bid.required_work_seconds
    assert bid.lock_elapsed_seconds == 144
    assert bid.effective_work_seconds == 655
    assert bid.required_work_seconds == 675
    assert not bid.eligible
    assert bid.rejection_codes == ("INSUFFICIENT_EFFECTIVE_WORK_WINDOW",)


def test_every_admitted_bid_has_enough_remaining_work_time() -> None:
    evaluation = model.evaluate_auction_policy(
        checker._workloads(),
        checker._shocks(),
        checker._provers(),
        _recommended_auction_policy(),
        checker._provers()[1],
    )
    assert evaluation.admitted_late_count == 0
    for outcome in evaluation.outcomes:
        for bid in outcome.bids:
            if bid.eligible:
                assert bid.effective_work_seconds >= bid.required_work_seconds


def test_static_ten_x_bond_reduces_fulfillment_and_owner_eligibility() -> None:
    provers = checker._provers()
    loss = model.evaluate_auction_policy(
        checker._workloads(),
        checker._shocks(),
        provers,
        _recommended_auction_policy(),
        provers[1],
    )
    static = model.evaluate_auction_policy(
        checker._workloads(),
        checker._shocks(),
        provers,
        model.AuctionPolicyV1(
            "STATIC_10X",
            8_000,
            40_000,
            25_000,
            5_000,
            120,
            model.BondRuleV1.STATIC_MULTIPLE,
            100_000,
        ),
        provers[1],
    )
    assert loss.fulfillment_bps == 10_000
    assert static.fulfillment_bps == 7_500
    assert static.bond_exclusion_bps > loss.bond_exclusion_bps
    assert (
        static.average_eligible_owner_fraction_bps
        < loss.average_eligible_owner_fraction_bps
    )


def test_wallet_split_is_aggregated_before_priority_owner_cap() -> None:
    aggregated = model.aggregate_requestor_demands_by_owner(
        (
            model.RequestorDemandV1("WALLET_A", "ALICE", 35),
            model.RequestorDemandV1("WALLET_B", "ALICE", 35),
            model.RequestorDemandV1("WALLET_C", "BOB", 20),
        )
    )
    assert aggregated == (("ALICE", 70), ("BOB", 20))


def test_capacity_floor_is_nonzero_and_unused_priority_spills_over() -> None:
    scenario = model.CapacityDemandScenarioV1(
        "SPILLOVER",
        10_000,
        (model.RequestorDemandV1("A", "OWNER_A", 10),),
        80,
    )
    outcome = model.simulate_capacity_scenario(
        scenario,
        model.CapacityPolicyV1(100, 2_000, 2_000),
    )
    assert outcome.permissionless_floor_slots == 20
    assert outcome.priority_served_slots == 10
    assert outcome.permissionless_served_slots == 80
    assert outcome.total_served_slots == 90
    with pytest.raises(ValueError, match="permissionless floor must be nonzero"):
        model.simulate_capacity_scenario(
            scenario,
            model.CapacityPolicyV1(100, 0, 2_000),
        )


def test_duplicate_requestor_identity_rejects_before_owner_aggregation() -> None:
    with pytest.raises(ValueError, match="requestor IDs must be unique"):
        model.aggregate_requestor_demands_by_owner(
            (
                model.RequestorDemandV1("SAME", "OWNER_A", 1),
                model.RequestorDemandV1("SAME", "OWNER_B", 1),
            )
        )
