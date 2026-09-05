"""Research obligations and explicit premise-breaking controls; no publication."""

import pytest

from tools.tokenomics.lp_service_budget_v1 import (
    AssetBudget,
    ServiceLot,
    falsifying_controls,
    fee_partition,
    reserve_service,
    select_unit_lots,
    service_entitlement,
    terminal_claims,
    usage_weighted_reward,
)


def test_committing_service_preserves_all_protected_ownership_buckets():
    before = AssetBudget("USD", 100, 7, 3, 20, 9, 11)
    after = reserve_service(before, 11)
    assert after.physical_atoms == before.physical_atoms
    assert after.principal == 100 and after.earned_claims == 7
    assert after.risk_reserve == 20 and after.burn_reserve == 9
    assert after.contract_escrow == 14 and after.free == 0
    with pytest.raises(ValueError, match="unencumbered"):
        reserve_service(before, 12)
    assert before.free == 11 and before.contract_escrow == 3


def test_principal_cannot_make_an_unfunded_quiet_epoch_affordable():
    before = AssetBudget("USD", 100, 0, 0, 0, 0, 0)
    with pytest.raises(ValueError, match="unencumbered"):
        reserve_service(before, 1)
    # Omission mutant: paying from physical assets instead loses principal cover.
    assert before.physical_atoms - 1 < before.principal


def test_fee_atom_cannot_be_promised_to_burn_and_service_twice():
    assert fee_partition(11, (2, 3), 10) == (2, 3, 6)
    with pytest.raises(ValueError, match="exceeds"):
        fee_partition(10, (6, 6), 10)


def test_cancellation_keeps_earned_claim_and_refunds_only_unearned_escrow():
    assert terminal_claims(10, 7, 3) == (4, 3)
    assert terminal_claims(10, 0, 0) == (0, 10)
    assert terminal_claims(10, 10, 10) == (0, 0)
    # Original cap 10, remaining physical escrow 7. Never pass current 7 as cap.
    provider, refund = terminal_claims(funded_cap=10, earned_total=4, paid_total=3)
    assert (provider, refund) == (1, 6) and provider + refund == 7
    with pytest.raises(ValueError, match="order"):
        terminal_claims(10, 7, 8)
    assert 10 - 3 != 4  # Omitting the original funder's refund loses ownership.


def test_frozen_entitlement_self_wash_bound_has_live_and_boundary_controls():
    before = service_entitlement(20, 3, 10, 100)
    after = service_entitlement(30, 3, 10, 100)
    assert before == 6 and after == 9 and after - before - 10 == -7
    assert service_entitlement(21, 10, 10, 100) - service_entitlement(20, 10, 10, 100) == 1
    assert service_entitlement(30, 3, 10, 7) == 7


def test_subsidy_and_weight_changes_falsify_a_broader_no_wash_claim():
    controls = falsifying_controls()
    assert controls["subsidy_unlocked_by_usage"]["incremental_profit"] == 1
    assert controls["claim_weight_changes"]["incremental_profit"] == 9
    assert usage_weighted_reward(10, 1, 9) == 1  # Honest competing usage changes reward.
    assert usage_weighted_reward(10, 0, 0) == 0


def test_individual_rounding_can_release_owned_carry_beyond_added_fee():
    before, after = fee_partition(1, (1, 1), 2), fee_partition(2, (1, 1), 2)
    payout_delta = sum(after[:-1]) - sum(before[:-1])
    assert payout_delta == 2 and before[-1] - after[-1] == 1
    assert payout_delta == 1 + before[-1] - after[-1]
    assert payout_delta > 1  # Mutant omitting old owned carry understates available resources.


def test_procurement_requires_disjoint_positions_and_affordable_exact_lots():
    lots = (ServiceLot("b", "position-b", 3), ServiceLot("a", "position-a", 2))
    assert select_unit_lots(lots, 1, 2) == ("a",)
    with pytest.raises(ValueError, match="unencumbered"):
        select_unit_lots(lots, 2, 4)
    with pytest.raises(ValueError, match="already committed"):
        select_unit_lots((lots[0], ServiceLot("c", "position-b", 1)), 1, 3)
    controls = falsifying_controls()
    assert controls["heterogeneous_ratio_greedy"]["greedy_cost"] == 17
    assert controls["heterogeneous_ratio_greedy"]["optimal_cost"] == 11
    assert controls["pay_as_bid_markup"]["utility_increase"] == 8


@pytest.mark.parametrize("amount", [True, -1, 0.5])
def test_only_nonnegative_integer_atoms_enter_the_research_model(amount):
    with pytest.raises(ValueError, match="integer atoms"):
        AssetBudget("asset", 0, 0, 0, 0, 0, amount)
