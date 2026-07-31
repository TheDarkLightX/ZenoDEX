from __future__ import annotations

import pytest

from src.core import fcis_m6_profile_ids
from src.core.fcis_fee_apportionment_allocator import apply_fee_apportionment_v2
from src.core.fcis_fee_apportionment_postconditions import (
    FeeAllocationPostconditionAcceptV2,
    FeeAllocationPostconditionCodeV2,
    FeeAllocationPostconditionRejectV2,
    FeeAllocationPostconditionResultV2,
    revalidate_fee_allocation_postconditions_v2,
)
from src.core.fcis_fee_apportionment_values import (
    AssetFeeAllocationV2,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
    FeeApportionmentTransitionOkV2,
    FeeDistributionPolicyV2,
)


def _policy(
    weights: tuple[int, int, int] = (3_333, 3_333, 3_334),
) -> FeeDistributionPolicyV2:
    return FeeDistributionPolicyV2(*weights, "buyback", "treasury", "rewards")


def _accepted(
    *,
    amount: int = 1,
    weights: tuple[int, int, int] = (3_333, 3_333, 3_334),
) -> tuple[FeeDistributionPolicyV2, AssetFeeAllocationV2]:
    key = FeeApportionmentKeyV2("domain-a", "asset-a")
    result = apply_fee_apportionment_v2(
        contributions=(FeeAmountCandidateV2(key, amount),),
        policy=_policy(weights),
        state=CommittedFeeApportionmentStateV2(
            "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
            (),
        ),
    )
    assert type(result) is FeeApportionmentTransitionOkV2
    assert len(result.allocations) == 1
    return _policy(weights), result.allocations[0]


def _revalidate(
    policy: FeeDistributionPolicyV2,
    allocation: AssetFeeAllocationV2,
    *,
    amounts: tuple[int, int, int] | None = None,
    bonuses: tuple[int, int, int] | None = None,
    deficits_post: tuple[int, int, int] | None = None,
) -> FeeAllocationPostconditionResultV2:
    return revalidate_fee_allocation_postconditions_v2(
        amount=allocation.amount,
        policy=policy,
        fractions=allocation.fractions,
        bonuses=allocation.bonuses if bonuses is None else bonuses,
        amounts=allocation.amounts if amounts is None else amounts,
        deficits_pre=allocation.deficits_pre,
        deficits_post=allocation.deficits_post if deficits_post is None else deficits_post,
    )


def test_postconditions_accept_a_fresh_allocator_result() -> None:
    policy, allocation = _accepted()

    checked = _revalidate(policy, allocation)

    assert checked == FeeAllocationPostconditionAcceptV2(
        ("buyback", "treasury", "rewards"),
        1,
    )


@pytest.mark.parametrize(
    ("mutant", "expected_code"),
    (
        (
            "B06_SUM_ALLOCATIONS",
            FeeAllocationPostconditionCodeV2.AMOUNT_CONSERVATION,
        ),
        (
            "B06_LOCAL_QUOTA",
            FeeAllocationPostconditionCodeV2.LOCAL_QUOTA,
        ),
        (
            "B06_POST_DEFICIT_RECURRENCE",
            FeeAllocationPostconditionCodeV2.POST_DEFICIT_RECURRENCE,
        ),
        (
            "B06_BONUS_ORDER",
            FeeAllocationPostconditionCodeV2.BONUS_ORDER,
        ),
    ),
)
def test_named_postcondition_mutants_are_rejected(
    mutant: str,
    expected_code: FeeAllocationPostconditionCodeV2,
) -> None:
    policy, allocation = _accepted()
    if mutant == "B06_SUM_ALLOCATIONS":
        result = _revalidate(policy, allocation, amounts=(1, 0, 1))
    elif mutant == "B06_LOCAL_QUOTA":
        result = _revalidate(policy, allocation, amounts=(1, 0, 0))
    elif mutant == "B06_POST_DEFICIT_RECURRENCE":
        result = _revalidate(policy, allocation, deficits_post=(3_333, 3_332, -6_665))
    else:
        result = _revalidate(
            policy,
            allocation,
            bonuses=(1, 0, 0),
            amounts=(1, 0, 0),
            deficits_post=(-6_667, 3_333, 3_334),
        )

    assert type(result) is FeeAllocationPostconditionRejectV2
    assert result.code is expected_code


def test_zero_weight_role_cannot_receive_a_mutated_amount() -> None:
    policy, allocation = _accepted(amount=1, weights=(10_000, 0, 0))

    result = _revalidate(policy, allocation, amounts=(0, 1, 0))

    assert type(result) is FeeAllocationPostconditionRejectV2
    assert result.code is FeeAllocationPostconditionCodeV2.ZERO_WEIGHT_SUPPORT


def test_fixed_role_profile_drift_rejects_before_acceptance(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    policy, allocation = _accepted()
    monkeypatch.setattr(
        fcis_m6_profile_ids,
        "FIXED_ROLE_ORDER_V1",
        ("rewards", "treasury", "buyback"),
    )

    result = _revalidate(policy, allocation)

    assert result == FeeAllocationPostconditionRejectV2(
        FeeAllocationPostconditionCodeV2.INVALID_ROLE_ORDER,
        ("role_order",),
    )


def test_allocator_grants_no_candidate_when_postcondition_relation_rejects(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from src.core import fcis_fee_apportionment_allocator as allocator
    from src.core.fcis_fee_apportionment_values import (
        CommittedFeeApportionmentStateV2,
        FeeApportionmentTransitionCodeV2,
        FeeApportionmentTransitionRejectV2,
    )

    rejection = FeeAllocationPostconditionRejectV2(
        FeeAllocationPostconditionCodeV2.BONUS_ORDER,
        ("bonuses",),
    )
    monkeypatch.setattr(
        allocator,
        "revalidate_fee_allocation_postconditions_v2",
        lambda **_: rejection,
    )
    key = FeeApportionmentKeyV2("domain-a", "asset-a")

    result = allocator.apply_fee_apportionment_v2(
        contributions=(FeeAmountCandidateV2(key, 1),),
        policy=_policy(),
        state=CommittedFeeApportionmentStateV2(
            "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
            (),
        ),
    )

    assert result == FeeApportionmentTransitionRejectV2(
        FeeApportionmentTransitionCodeV2.INTERNAL_RELATION_FAILURE,
        ("relation", "postconditions", "bonus_order", "bonuses"),
    )
