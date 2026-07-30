from __future__ import annotations

from itertools import product

from src.core import fcis_fee_apportionment_allocator as allocator
from src.core.fcis_fee_apportionment_values import (
    BPS_DENOMINATOR_V2,
    MAX_FEE_AMOUNT_V2,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
    FeeApportionmentTransitionOkV2,
    FeeDeficitEntryV2,
    FeeDistributionPolicyV2,
)


def _agqe_select_bonuses(
    surpluses: tuple[int, int, int],
    remainders: tuple[int, int, int],
    denominator: int,
) -> tuple[int, int, int]:
    seat_count = sum(remainders) // denominator
    eligible = [index for index, remainder in enumerate(remainders) if remainder > 0]
    eligible.sort(key=lambda index: (surpluses[index] - remainders[index], index))
    selected = set(eligible[:seat_count])
    return (
        1 if 0 in selected else 0,
        1 if 1 in selected else 0,
        1 if 2 in selected else 0,
    )


def _agqe_transition(
    *,
    amount: int,
    weights: tuple[int, int, int],
    surpluses_pre: tuple[int, int, int],
    denominator: int,
) -> tuple[
    tuple[int, int, int],
    tuple[int, int, int],
    tuple[int, int, int],
    tuple[int, int, int],
]:
    cycles, residual = divmod(amount, denominator)
    products = (
        residual * weights[0],
        residual * weights[1],
        residual * weights[2],
    )
    lowers = (
        cycles * weights[0] + products[0] // denominator,
        cycles * weights[1] + products[1] // denominator,
        cycles * weights[2] + products[2] // denominator,
    )
    remainders = (
        products[0] % denominator,
        products[1] % denominator,
        products[2] % denominator,
    )
    bonuses = _agqe_select_bonuses(surpluses_pre, remainders, denominator)
    allocations = (
        lowers[0] + bonuses[0],
        lowers[1] + bonuses[1],
        lowers[2] + bonuses[2],
    )
    surpluses_post = (
        surpluses_pre[0] - remainders[0] + denominator * bonuses[0],
        surpluses_pre[1] - remainders[1] + denominator * bonuses[1],
        surpluses_pre[2] - remainders[2] + denominator * bonuses[2],
    )
    return remainders, bonuses, allocations, surpluses_post


def _key() -> FeeApportionmentKeyV2:
    return FeeApportionmentKeyV2("protocol-fees", "asset-a")


def _policy(weights: tuple[int, int, int]) -> FeeDistributionPolicyV2:
    return FeeDistributionPolicyV2(
        *weights,
        "buyback",
        "treasury",
        "rewards",
    )


def _state(
    key: FeeApportionmentKeyV2,
    deficits: tuple[int, int, int],
) -> CommittedFeeApportionmentStateV2:
    entries = (
        ()
        if deficits == (0, 0, 0)
        else (FeeDeficitEntryV2(key, deficits[0], deficits[1]),)
    )
    return CommittedFeeApportionmentStateV2(
        "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
        entries,
    )


def test_agqe_selector_is_exact_sign_dual_over_d1_through_d12() -> None:
    checked = 0
    for denominator in range(1, 13):
        deficits = tuple(
            (d0, d1, -d0 - d1)
            for d0 in range(-denominator + 1, denominator)
            for d1 in range(-denominator + 1, denominator)
            if -denominator < -d0 - d1 < denominator
        )
        remainder_vectors = tuple(
            (values[0], values[1], values[2])
            for values in product(range(denominator), repeat=3)
            if sum(values) in (0, denominator, 2 * denominator)
        )

        for deficit_pre, remainders in product(deficits, remainder_vectors):
            surplus_pre = (
                -deficit_pre[0],
                -deficit_pre[1],
                -deficit_pre[2],
            )
            srgd_bonuses = allocator._select_bonuses_v2(
                deficit_pre,
                remainders,
                denominator=denominator,
            )
            agqe_bonuses = _agqe_select_bonuses(
                surplus_pre,
                remainders,
                denominator,
            )
            assert agqe_bonuses == srgd_bonuses

            deficit_post = tuple(
                deficit + remainder - denominator * bonus
                for deficit, remainder, bonus in zip(
                    deficit_pre,
                    remainders,
                    srgd_bonuses,
                    strict=True,
                )
            )
            surplus_post = tuple(
                surplus - remainder + denominator * bonus
                for surplus, remainder, bonus in zip(
                    surplus_pre,
                    remainders,
                    agqe_bonuses,
                    strict=True,
                )
            )
            assert surplus_post == (
                -deficit_post[0],
                -deficit_post[1],
                -deficit_post[2],
            )
            checked += 1

    assert checked == 164_528


def test_public_srgd_transition_matches_independent_agqe_at_u256_boundaries() -> None:
    key = _key()
    weights_set = (
        (10_000, 0, 0),
        (0, 10_000, 0),
        (0, 0, 10_000),
        (5_000, 5_000, 0),
        (3_333, 3_333, 3_334),
        (1, 1, 9_998),
        (9_999, 1, 0),
    )
    deficits_set = (
        (0, 0, 0),
        (3_333, 3_333, -6_666),
        (-9_999, 0, 9_999),
        (5_000, -9_999, 4_999),
    )
    amounts = (
        0,
        1,
        BPS_DENOMINATOR_V2 - 1,
        BPS_DENOMINATOR_V2,
        BPS_DENOMINATOR_V2 + 1,
        2 * BPS_DENOMINATOR_V2 + 1,
        MAX_FEE_AMOUNT_V2,
    )

    for weights, deficits_pre, amount in product(weights_set, deficits_set, amounts):
        result = allocator.apply_fee_apportionment_v2(
            contributions=(FeeAmountCandidateV2(key, amount),),
            policy=_policy(weights),
            state=_state(key, deficits_pre),
        )
        assert type(result) is FeeApportionmentTransitionOkV2
        allocation = result.allocations[0]
        agqe = _agqe_transition(
            amount=amount,
            weights=weights,
            surpluses_pre=(
                -deficits_pre[0],
                -deficits_pre[1],
                -deficits_pre[2],
            ),
            denominator=BPS_DENOMINATOR_V2,
        )
        remainders, bonuses, amounts_expected, surpluses_post = agqe

        assert allocation.fractions == remainders
        assert allocation.bonuses == bonuses
        assert allocation.amounts == amounts_expected
        assert tuple(-value for value in allocation.deficits_post) == surpluses_post


def test_adaptive_policy_stream_preserves_the_sign_dual_state() -> None:
    key = _key()
    policies = (
        (3_333, 3_333, 3_334),
        (1, 1, 9_998),
        (9_999, 1, 0),
        (0, 5_000, 5_000),
        (5_000, 0, 5_000),
    )
    state = _state(key, (0, 0, 0))
    surpluses = (0, 0, 0)

    for step in range(1_000):
        adversarial_role = min(range(3), key=lambda index: (surpluses[index], index))
        weights = policies[(step + adversarial_role) % len(policies)]
        amount = (step * 17 + adversarial_role) % 37
        expected = _agqe_transition(
            amount=amount,
            weights=weights,
            surpluses_pre=surpluses,
            denominator=BPS_DENOMINATOR_V2,
        )
        result = allocator.apply_fee_apportionment_v2(
            contributions=(FeeAmountCandidateV2(key, amount),),
            policy=_policy(weights),
            state=state,
        )

        assert type(result) is FeeApportionmentTransitionOkV2
        allocation = result.allocations[0]
        assert (
            allocation.fractions,
            allocation.bonuses,
            allocation.amounts,
            tuple(-value for value in allocation.deficits_post),
        ) == expected
        state = result.state
        surpluses = expected[3]


def test_largest_surplus_mutation_is_killed_by_minimized_witness() -> None:
    denominator = 3
    deficit_pre = (-2, 1, 1)
    surplus_pre = (2, -1, -1)
    remainders = (0, 1, 2)

    correct = _agqe_select_bonuses(surplus_pre, remainders, denominator)
    srgd = allocator._select_bonuses_v2(
        deficit_pre,
        remainders,
        denominator=denominator,
    )
    eligible = [1, 2]
    wrong_role = max(
        eligible,
        key=lambda index: (surplus_pre[index] - remainders[index], -index),
    )
    wrong = (
        1 if wrong_role == 0 else 0,
        1 if wrong_role == 1 else 0,
        1 if wrong_role == 2 else 0,
    )

    assert correct == (0, 0, 1)
    assert srgd == correct
    assert wrong == (0, 1, 0)


def test_event_granularity_counterexample_is_retained() -> None:
    denominator = 10
    weights = (5, 2, 3)
    initial = (0, 0, 0)

    whole = _agqe_transition(
        amount=867,
        weights=weights,
        surpluses_pre=initial,
        denominator=denominator,
    )
    first = _agqe_transition(
        amount=493,
        weights=weights,
        surpluses_pre=initial,
        denominator=denominator,
    )
    second = _agqe_transition(
        amount=374,
        weights=weights,
        surpluses_pre=first[3],
        denominator=denominator,
    )
    split = tuple(
        left + right for left, right in zip(first[2], second[2], strict=True)
    )

    key = _key()
    production_policy = _policy((5_000, 2_000, 3_000))
    grouped_result = allocator.apply_fee_apportionment_v2(
        contributions=(
            FeeAmountCandidateV2(key, 493),
            FeeAmountCandidateV2(key, 374),
        ),
        policy=production_policy,
        state=_state(key, (0, 0, 0)),
    )
    first_result = allocator.apply_fee_apportionment_v2(
        contributions=(FeeAmountCandidateV2(key, 493),),
        policy=production_policy,
        state=_state(key, (0, 0, 0)),
    )
    assert type(grouped_result) is FeeApportionmentTransitionOkV2
    assert type(first_result) is FeeApportionmentTransitionOkV2
    second_result = allocator.apply_fee_apportionment_v2(
        contributions=(FeeAmountCandidateV2(key, 374),),
        policy=production_policy,
        state=first_result.state,
    )
    assert type(second_result) is FeeApportionmentTransitionOkV2
    public_split = tuple(
        left + right
        for left, right in zip(
            first_result.allocations[0].amounts,
            second_result.allocations[0].amounts,
            strict=True,
        )
    )

    assert whole[2] == (434, 173, 260)
    assert split == (433, 174, 260)
    assert whole[2] != split
    assert grouped_result.allocations[0].amounts == whole[2]
    assert public_split == split
