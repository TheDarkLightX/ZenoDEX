from __future__ import annotations

from itertools import permutations, product

from src.core import fcis_fee_apportionment_allocator as allocator
from src.core.fcis_fee_apportionment_values import (
    BPS_DENOMINATOR_V2,
    MAX_FEE_AMOUNT_CANDIDATES_V2,
    MAX_FEE_AMOUNT_V2,
    AssetFeeAllocationV2,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
    FeeApportionmentTransitionCodeV2,
    FeeApportionmentTransitionOkV2,
    FeeApportionmentTransitionRejectV2,
    FeeDeficitEntryV2,
    FeeDistributionPolicyV2,
)


def _key(domain: str = "domain-a", asset: str = "asset-a") -> FeeApportionmentKeyV2:
    return FeeApportionmentKeyV2(domain, asset)


def _policy(
    weights: tuple[int, int, int] = (3_333, 3_333, 3_334),
    destinations: tuple[str, str, str] = ("buyback", "treasury", "rewards"),
) -> FeeDistributionPolicyV2:
    return FeeDistributionPolicyV2(*weights, *destinations)


def _state(
    *entries: tuple[FeeApportionmentKeyV2, tuple[int, int]],
) -> CommittedFeeApportionmentStateV2:
    exact = tuple(
        FeeDeficitEntryV2(key, deficits[0], deficits[1])
        for key, deficits in sorted(entries, key=lambda item: item[0].protocol_order_key)
    )
    return CommittedFeeApportionmentStateV2(
        "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
        exact,
    )


def _accepted(
    *,
    amount: int,
    weights: tuple[int, int, int] = (3_333, 3_333, 3_334),
    deficits: tuple[int, int, int] = (0, 0, 0),
) -> AssetFeeAllocationV2:
    key = _key()
    pre = _state((key, (deficits[0], deficits[1]))) if deficits != (0, 0, 0) else _state()
    result = allocator.apply_fee_apportionment_v2(
        contributions=(FeeAmountCandidateV2(key, amount),),
        policy=_policy(weights),
        state=pre,
    )
    assert type(result) is FeeApportionmentTransitionOkV2
    assert len(result.allocations) == 1
    return result.allocations[0]


def _independent_selector(
    deficits: tuple[int, int, int],
    fractions: tuple[int, int, int],
    denominator: int,
) -> tuple[int, int, int]:
    seat_count = sum(fractions) // denominator
    candidates: list[tuple[int, int, int]] = []
    for bonus in product((0, 1), repeat=3):
        if sum(bonus) != seat_count:
            continue
        if any(bonus[index] and fractions[index] == 0 for index in range(3)):
            continue
        selected = [index for index in range(3) if bonus[index]]
        unselected = [index for index in range(3) if not bonus[index] and fractions[index] > 0]
        valid = True
        for chosen in selected:
            for skipped in unselected:
                chosen_rank = (deficits[chosen] + fractions[chosen], -chosen)
                skipped_rank = (deficits[skipped] + fractions[skipped], -skipped)
                if chosen_rank < skipped_rank:
                    valid = False
        if valid:
            candidates.append(bonus)
    assert len(candidates) == 1
    return candidates[0]


def test_selector_refines_independent_eight_tuple_oracle_over_d4_domain() -> None:
    denominator = 4
    states = tuple(
        (d0, d1, -d0 - d1)
        for d0 in range(-denominator + 1, denominator)
        for d1 in range(-denominator + 1, denominator)
        if -denominator < -d0 - d1 < denominator
    )
    fractions = tuple(
        values
        for values in product(range(denominator), repeat=3)
        if sum(values) in (0, denominator, 2 * denominator)
    )

    assert len(states) == 37
    assert len(fractions) == 16
    for deficits, residuals in product(states, fractions):
        assert allocator._select_bonuses_v2(
            deficits,
            residuals,
            denominator=denominator,
        ) == _independent_selector(deficits, residuals, denominator)


def test_production_distinguishing_vectors() -> None:
    vectors = (
        (0, (3_333, 3_333, 3_334), (0, 0, 0), (0, 0, 0), (0, 0, 0)),
        (1, (3_333, 3_333, 3_334), (0, 0, 0), (0, 0, 1), (3_333, 3_333, -6_666)),
        (1, (5_000, 5_000, 0), (0, 0, 0), (1, 0, 0), (-5_000, 5_000, 0)),
        (2, (5_000, 2_500, 2_500), (0, 0, 0), (1, 1, 0), (0, -5_000, 5_000)),
        (
            1,
            (0, 3_333, 6_667),
            (-6_666, 3_333, 3_333),
            (0, 0, 1),
            (-6_666, 6_666, 0),
        ),
        (2, (3_333, 3_333, 3_334), (0, 0, 0), (1, 0, 1), (-3_334, 6_666, -3_332)),
        (
            BPS_DENOMINATOR_V2 - 1,
            (3_333, 3_333, 3_334),
            (0, 0, 0),
            (3_333, 3_333, 3_333),
            (-3_333, -3_333, 6_666),
        ),
        (
            BPS_DENOMINATOR_V2,
            (3_333, 3_333, 3_334),
            (3_333, 3_333, -6_666),
            (3_333, 3_333, 3_334),
            (3_333, 3_333, -6_666),
        ),
        (
            BPS_DENOMINATOR_V2 + 1,
            (3_333, 3_333, 3_334),
            (0, 0, 0),
            (3_333, 3_333, 3_335),
            (3_333, 3_333, -6_666),
        ),
        (
            MAX_FEE_AMOUNT_V2,
            (10_000, 0, 0),
            (0, 0, 0),
            (MAX_FEE_AMOUNT_V2, 0, 0),
            (0, 0, 0),
        ),
    )

    for amount, weights, pre, expected_amounts, expected_post in vectors:
        allocation = _accepted(amount=amount, weights=weights, deficits=pre)
        assert allocation.amounts == expected_amounts
        assert allocation.deficits_post == expected_post
        assert sum(allocation.amounts) == amount
        assert sum(allocation.deficits_post) == 0
        assert all(-BPS_DENOMINATOR_V2 < value < BPS_DENOMINATOR_V2 for value in expected_post)
        assert all(
            not bonus or fraction > 0
            for bonus, fraction in zip(allocation.bonuses, allocation.fractions, strict=True)
        )


def test_same_step_grouping_and_input_permutation_are_exact() -> None:
    key_a = _key("domain-a", "asset-a")
    key_b = _key("domain-a", "asset-b")
    contributions = (
        FeeAmountCandidateV2(key_b, 3),
        FeeAmountCandidateV2(key_a, 1),
        FeeAmountCandidateV2(key_a, 2),
    )
    expected: FeeApportionmentTransitionOkV2 | None = None
    for ordering in permutations(contributions):
        result = allocator.apply_fee_apportionment_v2(
            contributions=ordering,
            policy=_policy(),
            state=_state(),
        )
        assert type(result) is FeeApportionmentTransitionOkV2
        if expected is None:
            expected = result
        else:
            assert result == expected
    assert expected is not None
    assert tuple(item.key for item in expected.allocations) == (key_a, key_b)
    assert tuple(item.amount for item in expected.allocations) == (3, 3)


def test_aggregate_overflow_rejects_without_successor() -> None:
    key = _key()
    pre = _state()
    result = allocator.apply_fee_apportionment_v2(
        contributions=(
            FeeAmountCandidateV2(key, MAX_FEE_AMOUNT_V2),
            FeeAmountCandidateV2(key, 1),
        ),
        policy=_policy(),
        state=pre,
    )

    assert result == FeeApportionmentTransitionRejectV2(
        FeeApportionmentTransitionCodeV2.AGGREGATE_OVERFLOW,
        ("contributions", "aggregate", "domain-a", "asset-a"),
    )
    assert pre == _state()


def test_top_level_exact_types_precede_bounded_item_limit() -> None:
    candidate = FeeAmountCandidateV2(_key(), 1)
    oversized = (candidate,) * (MAX_FEE_AMOUNT_CANDIDATES_V2 + 1)

    wrong_policy = allocator.apply_fee_apportionment_v2(
        contributions=oversized,
        policy=object(),
        state=_state(),
    )
    limited = allocator.apply_fee_apportionment_v2(
        contributions=oversized,
        policy=_policy(),
        state=_state(),
    )

    assert wrong_policy == FeeApportionmentTransitionRejectV2(
        FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
        ("policy",),
    )
    assert limited == FeeApportionmentTransitionRejectV2(
        FeeApportionmentTransitionCodeV2.ITEM_LIMIT,
        ("contributions",),
    )


def test_policy_and_destination_rotation_preserve_deficit_state() -> None:
    key = _key()
    first = allocator.apply_fee_apportionment_v2(
        contributions=(FeeAmountCandidateV2(key, 1),),
        policy=_policy(),
        state=_state(),
    )
    assert type(first) is FeeApportionmentTransitionOkV2

    second = allocator.apply_fee_apportionment_v2(
        contributions=(FeeAmountCandidateV2(key, 0),),
        policy=_policy((1, 1, 9_998), ("b2", "t2", "r2")),
        state=first.state,
    )

    assert type(second) is FeeApportionmentTransitionOkV2
    assert second.allocations[0].deficits_pre == first.allocations[0].deficits_post
    assert second.allocations[0].deficits_post == first.allocations[0].deficits_post


def test_adaptive_policy_sequence_keeps_exact_cumulative_error_below_one_atom() -> None:
    key = _key()
    policies = (
        (3_333, 3_333, 3_334),
        (1, 1, 9_998),
        (9_999, 1, 0),
        (0, 5_000, 5_000),
        (5_000, 0, 5_000),
    )
    state = _state()
    cumulative_ideal_numerators = [0, 0, 0]
    cumulative_actual = [0, 0, 0]

    for step in range(1_000):
        current_deficits = (0, 0, 0) if not state.entries else state.entries[0].deficits
        adversarial_index = max(
            range(3),
            key=lambda index: (current_deficits[index], -index),
        )
        weights = policies[(step + adversarial_index) % len(policies)]
        amount = (step * 7 + current_deficits[adversarial_index]) % 23
        result = allocator.apply_fee_apportionment_v2(
            contributions=(FeeAmountCandidateV2(key, amount),),
            policy=_policy(weights),
            state=state,
        )

        assert type(result) is FeeApportionmentTransitionOkV2
        allocation = result.allocations[0]
        for index in range(3):
            cumulative_ideal_numerators[index] += amount * weights[index]
            cumulative_actual[index] += allocation.amounts[index]
            assert (
                cumulative_ideal_numerators[index] - BPS_DENOMINATOR_V2 * cumulative_actual[index]
                == allocation.deficits_post[index]
            )
            assert abs(allocation.deficits_post[index]) < BPS_DENOMINATOR_V2
        state = result.state


def test_zero_result_uses_unique_sparse_state_representation() -> None:
    result = allocator.apply_fee_apportionment_v2(
        contributions=(FeeAmountCandidateV2(_key(), 0),),
        policy=_policy(),
        state=_state(),
    )

    assert type(result) is FeeApportionmentTransitionOkV2
    assert result.state.entries == ()
    assert result.allocations[0].amounts == (0, 0, 0)


def test_hostile_nested_mutation_fails_closed() -> None:
    candidate = FeeAmountCandidateV2(_key(), 1)
    object.__setattr__(candidate.key, "asset", "")

    result = allocator.apply_fee_apportionment_v2(
        contributions=(candidate,),
        policy=_policy(),
        state=_state(),
    )

    assert result == FeeApportionmentTransitionRejectV2(
        FeeApportionmentTransitionCodeV2.NONCANONICAL_IDENTIFIER,
        ("contributions", "0", "key", "asset"),
    )


def test_fixed_policy_fragmentation_difference_is_at_most_one_atom() -> None:
    weights = (2_500, 2_500, 5_000)
    for total in range(24):
        whole = _accepted(amount=total, weights=weights)
        for first_amount in range(total + 1):
            key = _key()
            first = allocator.apply_fee_apportionment_v2(
                contributions=(FeeAmountCandidateV2(key, first_amount),),
                policy=_policy(weights),
                state=_state(),
            )
            assert type(first) is FeeApportionmentTransitionOkV2
            second = allocator.apply_fee_apportionment_v2(
                contributions=(FeeAmountCandidateV2(key, total - first_amount),),
                policy=_policy(weights),
                state=first.state,
            )
            assert type(second) is FeeApportionmentTransitionOkV2
            split = tuple(
                left + right
                for left, right in zip(
                    first.allocations[0].amounts,
                    second.allocations[0].amounts,
                    strict=True,
                )
            )
            assert all(
                abs(left - right) <= 1 for left, right in zip(whole.amounts, split, strict=True)
            )
