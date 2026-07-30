from __future__ import annotations

from hashlib import sha256
from itertools import permutations, product

from src.core import fcis_fee_apportionment_allocator as allocator
from src.core.fcis_fee_apportionment_values import (
    MAX_FEE_AMOUNT_V2,
    SRGD_ALGORITHM_VERSION_V1,
    CommittedFeeApportionmentStateV2,
    FeeApportionmentKeyV2,
    FeeApportionmentTransitionOkV2,
    FeeDistributionPolicyV2,
)
from src.core.fcis_fee_occurrence_normal_form import (
    CanonicalFeeOccurrenceHistoryV1,
    CanonicalFeeOccurrenceSegmentV1,
    FeeOccurrenceNormalizationCodeV1,
    FeeOccurrenceNormalizationRejectV1,
    FeeWitnessOccurrenceClaimV1,
    canonicalize_fee_occurrence_history_v1,
    canonicalize_fee_occurrence_segment_v1,
    fee_amount_candidate_word_from_history_v1,
    fee_amount_candidates_from_segment_v1,
)


def _digest(label: str) -> str:
    return sha256(label.encode()).hexdigest()


def _key(asset: str = "asset-a") -> FeeApportionmentKeyV2:
    return FeeApportionmentKeyV2("protocol-fees", asset)


def _witness(
    position: int,
    amount: int,
    label: str,
    asset: str = "asset-a",
) -> FeeWitnessOccurrenceClaimV1:
    return FeeWitnessOccurrenceClaimV1(
        position,
        _key(asset),
        amount,
        _digest(label),
    )


def _segment(
    label: str,
    witnesses: tuple[FeeWitnessOccurrenceClaimV1, ...],
    *,
    policy_label: str = "policy",
) -> CanonicalFeeOccurrenceSegmentV1 | FeeOccurrenceNormalizationRejectV1:
    return canonicalize_fee_occurrence_segment_v1(
        boundary_root=_digest(f"boundary:{label}"),
        policy_root=_digest(policy_label),
        witnesses=witnesses,
    )


def test_same_segment_split_merge_has_one_semantic_point_and_two_lineages() -> None:
    whole = _segment("same", (_witness(0, 867, "whole"),))
    split = _segment(
        "same",
        (
            _witness(0, 493, "left"),
            _witness(1, 374, "right"),
        ),
    )

    assert type(whole) is CanonicalFeeOccurrenceSegmentV1
    assert type(split) is CanonicalFeeOccurrenceSegmentV1
    assert whole.semantic_vector == split.semantic_vector == ((_key(), 867),)
    assert whole.semantic_stream_root == split.semantic_stream_root
    assert whole.witness_tuple_root != split.witness_tuple_root
    assert whole.lineage_stream_root != split.lineage_stream_root


def test_fixed_positions_make_raw_input_permutation_irrelevant() -> None:
    witnesses = (
        _witness(0, 3, "w0", "asset-b"),
        _witness(1, 5, "w1", "asset-a"),
        _witness(2, 7, "w2", "asset-b"),
    )
    expected = _segment("permutation", witnesses)
    assert type(expected) is CanonicalFeeOccurrenceSegmentV1

    for candidate in permutations(witnesses):
        assert _segment("permutation", candidate) == expected


def test_distinct_keys_use_protocol_order_and_reconstruct_global_provenance() -> None:
    segment = _segment(
        "keys",
        (
            _witness(0, 2, "z0", "asset-z"),
            _witness(1, 3, "a0", "asset-a"),
            _witness(2, 5, "z1", "asset-z"),
        ),
    )
    assert type(segment) is CanonicalFeeOccurrenceSegmentV1
    assert segment.semantic_vector == (
        (_key("asset-a"), 3),
        (_key("asset-z"), 7),
    )

    recovered = tuple(
        sorted(
            (
                contributor
                for occurrence in segment.occurrences
                for contributor in occurrence.contributors
            ),
            key=lambda witness: witness.position,
        )
    )
    assert recovered == segment.ordered_witnesses


def test_history_is_a_word_and_projection_never_flattens_boundaries() -> None:
    one_segment = _segment(
        "whole",
        (
            _witness(0, 493, "left"),
            _witness(1, 374, "right"),
        ),
    )
    left_segment = _segment("left", (_witness(0, 493, "left"),))
    right_segment = _segment("right", (_witness(0, 374, "right"),))
    assert type(one_segment) is CanonicalFeeOccurrenceSegmentV1
    assert type(left_segment) is CanonicalFeeOccurrenceSegmentV1
    assert type(right_segment) is CanonicalFeeOccurrenceSegmentV1

    whole_history = canonicalize_fee_occurrence_history_v1((one_segment,))
    split_history = canonicalize_fee_occurrence_history_v1(
        (left_segment, right_segment)
    )
    assert type(whole_history) is CanonicalFeeOccurrenceHistoryV1
    assert type(split_history) is CanonicalFeeOccurrenceHistoryV1
    assert whole_history.semantic_word == (((_key(), 867),),)
    assert split_history.semantic_word == (
        ((_key(), 493),),
        ((_key(), 374),),
    )
    assert whole_history.semantic_word_root != split_history.semantic_word_root
    assert whole_history.lineage_word_root != split_history.lineage_word_root

    whole_candidates = fee_amount_candidate_word_from_history_v1(whole_history)
    split_candidates = fee_amount_candidate_word_from_history_v1(split_history)
    assert tuple(tuple(item.amount for item in segment) for segment in whole_candidates) == (
        (867,),
    )
    assert tuple(tuple(item.amount for item in segment) for segment in split_candidates) == (
        (493,),
        (374,),
    )


def test_zero_amount_witness_remains_an_explicit_occurrence() -> None:
    segment = _segment("zero", (_witness(0, 0, "zero"),))
    assert type(segment) is CanonicalFeeOccurrenceSegmentV1
    assert segment.semantic_vector == ((_key(), 0),)
    assert fee_amount_candidates_from_segment_v1(segment)[0].amount == 0


def test_small_exhaustive_mass_and_permutation_campaign() -> None:
    checked = 0
    for amounts in product(range(4), repeat=3):
        witnesses = (
            _witness(0, amounts[0], f"{amounts}:0", "asset-b"),
            _witness(1, amounts[1], f"{amounts}:1", "asset-a"),
            _witness(2, amounts[2], f"{amounts}:2", "asset-b"),
        )
        expected = _segment(f"campaign:{amounts}", witnesses)
        assert type(expected) is CanonicalFeeOccurrenceSegmentV1
        assert sum(amounts) == sum(amount for _key_value, amount in expected.semantic_vector)
        for candidate in permutations(witnesses):
            assert _segment(f"campaign:{amounts}", candidate) == expected
            checked += 1
    assert checked == 384


def test_position_duplicate_and_u256_attacks_reject() -> None:
    gap = _segment("gap", (_witness(1, 1, "gap"),))
    assert type(gap) is FeeOccurrenceNormalizationRejectV1
    assert gap.code is FeeOccurrenceNormalizationCodeV1.NONCANONICAL_POSITION

    duplicate_root = _digest("duplicate")
    duplicate = _segment(
        "duplicate",
        (
            FeeWitnessOccurrenceClaimV1(0, _key(), 1, duplicate_root),
            FeeWitnessOccurrenceClaimV1(1, _key(), 2, duplicate_root),
        ),
    )
    assert type(duplicate) is FeeOccurrenceNormalizationRejectV1
    assert duplicate.code is FeeOccurrenceNormalizationCodeV1.DUPLICATE_WITNESS

    overflow = _segment(
        "overflow",
        (
            _witness(0, MAX_FEE_AMOUNT_V2, "maximum"),
            _witness(1, 1, "one"),
        ),
    )
    assert type(overflow) is FeeOccurrenceNormalizationRejectV1
    assert overflow.code is FeeOccurrenceNormalizationCodeV1.AGGREGATE_OVERFLOW


def test_boundary_and_policy_substitution_change_semantic_identity() -> None:
    witnesses = (_witness(0, 1, "witness"),)
    first = canonicalize_fee_occurrence_segment_v1(
        boundary_root=_digest("boundary-a"),
        policy_root=_digest("policy-a"),
        witnesses=witnesses,
    )
    changed_boundary = canonicalize_fee_occurrence_segment_v1(
        boundary_root=_digest("boundary-b"),
        policy_root=_digest("policy-a"),
        witnesses=witnesses,
    )
    changed_policy = canonicalize_fee_occurrence_segment_v1(
        boundary_root=_digest("boundary-a"),
        policy_root=_digest("policy-b"),
        witnesses=witnesses,
    )
    assert type(first) is CanonicalFeeOccurrenceSegmentV1
    assert type(changed_boundary) is CanonicalFeeOccurrenceSegmentV1
    assert type(changed_policy) is CanonicalFeeOccurrenceSegmentV1
    assert first.semantic_stream_root != changed_boundary.semantic_stream_root
    assert first.semantic_stream_root != changed_policy.semantic_stream_root


def test_production_allocator_has_tiny_zero_history_boundary_counterexample() -> None:
    whole_segment = _segment("whole-3", (_witness(0, 3, "whole"),))
    left_segment = _segment("left-1", (_witness(0, 1, "left"),))
    right_segment = _segment("right-2", (_witness(0, 2, "right"),))
    assert type(whole_segment) is CanonicalFeeOccurrenceSegmentV1
    assert type(left_segment) is CanonicalFeeOccurrenceSegmentV1
    assert type(right_segment) is CanonicalFeeOccurrenceSegmentV1

    policy = FeeDistributionPolicyV2(
        2_500,
        2_500,
        5_000,
        "buyback",
        "treasury",
        "rewards",
    )
    initial = CommittedFeeApportionmentStateV2(SRGD_ALGORITHM_VERSION_V1, ())
    whole = allocator.apply_fee_apportionment_v2(
        contributions=fee_amount_candidates_from_segment_v1(whole_segment),
        policy=policy,
        state=initial,
    )
    first = allocator.apply_fee_apportionment_v2(
        contributions=fee_amount_candidates_from_segment_v1(left_segment),
        policy=policy,
        state=initial,
    )
    assert type(whole) is FeeApportionmentTransitionOkV2
    assert type(first) is FeeApportionmentTransitionOkV2
    second = allocator.apply_fee_apportionment_v2(
        contributions=fee_amount_candidates_from_segment_v1(right_segment),
        policy=policy,
        state=first.state,
    )
    assert type(second) is FeeApportionmentTransitionOkV2

    split_allocations = tuple(
        left + right
        for left, right in zip(
            first.allocations[0].amounts,
            second.allocations[0].amounts,
            strict=True,
        )
    )
    assert whole.allocations[0].amounts == (1, 1, 1)
    assert split_allocations == (1, 0, 2)
    assert whole.allocations[0].deficits_post == (-2_500, -2_500, 5_000)
    assert second.allocations[0].deficits_post == (-2_500, 7_500, -5_000)


def _reference_step(
    amount: int,
    weights: tuple[int, int, int],
    deficits: tuple[int, int, int],
    denominator: int,
) -> tuple[tuple[int, int, int], tuple[int, int, int]]:
    cycles, residual = divmod(amount, denominator)
    products = tuple(residual * weight for weight in weights)
    lowers = tuple(
        cycles * weight + product_value // denominator
        for weight, product_value in zip(weights, products, strict=True)
    )
    fractions = tuple(product_value % denominator for product_value in products)
    seat_count = sum(fractions) // denominator
    eligible = [index for index, fraction in enumerate(fractions) if fraction > 0]
    eligible.sort(key=lambda index: (-(deficits[index] + fractions[index]), index))
    selected = set(eligible[:seat_count])
    bonuses = tuple(int(index in selected) for index in range(3))
    allocations = tuple(
        lower + bonus for lower, bonus in zip(lowers, bonuses, strict=True)
    )
    post = tuple(
        deficit + fraction - denominator * bonus
        for deficit, fraction, bonus in zip(
            deficits,
            fractions,
            bonuses,
            strict=True,
        )
    )
    return allocations, post


def test_d4_is_smallest_zero_history_boundary_counterexample_residue_domain() -> None:
    for denominator in range(1, 4):
        for left_weight in range(denominator + 1):
            for middle_weight in range(denominator - left_weight + 1):
                weights = (
                    left_weight,
                    middle_weight,
                    denominator - left_weight - middle_weight,
                )
                for left_amount, right_amount in product(range(denominator), repeat=2):
                    whole = _reference_step(
                        left_amount + right_amount,
                        weights,
                        (0, 0, 0),
                        denominator,
                    )
                    first = _reference_step(
                        left_amount,
                        weights,
                        (0, 0, 0),
                        denominator,
                    )
                    second = _reference_step(
                        right_amount,
                        weights,
                        first[1],
                        denominator,
                    )
                    split_allocations = tuple(
                        left + right
                        for left, right in zip(first[0], second[0], strict=True)
                    )
                    assert whole == (split_allocations, second[1])

    whole = _reference_step(3, (1, 1, 2), (0, 0, 0), 4)
    first = _reference_step(1, (1, 1, 2), (0, 0, 0), 4)
    second = _reference_step(2, (1, 1, 2), first[1], 4)
    split_allocations = tuple(
        left + right for left, right in zip(first[0], second[0], strict=True)
    )
    assert whole == ((1, 1, 1), (-1, -1, 2))
    assert (split_allocations, second[1]) == ((1, 0, 2), (-1, 3, -2))
