"""Deterministic counterexamples for the P4B5A corrected cursor proposal.

This is review evidence only. It is not runtime or protocol code.
"""

from __future__ import annotations

import json
from fractions import Fraction


def prefix_counts(weights: tuple[int, int, int], denominator: int, t: int) -> tuple[int, int, int]:
    w0, w1, _w2 = weights
    p0 = t * w0 // denominator
    remaining = t - p0
    p1 = remaining * w1 // (denominator - w0) if denominator != w0 else 0
    return p0, p1, t - p0 - p1


def allocate(
    weights: tuple[int, int, int],
    denominator: int,
    cursor: int,
    amount: int,
) -> tuple[tuple[int, int, int], int]:
    before = prefix_counts(weights, denominator, cursor)
    after = prefix_counts(weights, denominator, cursor + amount)
    return tuple(right - left for left, right in zip(before, after, strict=True)), (
        cursor + amount
    ) % denominator


def minimum_role2_weight_for_one_atom(denominator: int, cursor: int) -> tuple[int, int, int]:
    """Choose the smallest role-2 weight that awards the current atom to role 2.

    Restricting role 1 to zero is enough to produce the production-denominator
    adaptive-policy witness.
    """

    for w2 in range(denominator + 1):
        weights = (denominator - w2, 0, w2)
        amounts, _next_cursor = allocate(weights, denominator, cursor, 1)
        if amounts[2] == 1:
            return weights
    raise AssertionError("every cursor must admit a role-2 assignment")


def d4_reachable_witness() -> dict[str, object]:
    denominator = 4
    policies = ((3, 0, 1), (1, 1, 2), (2, 0, 2), (4, 0, 0))
    cursor = 0
    actual = 0
    ideal = Fraction(0)
    trace: list[dict[str, object]] = []
    for step in range(1, 9):
        weights = policies[cursor]
        amounts, next_cursor = allocate(weights, denominator, cursor, 1)
        actual += amounts[2]
        ideal += Fraction(weights[2], denominator)
        trace.append(
            {
                "step": step,
                "cursor_before": cursor,
                "weights": weights,
                "role2_actual": actual,
                "role2_ideal": str(ideal),
                "role2_excess": str(actual - ideal),
            }
        )
        cursor = next_cursor
    assert trace[4]["role2_excess"] == "5/2"
    assert actual - ideal == Fraction(7, 2)
    return {"trace": trace, "eight_step_excess": str(actual - ideal)}


def production_denominator_witness() -> dict[str, object]:
    denominator = 10_000
    cursor = 0
    actual = 0
    ideal = Fraction(0)
    first_policies: list[tuple[int, int, int]] = []
    for _epoch in range(100):
        weights = minimum_role2_weight_for_one_atom(denominator, cursor)
        if len(first_policies) < 10:
            first_policies.append(weights)
        amounts, cursor = allocate(weights, denominator, cursor, 1)
        actual += amounts[2]
        ideal += Fraction(weights[2], denominator)
    excess = actual - ideal
    assert actual == 100
    assert ideal == Fraction(20_967, 5_000)
    assert excess == Fraction(479_033, 5_000)
    return {
        "epochs": 100,
        "role2_actual": actual,
        "role2_ideal": str(ideal),
        "role2_excess": str(excess),
        "first_policies": first_policies,
    }


def role1_interval_bound_witness() -> dict[str, object]:
    denominator = 10_000
    weights = (1, 9_998, 1)
    cursor = 1
    amount = 9_998
    amounts, _next_cursor = allocate(weights, denominator, cursor, amount)
    ideal = Fraction(amount * weights[1], denominator)
    discrepancy = Fraction(amounts[1]) - ideal
    assert amounts[1] == 9_998
    assert discrepancy == Fraction(4_999, 2_500)
    assert discrepancy > 1
    return {
        "weights": weights,
        "cursor": cursor,
        "amount": amount,
        "role1_actual": amounts[1],
        "role1_ideal": str(ideal),
        "role1_discrepancy": str(discrepancy),
    }


def u256_cursor_intermediate_witness() -> dict[str, object]:
    denominator = 10_000
    maximum = (1 << 256) - 1
    cursor = denominator - 1
    remainder = maximum % denominator
    unsafe_sum = cursor + maximum
    safe_cursor = (cursor + remainder) % denominator
    assert unsafe_sum > maximum
    assert safe_cursor == unsafe_sum % denominator
    return {
        "q_plus_n_exceeds_u256": True,
        "safe_cursor": safe_cursor,
        "required_formula": "(q + (n mod D)) mod D",
    }


def main() -> None:
    receipt = {
        "d4_adaptive_policy": d4_reachable_witness(),
        "d10000_adaptive_policy": production_denominator_witness(),
        "role1_interval_bound": role1_interval_bound_witness(),
        "u256_cursor_intermediate": u256_cursor_intermediate_witness(),
    }
    print(json.dumps(receipt, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
