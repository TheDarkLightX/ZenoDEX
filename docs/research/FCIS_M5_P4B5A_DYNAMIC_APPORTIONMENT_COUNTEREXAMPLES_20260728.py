"""Deterministic evidence for the P4B5A dynamic-apportionment problem.

This file is research evidence. It is not runtime or protocol authority.
"""

from __future__ import annotations

import json
from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class ErrorVectorStep:
    allocation: tuple[int, int, int]
    next_deficit_numerators: tuple[int, int, int]


def error_vector_step(
    *,
    denominator: int,
    weights: tuple[int, int, int],
    deficit_numerators: tuple[int, int, int],
    amount: int,
) -> ErrorVectorStep:
    """Apply the leading dynamic error-vector hypothesis.

    Deficit means cumulative ideal numerator minus allocated numerator. The
    deterministic bonus tie-break is descending score, then ascending role
    index.
    """

    if denominator <= 0:
        raise ValueError("denominator must be positive")
    if amount < 0:
        raise ValueError("amount must be nonnegative")
    if any(weight < 0 for weight in weights) or sum(weights) != denominator:
        raise ValueError("weights must be nonnegative and sum to denominator")
    if sum(deficit_numerators) != 0:
        raise ValueError("deficit numerators must sum to zero")
    if any(abs(value) >= denominator for value in deficit_numerators):
        raise ValueError("each deficit numerator must have magnitude below denominator")

    cycles, remainder = divmod(amount, denominator)
    base = tuple(cycles * weight + (remainder * weight) // denominator for weight in weights)
    fractional_numerators = tuple((remainder * weight) % denominator for weight in weights)
    bonus_count, bonus_remainder = divmod(
        sum(fractional_numerators),
        denominator,
    )
    if bonus_remainder != 0 or bonus_count not in (0, 1, 2):
        raise AssertionError("fractional numerators must encode zero, one, or two bonuses")

    scores = tuple(
        deficit + fractional
        for deficit, fractional in zip(
            deficit_numerators,
            fractional_numerators,
            strict=True,
        )
    )
    selected = frozenset(sorted(range(3), key=lambda index: (-scores[index], index))[:bonus_count])
    bonuses = tuple(1 if index in selected else 0 for index in range(3))
    allocation = tuple(
        base_amount + bonus for base_amount, bonus in zip(base, bonuses, strict=True)
    )
    next_deficits = tuple(
        score - denominator * bonus for score, bonus in zip(scores, bonuses, strict=True)
    )

    if sum(allocation) != amount:
        raise AssertionError("allocation must conserve the amount")
    if sum(next_deficits) != 0:
        raise AssertionError("next deficits must sum to zero")
    if any(abs(value) >= denominator for value in next_deficits):
        raise AssertionError("the sub-one-atom deficit invariant must be preserved")

    return ErrorVectorStep(
        allocation=allocation,
        next_deficit_numerators=next_deficits,
    )


def bounded_error_vector_invariant() -> dict[str, int]:
    """Exhaust one-step inductiveness for small denominators."""

    checked = 0
    for denominator in range(2, 9):
        weights = tuple(
            (w0, w1, denominator - w0 - w1)
            for w0 in range(denominator + 1)
            for w1 in range(denominator - w0 + 1)
        )
        for d0 in range(-(denominator - 1), denominator):
            for d1 in range(-(denominator - 1), denominator):
                d2 = -d0 - d1
                if abs(d2) >= denominator:
                    continue
                deficits = (d0, d1, d2)
                for policy in weights:
                    for amount in range(2 * denominator + 1):
                        error_vector_step(
                            denominator=denominator,
                            weights=policy,
                            deficit_numerators=deficits,
                            amount=amount,
                        )
                        checked += 1
    return {
        "minimum_denominator": 2,
        "maximum_denominator": 8,
        "one_step_cases": checked,
    }


def error_vector_fragmentation_witness() -> dict[str, object]:
    """Show that bounded deficit does not imply exact fragmentation."""

    denominator = 4
    weights = (1, 1, 2)
    initial = (0, 0, 0)
    whole = error_vector_step(
        denominator=denominator,
        weights=weights,
        deficit_numerators=initial,
        amount=3,
    )
    first = error_vector_step(
        denominator=denominator,
        weights=weights,
        deficit_numerators=initial,
        amount=1,
    )
    second = error_vector_step(
        denominator=denominator,
        weights=weights,
        deficit_numerators=first.next_deficit_numerators,
        amount=2,
    )
    combined = tuple(
        left + right for left, right in zip(first.allocation, second.allocation, strict=True)
    )

    if whole.allocation != (1, 1, 1):
        raise AssertionError("unexpected whole-step witness")
    if combined != (1, 0, 2):
        raise AssertionError("unexpected fragmented witness")
    if whole.allocation == combined:
        raise AssertionError("fragmentation witness must distinguish the schedules")

    return {
        "denominator": denominator,
        "weights": weights,
        "initial_deficit_numerators": initial,
        "whole": {
            "allocation": whole.allocation,
            "next_deficit_numerators": whole.next_deficit_numerators,
        },
        "split": {
            "amounts": (1, 2),
            "first_allocation": first.allocation,
            "second_allocation": second.allocation,
            "combined_allocation": combined,
            "next_deficit_numerators": second.next_deficit_numerators,
        },
    }


def main() -> None:
    result = {
        "bounded_error_vector_invariant": bounded_error_vector_invariant(),
        "error_vector_fragmentation": error_vector_fragmentation_witness(),
    }
    print(json.dumps(result, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
