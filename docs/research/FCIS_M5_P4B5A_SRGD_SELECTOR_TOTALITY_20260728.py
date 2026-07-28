"""Exhaustive D=4 selector-totality evidence for the SRGD-v1 amendment."""

from __future__ import annotations

import itertools
import json
from collections.abc import Iterator

D = 4
ROLE_COUNT = 3


def _valid_states() -> Iterator[tuple[int, int, int]]:
    for state in itertools.product(range(-(D - 1), D), repeat=ROLE_COUNT):
        if sum(state) == 0:
            yield state


def _valid_fractions() -> Iterator[tuple[int, int, int]]:
    for fractions in itertools.product(range(D), repeat=ROLE_COUNT):
        if sum(fractions) in (0, D, 2 * D):
            yield fractions


def _selector(
    state: tuple[int, int, int],
    fractions: tuple[int, int, int],
) -> tuple[int, int, int]:
    seat_count = sum(fractions) // D
    eligible = tuple(index for index, fraction in enumerate(fractions) if fraction > 0)
    if len(eligible) < seat_count:
        raise AssertionError("valid quota remainders must have enough positive support")
    ranked = sorted(eligible, key=lambda index: (-(state[index] + fractions[index]), index))
    selected = frozenset(ranked[:seat_count])
    return tuple(int(index in selected) for index in range(ROLE_COUNT))


def _relation_holds(
    state: tuple[int, int, int],
    fractions: tuple[int, int, int],
    bonuses: tuple[int, int, int],
    *,
    strict_semantic_ties: bool,
) -> bool:
    if D * sum(bonuses) != sum(fractions):
        return False
    if any(bonus and fraction == 0 for bonus, fraction in zip(bonuses, fractions, strict=True)):
        return False
    scores = tuple(deficit + fraction for deficit, fraction in zip(state, fractions, strict=True))
    for selected in range(ROLE_COUNT):
        if bonuses[selected] == 0:
            continue
        for unselected in range(ROLE_COUNT):
            if bonuses[unselected] == 1 or fractions[unselected] == 0:
                continue
            if strict_semantic_ties and selected > unselected:
                if scores[selected] <= scores[unselected]:
                    return False
            elif scores[selected] < scores[unselected]:
                return False
    return True


def main() -> None:
    pair_count = 0
    relaxed_tie_nondeterministic_pairs = 0
    nonzero_fraction_pairs = 0
    strengthened_guard_enabled_nonzero_pairs = 0

    for state in _valid_states():
        for fractions in _valid_fractions():
            pair_count += 1
            expected = _selector(state, fractions)
            valid = tuple(
                bonuses
                for bonuses in itertools.product((0, 1), repeat=ROLE_COUNT)
                if _relation_holds(
                    state,
                    fractions,
                    bonuses,
                    strict_semantic_ties=True,
                )
            )
            if valid != (expected,):
                raise AssertionError(
                    f"selector relation is not uniquely total: {state=}, {fractions=}, {valid=}"
                )

            relaxed = tuple(
                bonuses
                for bonuses in itertools.product((0, 1), repeat=ROLE_COUNT)
                if _relation_holds(
                    state,
                    fractions,
                    bonuses,
                    strict_semantic_ties=False,
                )
            )
            if len(relaxed) > 1:
                relaxed_tie_nondeterministic_pairs += 1

            if sum(fractions) > 0:
                nonzero_fraction_pairs += 1
                if 100 * sum(expected) == sum(fractions):
                    strengthened_guard_enabled_nonzero_pairs += 1

    expected_receipt = {
        "denominator": 4,
        "invariant_state_count": 37,
        "valid_fraction_count": 16,
        "state_fraction_pair_count": 592,
        "unique_selector_pair_count": 592,
        "relaxed_tie_nondeterministic_pair_count": 57,
        "nonzero_fraction_pair_count": 555,
        "strengthened_guard_enabled_nonzero_pair_count": 0,
    }
    actual_receipt = {
        "denominator": D,
        "invariant_state_count": sum(1 for _ in _valid_states()),
        "valid_fraction_count": sum(1 for _ in _valid_fractions()),
        "state_fraction_pair_count": pair_count,
        "unique_selector_pair_count": pair_count,
        "relaxed_tie_nondeterministic_pair_count": relaxed_tie_nondeterministic_pairs,
        "nonzero_fraction_pair_count": nonzero_fraction_pairs,
        "strengthened_guard_enabled_nonzero_pair_count": (strengthened_guard_enabled_nonzero_pairs),
    }
    if actual_receipt != expected_receipt:
        raise AssertionError(f"selector evidence drift: {actual_receipt!r}")
    print(json.dumps(actual_receipt, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
