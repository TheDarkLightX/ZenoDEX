#!/usr/bin/env python3
"""Find a small exact subcube partition outside recursive split-tree form."""

from __future__ import annotations

import json

from run_experiment import recursively_generated_partitions
from subcube_certificate import Subcube


def all_subcubes(nchoices: int) -> tuple[tuple[Subcube, int], ...]:
    values: list[tuple[Subcube, int]] = []
    for fixed in range(1 << nchoices):
        positive = fixed
        while True:
            scope = Subcube(fixed, positive)
            covered = 0
            for assignment in range(1 << nchoices):
                if scope.matches_assignment(assignment):
                    covered |= 1 << assignment
            values.append((scope, covered))
            if positive == 0:
                break
            positive = (positive - 1) & fixed
    return tuple(values)


def classify_all(nchoices: int) -> dict[str, object]:
    known = {frozenset(partition) for partition in recursively_generated_partitions(nchoices)}
    universe = (1 << (1 << nchoices)) - 1
    subcubes = all_subcubes(nchoices)
    by_assignment: list[list[tuple[Subcube, int]]] = [[] for _ in range(1 << nchoices)]
    for scope, covered in subcubes:
        for assignment in range(1 << nchoices):
            if covered & (1 << assignment):
                by_assignment[assignment].append((scope, covered))
    for choices in by_assignment:
        choices.sort(key=lambda item: (-item[1].bit_count(), item[0]))

    exact_partitions_examined = 0
    nonrecursive_partitions = 0
    first_nonrecursive: tuple[Subcube, ...] | None = None

    def rec(uncovered: int, selected: tuple[Subcube, ...]) -> None:
        nonlocal exact_partitions_examined, first_nonrecursive, nonrecursive_partitions
        if uncovered == 0:
            exact_partitions_examined += 1
            family = frozenset(selected)
            if family not in known:
                nonrecursive_partitions += 1
                if first_nonrecursive is None:
                    first_nonrecursive = tuple(sorted(family))
            return
        first_bit = uncovered & -uncovered
        first_assignment = first_bit.bit_length() - 1
        for scope, covered in by_assignment[first_assignment]:
            if covered & ~uncovered:
                continue
            rec(uncovered ^ covered, (*selected, scope))

    rec(universe, ())
    return {
        "named_choices": nchoices,
        "recursive_partitions": len(known),
        "exact_partitions": exact_partitions_examined,
        "nonrecursive_partitions": nonrecursive_partitions,
        "found_nonrecursive": first_nonrecursive is not None,
        "witness": (
            [
                {
                    "fixed_mask": scope.fixed_mask,
                    "positive_mask": scope.positive_mask,
                }
                for scope in first_nonrecursive
            ]
            if first_nonrecursive is not None
            else None
        ),
    }


def main() -> int:
    rows = [classify_all(nchoices) for nchoices in (1, 2, 3)]
    print(json.dumps(rows, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
