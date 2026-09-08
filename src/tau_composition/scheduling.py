"""Deterministic finite dependency graphs for repair scheduling."""

from __future__ import annotations


def topological_order(size: int, edges: frozenset[tuple[int, int]]) -> tuple[int, ...] | None:
    remaining = set(range(size))
    result = []
    while remaining:
        ready = sorted(node for node in remaining if not any(
            target == node and source in remaining for source, target in edges
        ))
        if not ready:
            return None
        result.extend(ready)
        remaining.difference_update(ready)
    return tuple(result)


def strongly_connected_groups(size: int, edges: frozenset[tuple[int, int]]) -> tuple[tuple[int, ...], ...]:
    """Bounded transitive closure avoids recursive graph traversal.

    At most 128 requirements enter this research compiler. This deliberately
    simple O(n^3) closure is separate from the expensive native logical work.
    """
    reachable = [{index} for index in range(size)]
    for source, target in edges:
        reachable[source].add(target)
    for middle in range(size):
        for source in range(size):
            if middle in reachable[source]:
                reachable[source].update(reachable[middle])
    unused = set(range(size))
    groups = []
    while unused:
        first = min(unused)
        group = tuple(sorted(node for node in unused if (
            node in reachable[first] and first in reachable[node]
        )))
        groups.append(group)
        unused.difference_update(group)
    return tuple(groups)
