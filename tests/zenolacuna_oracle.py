"""Grade-3 oracle: enumerate complete question trees, then evaluate their paths.

No production imports, semantic helper reuse, dynamic programming, or memoization.
The explicit tree representation deliberately trades speed for independence.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterator


@dataclass(frozen=True)
class OracleQuestion:
    name: str
    cost: int
    answers: tuple[str, ...]


@dataclass(frozen=True)
class Leaf:
    interpretation: int


@dataclass(frozen=True)
class Branch:
    question: OracleQuestion
    children: tuple[tuple[str, Leaf | Branch], ...]


def complete_trees(
    interpretations: tuple[int, ...], questions: tuple[OracleQuestion, ...]
) -> Iterator[Leaf | Branch]:
    if len(interpretations) == 1:
        yield Leaf(interpretations[0])
        return
    for question in questions:
        tokens = sorted({question.answers[i] for i in interpretations})
        if len(tokens) < 2:
            continue
        remaining = tuple(q for q in questions if q.name != question.name)
        subtrees = []
        for token in tokens:
            compatible = tuple(i for i in interpretations if question.answers[i] == token)
            subtrees.append(tuple(complete_trees(compatible, remaining)))
        for children in product(*subtrees):
            yield Branch(question, tuple(zip(tokens, children, strict=True)))


def path_cost(tree: Leaf | Branch, interpretation: int) -> int:
    cost = 0
    while isinstance(tree, Branch):
        cost += tree.question.cost
        token = tree.question.answers[interpretation]
        tree = dict(tree.children)[token]
    if tree.interpretation != interpretation:
        raise ValueError("Tree terminates at the wrong interpretation")
    return cost


def optimal_tree(
    count: int, questions: tuple[OracleQuestion, ...]
) -> tuple[int | None, str | None]:
    if not 1 <= count <= 5 or len(questions) > 5:
        raise ValueError("Independent oracle is limited to five classes and questions")
    interpretations = tuple(range(count))
    ranked = []
    for tree in complete_trees(interpretations, questions):
        cost = max(path_cost(tree, i) for i in interpretations)
        ranked.append((cost, tree.question.name if isinstance(tree, Branch) else ""))
    if not ranked:
        return None, None
    cost, name = min(ranked)
    return cost, name or None
