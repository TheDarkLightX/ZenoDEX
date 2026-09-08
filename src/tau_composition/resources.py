"""Bound expanded trees before recursive consumers traverse shared terms."""

from collections.abc import Mapping

from .terms import Term

MAX_EXPRESSION_NODES = 16_384
MAX_EXPRESSION_DEPTH = 96
MAX_EXPRESSION_JSON_BYTES = 1_000_000


class ExpressionBudgetError(ValueError):
    """An application representation limit, with no logical verdict."""


def check_terms(terms: tuple[Term, ...]) -> None:
    """Count expanded occurrences using bounded work on shared object identities.

    Reusing a child twice costs twice its tree size, even though the object is
    shared. This checks the size consumed by rendering/JSON/evaluation without
    first expanding it. Maximum depth includes the root as one level.
    """
    sizes: dict[int, tuple[int, int, int]] = {}
    for root in terms:
        pending = [(root, False)]
        active: set[int] = set()
        while pending:
            term, visited = pending.pop()
            key = id(term)
            if key in sizes:
                continue
            if not visited:
                if key in active:
                    raise ExpressionBudgetError("expression_cycle")
                if len(term.operands) > MAX_EXPRESSION_NODES:
                    raise ExpressionBudgetError("expression_node_bound")
                active.add(key)
                pending.append((term, True))
                pending.extend((child, False) for child in reversed(term.operands))
                continue
            active.remove(key)
            child_sizes = tuple(sizes[id(child)] for child in term.operands)
            nodes = 1 + sum(size[0] for size in child_sizes)
            depth = 1 + max((size[1] for size in child_sizes), default=0)
            if child_sizes:
                overhead = len('{"kind":"' + term.kind + '","operands":[]}')
                encoded = overhead + len(child_sizes) - 1 + sum(size[2] for size in child_sizes)
            else:
                encoded = len(term.canonical_json().encode("utf-8"))
            _check_size(nodes, depth, encoded)
            sizes[key] = (nodes, depth, encoded)
    _check_size(sum(sizes[id(t)][0] for t in terms),
                max((sizes[id(t)][1] for t in terms), default=0),
                sum(sizes[id(t)][2] for t in terms))


def _check_size(nodes: int, depth: int, encoded: int) -> None:
    if nodes > MAX_EXPRESSION_NODES:
        raise ExpressionBudgetError("expression_node_bound")
    if depth > MAX_EXPRESSION_DEPTH:
        raise ExpressionBudgetError("expression_depth_bound")
    if encoded > MAX_EXPRESSION_JSON_BYTES:
        raise ExpressionBudgetError("expression_byte_bound")


def bounded_substitute(term: Term, mapping: Mapping[str, Term]) -> Term:
    check_terms((term, *mapping.values()))
    result = term.substitute(mapping)
    check_terms((result,))
    return result
