"""Bounded exact Shannon factoring for finite selector relations.

This applies classical Boolean decomposition, with exhaustive local parity.
It changes representation, not the accepted relation or Tau's decision procedure.
"""

from __future__ import annotations

from itertools import product

from src.tau_composition.terms import Term, constant, join, meet, negate, variable

MAX_SELECTOR_BITS = 12


def residuals(
    controls: tuple[str, ...], allowed: frozenset[tuple[bool, ...]],
) -> tuple[Term, Term]:
    """Return enumerated and selected residuals, both zero exactly on allowed rows."""
    _check_relation(controls, allowed)
    enumerated = negate(join(*(meet(*(variable(name) if value else negate(variable(name))
                                     for name, value in zip(controls, row, strict=True)))
                               for row in sorted(allowed))))
    rows = tuple(product((False, True), repeat=len(controls)))
    values = tuple(row not in allowed for row in rows)
    factored = _factor(controls, 0, values, {})
    selected = min((enumerated, factored), key=lambda term: len(term.to_tau().encode("utf-8")))
    for row, expected in zip(rows, values, strict=True):
        assignment = dict(zip(controls, row, strict=True))
        if selected.evaluate(assignment) != expected:
            raise ValueError("selector_factoring_disagreement")
    return enumerated, selected


def _check_relation(controls: tuple[str, ...], allowed: frozenset[tuple[bool, ...]]) -> None:
    if type(controls) is not tuple or not 1 <= len(controls) <= MAX_SELECTOR_BITS:
        raise ValueError("selector_bit_bound")
    for name in controls:
        variable(name)
    if len(set(controls)) != len(controls):
        raise ValueError("selector_names")
    if type(allowed) is not frozenset or len(allowed) > 1 << len(controls):
        raise ValueError("selector_row_bound")
    for row in allowed:
        if type(row) is not tuple or len(row) != len(controls) or any(type(v) is not bool for v in row):
            raise ValueError("selector_row_shape")


def _factor(
    controls: tuple[str, ...], index: int, values: tuple[bool, ...],
    cache: dict[tuple[int, tuple[bool, ...]], Term],
) -> Term:
    key = index, values
    if key in cache:
        return cache[key]
    if all(value == values[0] for value in values):
        result = constant(values[0])
    else:
        middle = len(values) // 2
        low = _factor(controls, index + 1, values[:middle], cache)
        high = _factor(controls, index + 1, values[middle:], cache)
        symbol = variable(controls[index])
        result = low if low == high else join(meet(negate(symbol), low), meet(symbol, high))
    cache[key] = result
    return result
