"""Independent complete selector tables for exact representation changes."""

from itertools import product

import pytest

from src.tau_workbench.relation import residuals


def test_all_three_bit_relations_retain_exact_membership() -> None:
    rows = tuple(product((False, True), repeat=3))
    controls = ("a", "b", "c")
    for mask in range(256):
        allowed = frozenset(row for index, row in enumerate(rows) if mask & (1 << index))
        reference, selected = residuals(controls, allowed)
        for row in rows:
            assignment = dict(zip(controls, row, strict=True))
            assert reference.evaluate(assignment) == selected.evaluate(assignment) == (row not in allowed)
        assert len(selected.to_tau()) <= len(reference.to_tau())


@pytest.mark.parametrize("controls,allowed,code", [
    ((), frozenset(), "selector_bit_bound"),
    (("a",) * 13, frozenset(), "selector_bit_bound"),
    (("a", "a"), frozenset(), "selector_names"),
    (("a",), frozenset({(1,)}), "selector_row_shape"),
    (("a",), frozenset({(False, True)}), "selector_row_shape"),
    (("a",), {(False,)}, "selector_row_bound"),
])
def test_selector_profile_rejects_malformed_or_over_budget_inputs(controls, allowed, code) -> None:
    with pytest.raises(ValueError, match=code):
        residuals(controls, allowed)
