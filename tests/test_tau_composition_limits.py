"""Host expansion must stop before rendering, evaluation or serialization."""

import pytest

from src.tau_composition.models import RepairMap, compose_maps
from src.tau_composition.terms import meet, negate, variable


def test_repeated_shared_substitution_has_an_expanded_node_budget() -> None:
    # Only one source map and 18 tiny DAG steps; an expanded consumer would
    # otherwise traverse more than half a million occurrences of x.
    x = variable("x")
    repair = RepairMap((("x", meet(x, x)),))
    with pytest.raises(ValueError, match="expression_node_bound"):
        compose_maps((repair,) * 18, ("x",))


def test_composition_depth_is_checked_before_recursive_consumers() -> None:
    repair = RepairMap((("x", negate(variable("x"))),))
    with pytest.raises(ValueError, match="expression_depth_bound"):
        compose_maps((repair,) * 100, ("x",))
