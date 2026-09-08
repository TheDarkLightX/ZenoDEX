"""Small, exact host-Boolean swarm problems for advisory local-domain study."""

from __future__ import annotations

from src.tau_composition.models import Contract, RepairMap, Requirement
from src.tau_composition.terms import Term, constant, join, meet, negate, variable

from .models import AgentBlock, SwarmProblem


def _zero_anchor(controls: tuple[str, ...]) -> RepairMap:
    return RepairMap(tuple((control, constant(False)) for control in controls))


def asymmetric_choices() -> SwarmProblem:
    """Two uneven local blocks under ``a&(b|c) | b&c = 0``."""

    a, b, c = map(variable, ("a", "b", "c"))
    controls = ("a", "b", "c")
    contract = Contract("asymmetric_choices", (), controls, (
        Requirement("global", join(meet(a, join(b, c)), meet(b, c))),
    ))
    return SwarmProblem(
        contract,
        (AgentBlock("A", ("a",)), AgentBlock("B", ("b", "c"))),
        _zero_anchor(controls),
    )


def planning_swarm() -> SwarmProblem:
    """The bounded API-change planning case with a readable human environment flag."""

    names = ("breaking", "additive", "upgrade", "shim", "regression", "migration")
    breaking, additive, upgrade, shim, regression, migration = map(variable, names)
    allow_breaking = variable("allow_breaking")
    contract = Contract("api_change_planning", ("allow_breaking",), names, (
        Requirement("single_schema_strategy", meet(breaking, additive)),
        Requirement("single_client_strategy", meet(upgrade, shim)),
        Requirement("breaking_requires_upgrade", meet(breaking, negate(upgrade))),
        Requirement("breaking_requires_migration", meet(breaking, negate(migration))),
        Requirement("additive_requires_regression", meet(additive, negate(regression))),
        Requirement("shim_requires_regression", meet(shim, negate(regression))),
        Requirement("breaking_forbids_shim", meet(breaking, shim)),
        Requirement("upgrade_requires_regression", meet(upgrade, negate(regression))),
        Requirement("human_allows_breaking", meet(negate(allow_breaking), breaking)),
    ))
    anchor = RepairMap((
        ("breaking", constant(False)),
        ("additive", constant(False)),
        ("upgrade", constant(True)),
        ("shim", constant(False)),
        ("regression", constant(True)),
        ("migration", constant(True)),
    ))
    return SwarmProblem(
        contract,
        (
            AgentBlock("schema", names[:2]),
            AgentBlock("client", names[2:4]),
            AgentBlock("verification", names[4:]),
        ),
        anchor,
    )


def _code_pattern(bits: tuple[str, str], code: int) -> Term:
    return meet(*(variable(name) if code & (1 << index) else negate(variable(name))
                  for index, name in enumerate(bits)))


def triangle_choices() -> SwarmProblem:
    """Two two-bit agents whose code pairs have six explicitly allowed choices."""

    left = ("left_low", "left_high")
    right = ("right_low", "right_high")
    controls = left + right
    allowed = frozenset({(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)})
    forbidden = tuple(
        meet(_code_pattern(left, left_code), _code_pattern(right, right_code))
        for left_code in range(4)
        for right_code in range(4)
        if (left_code, right_code) not in allowed
    )
    contract = Contract("triangle_choices", (), controls, (
        Requirement("allowed_code_pair", join(*forbidden)),
    ))
    return SwarmProblem(
        contract,
        (AgentBlock("left", left), AgentBlock("right", right)),
        _zero_anchor(controls),
    )


def balanced_anchor(problem: SwarmProblem) -> RepairMap:
    """Return the known valid ``(1, 1)`` code-pair anchor for triangle choices."""

    if (
        not isinstance(problem, SwarmProblem)
        or problem.contract.name != "triangle_choices"
        or problem.contract.controls != ("left_low", "left_high", "right_low", "right_high")
    ):
        raise ValueError("triangle_problem_required")
    return RepairMap((
        ("left_low", constant(True)),
        ("left_high", constant(False)),
        ("right_low", constant(True)),
        ("right_high", constant(False)),
    ))
