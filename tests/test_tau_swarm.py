"""Independent finite relation oracles for native swarm-domain compilation."""

import os
from itertools import product

import pytest

from src.tau_composition.models import Contract, RepairMap, Requirement
from src.tau_composition.runtime import TauQueryError, TauRuntime
from src.tau_composition.terms import constant, variable
from src.tau_swarm.compiler import AutonomyCompiler
from src.tau_swarm.examples import (
    asymmetric_choices,
    balanced_anchor,
    planning_swarm,
    triangle_choices,
)
from src.tau_swarm.models import AgentBlock, AutonomyEnvelope, SwarmProblem


@pytest.fixture
def native() -> TauRuntime:
    binary = os.environ.get("TAU_COMPOSITION_BIN")
    if not binary:
        pytest.skip("explicit native Tau binary required")
    return TauRuntime(binary, timeout_seconds=5)


def _rows(names):
    return tuple(dict(zip(names, bits, strict=True)) for bits in product((False, True), repeat=len(names)))


def _oracle(envelope: AutonomyEnvelope, environment: dict[str, bool], legal) -> int:
    """Construct all local alternatives and test exact cofactors independently."""
    blocks = envelope.problem.blocks
    choices = tuple(tuple(row for row in _rows(block.controls)
                          if envelope.permits(block.name, environment | row)) for block in blocks)
    assert all(choices)
    count = 0
    for local in product(*choices):
        values = environment | {name: bit for row in local for name, bit in row.items()}
        before = dict(values)
        assert legal(values)
        assert envelope.check_bundle(values) == values
        issued = tuple(envelope.choose(block.name, environment | row)
                       for block, row in zip(blocks, local, strict=True))
        assert envelope.combine_choices(issued) == values
        assert values == before
        count += 1
    for index, block in enumerate(blocks):
        other = tuple(j for j in range(len(blocks)) if j != index)
        for own in _rows(block.controls):
            compatible = all(legal(environment | own | {
                name: bit for row in others for name, bit in row.items()
            }) for others in product(*(choices[j] for j in other)))
            assert envelope.permits(block.name, environment | own) == compatible
    return count


def _planning_legal(v):
    return (
        not (v["breaking"] and v["additive"])
        and not (v["upgrade"] and v["shim"])
        and (not v["breaking"] or (v["allow_breaking"] and v["upgrade"] and v["migration"] and not v["shim"]))
        and (not (v["additive"] or v["shim"] or v["upgrade"]) or v["regression"])
    )


def test_human_priority_changes_which_agent_alternatives_survive(native: TauRuntime) -> None:
    compiler = AutonomyCompiler(native)
    problem = planning_swarm()
    schema_first = compiler.compile(problem, ("schema", "client", "verification"))
    verification_first = compiler.compile(problem, ("verification", "client", "schema"))
    assert _oracle(schema_first, {"allow_breaking": True}, _planning_legal) == 3
    assert _oracle(verification_first, {"allow_breaking": True}, _planning_legal) == 12
    assert _oracle(schema_first, {"allow_breaking": False}, _planning_legal) == 12
    assert _oracle(verification_first, {"allow_breaking": False}, _planning_legal) == 12
    assert schema_first.permits("schema", {"allow_breaking": True, "breaking": True, "additive": False})
    assert not verification_first.permits("schema", {"allow_breaking": True, "breaking": True, "additive": False})


def test_searching_every_order_can_miss_a_larger_product(native: TauRuntime) -> None:
    problem = triangle_choices()
    allowed = {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)}

    def legal(v):
        return (int(v["left_low"]) + 2 * int(v["left_high"]),
                int(v["right_low"]) + 2 * int(v["right_high"])) in allowed

    compiler = AutonomyCompiler(native)
    for order in (("left", "right"), ("right", "left")):
        assert _oracle(compiler.compile(problem, order), {}, legal) == 3
    balanced = SwarmProblem(problem.contract, problem.blocks, balanced_anchor(problem))
    assert _oracle(compiler.compile(balanced), {}, legal) == 4


def test_individually_feasible_or_stale_parallel_expansions_are_unsafe() -> None:
    # Every choice of A and each of these B choices has a compatible counterpart.
    # Independent existential projections or stale full expansions admit six
    # combinations; the exact joint relation admits four.
    a_choices = (False, True)
    b_choices = ((False, False), (False, True), (True, False))
    def legal(a, b, c):
        return not (a and (b or c)) and not (b and c)
    combinations = [(a, b, c) for a in a_choices for b, c in b_choices]
    assert len(combinations) == 6
    assert [row for row in combinations if not legal(*row)] == [(True, False, True), (True, True, False)]


def test_projection_mutant_cannot_issue_an_unsafe_or_inexact_envelope(native: TauRuntime, monkeypatch) -> None:
    monkeypatch.setattr(native, "project", lambda _query: "T")
    with pytest.raises(TauQueryError, match="domain_projection_not_equivalent"):
        AutonomyCompiler(native).compile(asymmetric_choices())


def test_unknown_projection_and_invalid_order_never_produce_an_envelope(native: TauRuntime, monkeypatch) -> None:
    compiler = AutonomyCompiler(native)
    with pytest.raises(ValueError, match="expansion_order_permutation"):
        compiler.compile(asymmetric_choices(), ("A", "A"))
    assert not native.records

    def unavailable(_formula):
        raise TauQueryError("native_timeout")

    monkeypatch.setattr(native, "project", unavailable)
    with pytest.raises(TauQueryError, match="native_timeout"):
        compiler.compile(asymmetric_choices())


def test_small_local_projection_does_not_inherit_global_alias_limit(native: TauRuntime) -> None:
    # Given 65 coordinates but a one-coordinate local condition, symbolic
    # projection needs only that block's aliases. No 2**65 enumeration occurs.
    names = tuple(f"x{i}" for i in range(65))
    problem = SwarmProblem(
        Contract("wide", (), names, (Requirement("first_zero", variable(names[0])),)),
        (AgentBlock("first", names[:1]), AgentBlock("rest", names[1:])),
        RepairMap(tuple((name, constant(False)) for name in names)),
    )
    envelope = AutonomyCompiler(native).compile(problem)
    assert envelope.permits("first", {"x0": False})
    assert not envelope.permits("first", {"x0": True})
    assert envelope.domains[1].residual.variables() == frozenset()
    assert not envelope.domains[1].residual.evaluate({})
    values = dict.fromkeys(names, True) | {"x0": False}
    assert envelope.check_bundle(values) == values
    with pytest.raises(ValueError, match="outside_agent_domain"):
        envelope.check_bundle(dict.fromkeys(names, True))


def test_one_agent_receives_exactly_the_globally_feasible_choices(native: TauRuntime) -> None:
    problem = asymmetric_choices()
    single = SwarmProblem(problem.contract, (AgentBlock("team", problem.contract.controls),), problem.anchor)
    envelope = AutonomyCompiler(native).compile(single)
    for values in _rows(problem.contract.controls):
        legal = not (values["a"] and (values["b"] or values["c"])) and not (values["b"] and values["c"])
        assert envelope.permits("team", values) == legal
        if legal:
            assert envelope.check_bundle(values) == values
        else:
            with pytest.raises(ValueError, match="outside_agent_domain"):
                envelope.check_bundle(values)
