"""Independent explanations of formal autonomy limits for a human and swarm."""

from itertools import product

import pytest

from src.tau_composition.models import Contract, RepairMap, Requirement
from src.tau_composition.terms import constant, join, variable
from src.tau_swarm.examples import asymmetric_choices
from src.tau_swarm.inspection import inspect_envelope
from src.tau_swarm.models import AgentBlock, AgentDomain, AutonomyEnvelope, SwarmProblem


def _asymmetric(a_residual=None, b_residual=None):
    problem = asymmetric_choices()
    residuals = (constant(False) if a_residual is None else a_residual,
                 join(variable("b"), variable("c")) if b_residual is None else b_residual)
    domains = tuple(AgentDomain(block, term) for block, term in zip(problem.blocks, residuals, strict=True))
    return AutonomyEnvelope(problem, domains, ("A", "B"), 0, "advisory_test_data")


def test_human_gets_concrete_conflicts_for_every_excluded_agent_choice() -> None:
    result = inspect_envelope(_asymmetric(), {})
    assert result["authority"] == "NONE"
    assert result["independent_combinations"] == 2
    assert result["all_globally_feasible_combinations"] == 4
    a, b = result["agents"]
    assert a["choices"] == [{"a": False}, {"a": True}]
    assert b["choices"] == [{"b": False, "c": False}]
    assert a["excluded_choices"] == []
    excluded = b["excluded_choices"]
    assert len(excluded) == 3
    for item in excluded:
        row = item["conflicting_joint_choice"]
        assert {name: row[name] for name in ("b", "c")} == item["choice"]
        assert {"a": row["a"]} in a["choices"]
        assert (row["a"] and (row["b"] or row["c"])) or (row["b"] and row["c"])
        assert item["violated_requirements"] == ["global"]
    # Exclusion from this product does not mean globally infeasible.
    assert any(not (False and (b or c)) and not (b and c)
               for b, c in product((False, True), repeat=2) if b or c)


def test_explanations_recheck_safety_and_maximality_of_uncredentialed_envelopes() -> None:
    with pytest.raises(ValueError, match="global_contract_rejected"):
        inspect_envelope(_asymmetric(b_residual=constant(False)), {})
    with pytest.raises(ValueError, match="inspection_missing_exclusion_witness"):
        inspect_envelope(_asymmetric(a_residual=variable("a")), {})
    with pytest.raises(ValueError, match="inspection_empty_domain"):
        inspect_envelope(_asymmetric(a_residual=constant(True)), {})


@pytest.mark.parametrize("environment", [None, [], (), "", {"unexpected": False}])
def test_invalid_environment_shape_is_a_typed_rejection(environment) -> None:
    with pytest.raises(ValueError, match="inspection_environment_fields"):
        inspect_envelope(_asymmetric(), environment)


def test_inspection_bound_rejects_before_exponential_enumeration() -> None:
    names = tuple(f"x{i}" for i in range(11))
    contract = Contract("large", (), names, (Requirement("zero", constant(False)),))
    block = AgentBlock("agent", names)
    problem = SwarmProblem(contract, (block,), RepairMap(tuple((name, constant(False)) for name in names)))
    envelope = AutonomyEnvelope(problem, (AgentDomain(block, constant(False)),), ("agent",), 0, "test")
    with pytest.raises(ValueError, match="inspection_bit_bound"):
        inspect_envelope(envelope, {})
