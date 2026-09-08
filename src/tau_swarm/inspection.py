"""Bounded human/LLM explanations of an already compiled choice workspace."""

from itertools import product
from math import prod

from .models import AutonomyEnvelope

MAX_INSPECTION_BITS = 10


def _rows(names: tuple[str, ...]) -> tuple[dict[str, bool], ...]:
    return tuple(dict(zip(names, bits, strict=True))
                 for bits in product((False, True), repeat=len(names)))


def _merge(environment: dict[str, bool], rows: tuple[dict[str, bool], ...]) -> dict[str, bool]:
    return environment | {name: value for row in rows for name, value in row.items()}


def inspect_envelope(envelope: AutonomyEnvelope, environment: dict[str, bool]) -> dict[str, object]:
    """List local choices and concrete witnesses explaining excluded choices.

    Enumeration is an optional small-workspace explanation, not the compiler.
    Larger problems retain symbolic domains and skip this operation explicitly.
    Each exclusion witness uses choices still permitted to all other agents.
    """
    problem = envelope.problem
    if type(environment) is not dict or set(environment) != set(problem.contract.environment):
        raise ValueError("inspection_environment_fields")
    if any(type(value) is not bool for value in environment.values()):
        raise ValueError("exact_boolean_required")
    if len(problem.contract.controls) > MAX_INSPECTION_BITS:
        raise ValueError("inspection_bit_bound")
    choices = tuple(tuple(row for row in _rows(block.controls)
                          if envelope.permits(block.name, environment | row)) for block in problem.blocks)
    if any(not rows for rows in choices):
        raise ValueError("inspection_empty_domain")
    for combination in product(*choices):
        envelope.check_bundle(_merge(environment, combination))
    agents = []
    for index, block in enumerate(problem.blocks):
        exclusions = []
        others = tuple(j for j in range(len(problem.blocks)) if j != index)
        for own in _rows(block.controls):
            if envelope.permits(block.name, environment | own):
                continue
            witness = _exclusion_witness(envelope, environment, own, tuple(choices[j] for j in others))
            exclusions.append(witness)
        agents.append({
            "agent": block.name, "controls": list(block.controls),
            "choices": list(choices[index]), "choice_count": len(choices[index]),
            "excluded_choices": exclusions,
        })
    global_count = sum(problem.contract.satisfied(environment | row) for row in _rows(problem.contract.controls))
    return {
        "schema": "tau-swarm/inspection-v1", "authority": "NONE",
        "envelope_id": envelope.subject_id, "environment": dict(environment),
        "independent_combinations": prod(len(rows) for rows in choices),
        "all_globally_feasible_combinations": global_count,
        "agents": agents,
        "scope": "exact Boolean planning choices; no claim about generated work, authorization or performance",
    }


def _exclusion_witness(
    envelope: AutonomyEnvelope, environment: dict[str, bool], own: dict[str, bool],
    other_choices: tuple[tuple[dict[str, bool], ...], ...],
) -> dict[str, object]:
    for combination in product(*other_choices):
        proposed = _merge(environment | own, combination)
        violated = [item.name for item in envelope.problem.contract.requirements
                    if item.residual.evaluate(proposed)]
        if violated:
            return {"choice": dict(own), "conflicting_joint_choice": proposed, "violated_requirements": violated}
    # This also checks the maximality correspondence on the inspected slice.
    raise ValueError("inspection_missing_exclusion_witness")
