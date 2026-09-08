"""Independent host-domain obligations for immutable Tau swarm models."""

from __future__ import annotations

from dataclasses import FrozenInstanceError
from itertools import product
from typing import cast

import pytest

from src.tau_composition.models import RepairMap
from src.tau_composition.terms import constant, variable
from src.tau_swarm.examples import (
    asymmetric_choices,
    balanced_anchor,
    planning_swarm,
    triangle_choices,
)
from src.tau_swarm.models import (
    AgentBlock,
    AgentDomain,
    AutonomyEnvelope,
    LocalChoice,
    SwarmProblem,
)


def _values(names: tuple[str, ...]):
    for bits in product((False, True), repeat=len(names)):
        yield dict(zip(names, bits, strict=True))


def _envelope(
    problem: SwarmProblem,
    domains: tuple[AgentDomain, ...],
    *,
    order: tuple[str, ...] | None = None,
    native_queries: int = 0,
    binary_sha256: str = "host-only",
) -> AutonomyEnvelope:
    return AutonomyEnvelope(
        problem=problem,
        domains=domains,
        expansion_order=order or tuple(block.name for block in problem.blocks),
        native_queries=native_queries,
        binary_sha256=binary_sha256,
    )


def test_agent_blocks_and_problem_partition_are_owned_and_fail_closed() -> None:
    problem = asymmetric_choices()

    assert problem.block("A").controls == ("a",)
    assert problem.block("B").controls == ("b", "c")
    frozen_field = "blocks"
    with pytest.raises(FrozenInstanceError):
        setattr(problem, frozen_field, ())
    with pytest.raises(ValueError, match="unknown_agent_block"):
        problem.block("missing")
    with pytest.raises(ValueError, match="agent_block_controls_required"):
        AgentBlock("A", cast(tuple[str, ...], ["a"]))
    with pytest.raises(ValueError, match="duplicate_agent_control"):
        AgentBlock("A", ("a", "a"))
    with pytest.raises(ValueError, match="block_control_partition"):
        SwarmProblem(
            problem.contract,
            (AgentBlock("A", ("a",)), AgentBlock("B", ("b",))),
            problem.anchor,
        )
    with pytest.raises(ValueError, match="block_control_overlap"):
        SwarmProblem(
            problem.contract,
            (AgentBlock("A", ("a", "b")), AgentBlock("B", ("b", "c"))),
            problem.anchor,
        )
    with pytest.raises(ValueError, match="anchor_control_coverage"):
        SwarmProblem(
            problem.contract,
            problem.blocks,
            RepairMap((("b", constant(False)), ("a", constant(False)), ("c", constant(False)))),
        )
    with pytest.raises(ValueError, match="anchor_reads_non_environment"):
        SwarmProblem(
            problem.contract,
            problem.blocks,
            RepairMap((("a", variable("a")), ("b", constant(False)), ("c", constant(False)))),
        )


def test_envelope_rejects_cross_block_scope_leaks_and_bad_order() -> None:
    problem = asymmetric_choices()
    with pytest.raises(ValueError, match="domain_scope_leak"):
        _envelope(
            problem,
            (AgentDomain(problem.block("A"), variable("b")), AgentDomain(problem.block("B"), constant(False))),
        )
    with pytest.raises(ValueError, match="expansion_order_permutation"):
        AutonomyEnvelope(
            problem,
            (AgentDomain(problem.block("A"), constant(False)), AgentDomain(problem.block("B"), constant(False))),
            ("A", "A"),
            0,
            "host-only",
        )


def test_local_permits_requires_exact_booleans_and_local_coordinates() -> None:
    problem = asymmetric_choices()
    envelope = _envelope(
        problem,
        (AgentDomain(problem.block("A"), variable("a")), AgentDomain(problem.block("B"), constant(False))),
    )

    assert envelope.local_contract("A").controls == ("a",)
    assert envelope.permits("A", {"a": False}) is True
    assert envelope.permits("A", {"a": True}) is False
    with pytest.raises(ValueError, match="exact_boolean_required"):
        envelope.permits("A", {"a": cast(bool, 1)})
    with pytest.raises(ValueError, match="coordinate_set_mismatch"):
        envelope.permits("A", {"a": False, "b": False})


def test_bundle_rejection_is_immutable_and_checks_domains_before_global_contract() -> None:
    problem = asymmetric_choices()
    restricted = _envelope(
        problem,
        (AgentDomain(problem.block("A"), variable("a")), AgentDomain(problem.block("B"), constant(False))),
    )
    locally_forbidden = {"a": True, "b": False, "c": False}
    before_local = dict(locally_forbidden)
    with pytest.raises(ValueError, match="outside_agent_domain"):
        restricted.check_bundle(locally_forbidden)
    assert locally_forbidden == before_local

    permissive = _envelope(
        problem,
        (AgentDomain(problem.block("A"), constant(False)), AgentDomain(problem.block("B"), constant(False))),
    )
    globally_forbidden = {"a": True, "b": True, "c": False}
    before_global = dict(globally_forbidden)
    with pytest.raises(ValueError, match="global_contract_rejected"):
        permissive.check_bundle(globally_forbidden)
    assert globally_forbidden == before_global
    valid_bundle = {"a": False, "b": False, "c": False}
    accepted = permissive.check_bundle(valid_bundle)
    assert accepted == {"a": False, "b": False, "c": False}
    accepted["a"] = True
    assert valid_bundle == {"a": False, "b": False, "c": False}


def test_local_choice_binds_a_permitted_value_to_the_semantic_snapshot() -> None:
    problem = asymmetric_choices()
    domains = (
        AgentDomain(problem.block("A"), variable("a")),
        AgentDomain(problem.block("B"), constant(False)),
    )
    envelope = _envelope(problem, domains)
    replayed = _envelope(problem, domains, native_queries=9, binary_sha256="different-binary")
    reordered = _envelope(problem, domains, order=("B", "A"))
    widened = _envelope(
        problem,
        (AgentDomain(problem.block("A"), constant(False)), domains[1]),
    )
    alternate_anchor_problem = SwarmProblem(
        problem.contract,
        problem.blocks,
        RepairMap((("a", constant(False)), ("b", constant(True)), ("c", constant(False)))),
    )
    alternate_anchor = _envelope(
        alternate_anchor_problem,
        (
            AgentDomain(alternate_anchor_problem.block("A"), variable("a")),
            AgentDomain(alternate_anchor_problem.block("B"), constant(False)),
        ),
    )

    assert envelope.subject_id == replayed.subject_id
    assert envelope.subject_id != reordered.subject_id
    assert envelope.subject_id != widened.subject_id
    assert envelope.subject_id != alternate_anchor.subject_id
    assert len(envelope.subject_id) == 64
    source = {"a": False}
    choice = envelope.choose("A", source)
    assert choice == LocalChoice("A", (), (("a", False),), envelope.subject_id)
    assert source == {"a": False}
    with pytest.raises(ValueError, match="outside_agent_domain"):
        envelope.choose("A", {"a": True})
    with pytest.raises(ValueError, match="exact_boolean_required"):
        envelope.choose("A", {"a": cast(bool, 1)})


def test_choice_aggregation_rechecks_snapshot_owner_fields_and_local_guard() -> None:
    problem = asymmetric_choices()
    domains = (
        AgentDomain(problem.block("A"), variable("a")),
        AgentDomain(problem.block("B"), constant(False)),
    )
    envelope = _envelope(problem, domains)
    choice_a = envelope.choose("A", {"a": False})
    choice_b = envelope.choose("B", {"b": False, "c": False})

    combined = envelope.combine_choices((choice_a, choice_b))
    assert combined == {"a": False, "b": False, "c": False}
    combined["a"] = True
    assert choice_a.controls == (("a", False),)
    with pytest.raises(ValueError, match="ordered_local_choices_required"):
        envelope.combine_choices((choice_a,))
    with pytest.raises(ValueError, match="choice_owner_order"):
        envelope.combine_choices((choice_b, choice_a))
    with pytest.raises(ValueError, match="outside_agent_domain"):
        envelope.combine_choices((
            LocalChoice("A", (), (("a", True),), envelope.subject_id),
            choice_b,
        ))
    with pytest.raises(ValueError, match="choice_controls_mismatch"):
        envelope.combine_choices((
            choice_a,
            LocalChoice("B", (), (("c", False), ("b", False)), envelope.subject_id),
        ))
    with pytest.raises(ValueError, match="local_choice_value_bool"):
        LocalChoice("A", (), (("a", cast(bool, 1)),), envelope.subject_id)


def test_choice_aggregation_rejects_mixed_environment_and_other_snapshot() -> None:
    asymmetric = asymmetric_choices()
    domains = (
        AgentDomain(asymmetric.block("A"), variable("a")),
        AgentDomain(asymmetric.block("B"), constant(False)),
    )
    envelope = _envelope(asymmetric, domains)
    reordered = _envelope(asymmetric, domains, order=("B", "A"))
    with pytest.raises(ValueError, match="choice_subject_mismatch"):
        envelope.combine_choices((
            reordered.choose("A", {"a": False}),
            reordered.choose("B", {"b": False, "c": False}),
        ))

    planning = planning_swarm()
    planning_envelope = _envelope(
        planning,
        tuple(AgentDomain(block, constant(False)) for block in planning.blocks),
    )
    schema = planning_envelope.choose(
        "schema", {"allow_breaking": False, "breaking": False, "additive": False},
    )
    client = planning_envelope.choose(
        "client", {"allow_breaking": True, "upgrade": False, "shim": False},
    )
    verification = planning_envelope.choose(
        "verification", {"allow_breaking": False, "regression": False, "migration": False},
    )
    with pytest.raises(ValueError, match="choice_environment_mismatch"):
        planning_envelope.combine_choices((schema, client, verification))


def test_examples_match_independent_truth_oracles_for_every_small_host_assignment() -> None:
    asymmetric = asymmetric_choices()
    for values in _values(asymmetric.contract.controls):
        expected = not ((values["a"] and (values["b"] or values["c"])) or (values["b"] and values["c"]))
        assert asymmetric.contract.satisfied(values) is expected
        assert asymmetric.contract.satisfied(asymmetric.anchor.apply(values)) is True

    planning = planning_swarm()
    assert tuple(requirement.name for requirement in planning.contract.requirements) == (
        "single_schema_strategy",
        "single_client_strategy",
        "breaking_requires_upgrade",
        "breaking_requires_migration",
        "additive_requires_regression",
        "shim_requires_regression",
        "breaking_forbids_shim",
        "upgrade_requires_regression",
        "human_allows_breaking",
    )
    names = planning.contract.environment + planning.contract.controls
    for values in _values(names):
        breaking, additive = values["breaking"], values["additive"]
        upgrade, shim = values["upgrade"], values["shim"]
        regression, migration = values["regression"], values["migration"]
        forbidden = (
            (breaking and additive)
            or (upgrade and shim)
            or (breaking and not upgrade)
            or (breaking and not migration)
            or (additive and not regression)
            or (shim and not regression)
            or (breaking and shim)
            or (upgrade and not regression)
            or (not values["allow_breaking"] and breaking)
        )
        assert planning.contract.satisfied(values) is (not forbidden)
        assert planning.contract.satisfied(planning.anchor.apply(values)) is True

    triangle = triangle_choices()
    allowed = {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)}
    for values in _values(triangle.contract.controls):
        left = int(values["left_low"]) + 2 * int(values["left_high"])
        right = int(values["right_low"]) + 2 * int(values["right_high"])
        assert triangle.contract.satisfied(values) is ((left, right) in allowed)
        assert triangle.contract.satisfied(triangle.anchor.apply(values)) is True
        balanced = balanced_anchor(triangle).apply(values)
        assert balanced == {
            "left_low": True,
            "left_high": False,
            "right_low": True,
            "right_high": False,
        }
        assert triangle.contract.satisfied(balanced) is True
