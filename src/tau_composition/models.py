"""Immutable application contracts and proposal maps; these confer no authority."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

from .resources import check_terms
from .terms import Term, constant, join, variable


@dataclass(frozen=True, slots=True)
class Requirement:
    """A named Boolean equation: ``residual = 0``."""

    name: str
    residual: Term

    def __post_init__(self) -> None:
        variable(self.name)
        if not isinstance(self.residual, Term):
            raise ValueError("requirement_term_required")
        check_terms((self.residual,))


@dataclass(frozen=True, slots=True)
class Contract:
    """Environment is read-only; only declared proposal coordinates may change.

    The executable application domain is exact host booleans. Native Boolean
    algebra identities are additionally checked by Tau. Arithmetic, temporal
    liveness, signatures, custody and finality require separate contracts.
    """

    name: str
    environment: tuple[str, ...]
    controls: tuple[str, ...]
    requirements: tuple[Requirement, ...]

    def __post_init__(self) -> None:
        variable(self.name)
        collections = (self.environment, self.controls, self.requirements)
        if any(type(item) is not tuple for item in collections):
            raise ValueError("owned_tuples_required")
        names = self.environment + self.controls
        if not self.controls or len(names) > 256:
            raise ValueError("contract_coordinate_bound")
        for name in names:
            variable(name)
        if len(set(names)) != len(names):
            raise ValueError("duplicate_coordinate")
        self._check_requirements(frozenset(names))

    def _check_requirements(self, names: frozenset[str]) -> None:
        if not self.requirements or len(self.requirements) > 128:
            raise ValueError("contract_requirement_bound")
        if any(not isinstance(item, Requirement) for item in self.requirements):
            raise ValueError("requirement_type")
        check_terms((self.residual,))
        labels = tuple(item.name for item in self.requirements)
        if len(set(labels)) != len(labels):
            raise ValueError("duplicate_requirement")
        if any(item.residual.variables() - names for item in self.requirements):
            raise ValueError("undeclared_coordinate")

    @property
    def residual(self) -> Term:
        return join(*(item.residual for item in self.requirements))

    def validate_values(self, values: Mapping[str, bool]) -> None:
        if set(values) != set(self.environment + self.controls):
            raise ValueError("coordinate_set_mismatch")
        if any(type(value) is not bool for value in values.values()):
            raise ValueError("exact_boolean_required")

    def satisfied(self, values: Mapping[str, bool]) -> bool:
        self.validate_values(values)
        return not self.residual.evaluate(values)


@dataclass(frozen=True, slots=True)
class RepairMap:
    """Simultaneous replacements for proposal coordinates, never a permission."""

    assignments: tuple[tuple[str, Term], ...]

    def __post_init__(self) -> None:
        if type(self.assignments) is not tuple:
            raise ValueError("owned_assignments_required")
        names = []
        for item in self.assignments:
            if type(item) is not tuple or len(item) != 2:
                raise ValueError("assignment_shape")
            name, term = item
            variable(name)
            if not isinstance(term, Term):
                raise ValueError("assignment_term")
            names.append(name)
        if len(set(names)) != len(names):
            raise ValueError("duplicate_assignment")
        check_terms(tuple(term for _, term in self.assignments))

    def replacements(self) -> dict[str, Term]:
        return dict(self.assignments)

    def apply(self, values: Mapping[str, bool]) -> dict[str, bool]:
        if any(type(value) is not bool for value in values.values()):
            raise ValueError("exact_boolean_required")
        if set(self.replacements()) - set(values):
            raise ValueError("missing_proposal_coordinate")
        result = dict(values)
        result.update((name, term.evaluate(values)) for name, term in self.assignments)
        return result


def compose_maps(maps: tuple[RepairMap, ...], controls: tuple[str, ...]) -> RepairMap:
    """Apply maps from left to right, with simultaneous substitution at each step."""
    current = {name: variable(name) for name in controls}
    for repair in maps:
        if set(repair.replacements()) - set(controls):
            raise ValueError("repair_writes_environment")
        updates = {name: term.substitute(current) for name, term in repair.assignments}
        current.update(updates)
        check_terms(tuple(current.values()))
    return RepairMap(tuple((name, current[name]) for name in controls))


def empty_repair() -> RepairMap:
    return RepairMap(())


def tautology_contract(name: str, controls: tuple[str, ...]) -> Contract:
    return Contract(name, (), controls, (Requirement("unrestricted", constant(False)),))
