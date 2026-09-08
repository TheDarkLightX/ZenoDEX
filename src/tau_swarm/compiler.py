"""Compile exact local choice domains through native Tau universal projection.

The sequential expansion is the standard polyadic-concept construction. Its
application here is symbolic, environment-parametric coordination of disjoint
agent choices. Results confer no permission to execute generated work.
"""

from __future__ import annotations

from src.tau_composition.anchor import AnchorCompiler
from src.tau_composition.compiler import _projection_term
from src.tau_composition.resources import bounded_substitute, check_terms
from src.tau_composition.runtime import TauQueryError, TauRuntime
from src.tau_composition.terms import Term, join, negate, variable, xor

from .models import AgentDomain, AutonomyEnvelope, SwarmProblem


def _symbols(problem: SwarmProblem) -> dict[str, str]:
    names = problem.contract.environment + problem.contract.controls
    return {name: f"v{index}" for index, name in enumerate(names)}


def _equation(term: Term, symbols: dict[str, str]) -> str:
    check_terms((term,))
    typed = {name: f"{symbol}:sbf" for name, symbol in symbols.items()}
    return f"({term.to_tau(typed)} = 0:sbf)"


def _all(names: tuple[str, ...], body: str, symbols: dict[str, str]) -> str:
    if not names:
        return body
    binders = ", ".join(f"{symbols[name]}:sbf" for name in names)
    return f"all {binders} ({body})"


def _cofactor(problem: SwarmProblem, domains: tuple[AgentDomain, ...], index: int) -> str:
    """All choices admitted to other agents must be compatible with our choice."""
    symbols = _symbols(problem)
    own = frozenset(problem.blocks[index].controls)
    other_names = tuple(name for name in problem.contract.controls if name not in own)
    others = join(*(domain.residual for j, domain in enumerate(domains) if j != index))
    global_residual = problem.contract.residual
    check_terms((others, global_residual))
    implication = f"({_equation(others, symbols)} -> {_equation(global_residual, symbols)})"
    return _all(other_names, implication, symbols)


def _equivalence(problem: SwarmProblem, index: int, residual: Term, formula: str) -> str:
    symbols = _symbols(problem)
    free = problem.contract.environment + problem.blocks[index].controls
    return _all(free, f"({_equation(residual, symbols)} <-> ({formula}))", symbols)


def _order(problem: SwarmProblem, order: tuple[str, ...] | None) -> tuple[str, ...]:
    names = tuple(block.name for block in problem.blocks)
    if order is None:
        return names
    if (type(order) is not tuple or any(type(name) is not str for name in order)
            or len(order) != len(names) or set(order) != set(names)):
        raise ValueError("expansion_order_permutation")
    return order


class AutonomyCompiler:
    """One exact sequential sweep, with independent native final obligations."""

    def __init__(self, runtime: TauRuntime) -> None:
        self.runtime = runtime

    def compile(
        self, problem: SwarmProblem, order: tuple[str, ...] | None = None,
    ) -> AutonomyEnvelope:
        if not isinstance(problem, SwarmProblem):
            raise ValueError("swarm_problem_type")
        sequence = _order(problem, order)
        start = len(self.runtime.records)
        # This proves a feasible environment-only seed for every environment,
        # rather than obtaining a SAT model that also assigns the environment.
        AnchorCompiler(self.runtime).compile(problem.contract, problem.anchor)
        anchor = problem.anchor.replacements()
        domains = tuple(AgentDomain(block, join(*(
            xor(variable(name), anchor[name]) for name in block.controls
        ))) for block in problem.blocks)
        indices = {block.name: index for index, block in enumerate(problem.blocks)}
        for name in sequence:
            index = indices[name]
            formula = _cofactor(problem, domains, index)
            domain = self._project(problem, index, formula)
            # Commit each expansion before computing the next cofactor. Merging
            # independent expansions of an old snapshot can violate the contract.
            domains = domains[:index] + (domain,) + domains[index + 1:]
        self._check_final(problem, domains)
        return AutonomyEnvelope(
            problem, domains, sequence, len(self.runtime.records) - start,
            self.runtime.binary_sha256,
        )

    def _project(self, problem: SwarmProblem, index: int, formula: str) -> AgentDomain:
        symbols = _symbols(problem)
        block = problem.blocks[index]
        free = frozenset(problem.contract.environment + block.controls)
        # The parser needs only this local projection's possible free names.
        aliases = {symbol: name for name, symbol in symbols.items() if name in free}
        allowed = _projection_term(self.runtime.project(formula), aliases)
        residual = negate(allowed)
        if residual.variables() - free:
            raise TauQueryError("domain_projection_scope")
        if not self.runtime.valid(_equivalence(problem, index, residual, formula)):
            raise TauQueryError("domain_projection_not_equivalent")
        return AgentDomain(block, residual)

    def _check_final(self, problem: SwarmProblem, domains: tuple[AgentDomain, ...]) -> None:
        symbols = _symbols(problem)
        joint = join(*(domain.residual for domain in domains))
        names = problem.contract.environment + problem.contract.controls
        body = f"({_equation(joint, symbols)} -> {_equation(problem.contract.residual, symbols)})"
        if not self.runtime.valid(_all(names, body, symbols)):
            raise TauQueryError("domain_product_unsafe")
        anchored = bounded_substitute(joint, problem.anchor.replacements())
        if not self.runtime.valid(_all(problem.contract.environment, _equation(anchored, symbols), symbols)):
            raise TauQueryError("domain_anchor_lost")
        for index, domain in enumerate(domains):
            formula = _cofactor(problem, domains, index)
            if not self.runtime.valid(_equivalence(problem, index, domain.residual, formula)):
                raise TauQueryError("domain_not_maximal")
