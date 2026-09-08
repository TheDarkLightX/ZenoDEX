"""Native-certified composition of symbolic reproductive proposal maps.

Tau owns LGRS and logical reasoning. This original application schedules and
reuses those results. It does not implement quantifier elimination or a solver.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from .models import Contract, RepairMap, compose_maps
from .resources import bounded_substitute, check_terms
from .runtime import TauQueryError, TauRuntime
from .scheduling import strongly_connected_groups, topological_order
from .terms import Term, constant, join, meet, negate, parse_native_term, variable, xor


def _symbols(names: tuple[str, ...]) -> dict[str, str]:
    return {name: f"v{index}" for index, name in enumerate(names)}


def _typed(symbols: dict[str, str]) -> dict[str, str]:
    return {name: f"{symbol}:sbf" for name, symbol in symbols.items()}


def _quantify(kind: str, names: tuple[str, ...], body: str, symbols: dict[str, str]) -> str:
    if not names:
        return body
    binders = ", ".join(f"{symbols[name]}:sbf" for name in names)
    return f"{kind} {binders} ({body})"


def _equation(term: Term, symbols: dict[str, str]) -> str:
    return f"({term.to_tau(_typed(symbols))} = 0:sbf)"


def _all_equation(term: Term) -> str:
    check_terms((term,))
    names = tuple(sorted(term.variables()))
    symbols = _symbols(names)
    return _quantify("all", names, _equation(term, symbols), symbols)


def _implication(before: Term, after: Term) -> str:
    check_terms((before, after))
    names = tuple(sorted(before.variables() | after.variables()))
    symbols = _symbols(names)
    body = f"({_equation(before, symbols)} -> {_equation(after, symbols)})"
    return _quantify("all", names, body, symbols)


def _solution_map(text: str, aliases: dict[str, str], controls: tuple[str, ...]) -> RepairMap:
    content = text[len("solution: {"):-1].strip()
    result = {}
    for line in content.splitlines():
        match = re.fullmatch(r"\s*([a-z][a-z0-9]*)\s*:=\s*(.+)", line)
        if match is None or match[1] not in aliases:
            raise TauQueryError("native_assignment_shape")
        target = aliases[match[1]]
        if target not in controls or target in result:
            raise TauQueryError("native_assignment_target")
        try:
            result[target] = parse_native_term(match[2], aliases)
        except ValueError as exc:
            raise TauQueryError("native_term_unsupported") from exc
    if set(result) != set(controls):
        raise TauQueryError("native_assignment_coverage")
    return RepairMap(tuple((name, result[name]) for name in controls))


def _projection_term(text: str, aliases: dict[str, str]) -> Term:
    if text in {"T", "F"}:
        return constant(text == "T")
    match = re.fullmatch(r"(.+?)\s*=\s*0(?:\s*:\s*sbf)?", text)
    if match is None:
        raise TauQueryError("projection_fragment_unsupported")
    try:
        return negate(parse_native_term(match[1], aliases))
    except ValueError as exc:
        raise TauQueryError("projection_term_unsupported") from exc


@dataclass(frozen=True, slots=True)
class CompiledRepair:
    contract: Contract
    repair: RepairMap
    groups: tuple[tuple[str, ...], ...]
    dependency_edges: tuple[tuple[int, int], ...]
    schedule: tuple[int, ...]
    merge_rounds: int
    native_queries: int
    cache_hits: int
    binary_sha256: str
    alternative_orders: tuple[tuple[int, ...], ...] = ()
    order_guards: tuple[Term, ...] = ()

    def propose(self, values: dict[str, bool]) -> dict[str, bool]:
        """Return an advisory proposal, rechecking original requirements.

        No input mutation or external effects. Runtime authentication and
        deterministic ZenoDEX validators must still admit any real action.
        """
        self.contract.validate_values(values)
        candidate = self.repair.apply(values)
        if not self.contract.satisfied(candidate):
            raise ValueError("compiled_proposal_failed_contract")
        return candidate


@dataclass(frozen=True, slots=True)
class GuardAnalysis:
    safe_environment: Term
    feasible_environment: Term
    covers_feasible_environment: bool


class RepairCompiler:
    """Session-local content/role-bound reuse; solver failures never certify maps."""

    def __init__(self, runtime: TauRuntime) -> None:
        self.runtime = runtime
        self._repairs: dict[str, RepairMap] = {}
        self._preservation: dict[str, bool] = {}
        self.cache_hits = 0

    def native_repair(self, contract: Contract) -> RepairMap:
        residual = contract.residual
        support = residual.variables()
        environment = tuple(name for name in contract.environment if name in support)
        controls = tuple(name for name in contract.controls if name in support)
        canonical = {name: f"e{index}" for index, name in enumerate(environment)}
        canonical.update((name, f"c{index}") for index, name in enumerate(controls))
        normalized = residual.substitute({name: variable(alias) for name, alias in canonical.items()})
        key = f"{len(environment)}:{len(controls)}:{normalized.sha256()}"
        if key in self._repairs:
            self.cache_hits += 1
            template = self._repairs[key]
        else:
            template = self._compile_template(normalized, len(environment), len(controls))
            self._repairs[key] = template
        reverse = {alias: variable(name) for name, alias in canonical.items()}
        names = {alias: name for name, alias in canonical.items()}
        return RepairMap(tuple((names[name], term.substitute(reverse)) for name, term in template.assignments))

    def _compile_template(self, residual: Term, env_count: int, control_count: int) -> RepairMap:
        environment = tuple(f"e{index}" for index in range(env_count))
        controls = tuple(f"c{index}" for index in range(control_count))
        if env_count > 26:
            raise TauQueryError("coefficient_symbol_bound")
        if residual == constant(False):
            return RepairMap(tuple((name, variable(name)) for name in controls))
        if not controls:
            raise TauQueryError("environment_only_requirement")
        # This binary's SBF coefficient parser requires single-letter atoms.
        symbols = {name: chr(ord("a") + index) for index, name in enumerate(environment)}
        symbols.update((name, f"v{index}") for index, name in enumerate(controls))
        rendering = {name: f"{{{symbols[name]}}}:sbf" for name in environment}
        rendering.update((name, f"{symbols[name]}:sbf") for name in controls)
        equation = f"({residual.to_tau(rendering)} = 0:sbf)"
        text = self.runtime.lgrs(equation)
        repair = _solution_map(text, {alias: name for name, alias in symbols.items()}, controls)
        self._check_reproductive(residual, repair)
        return repair

    def _check_reproductive(self, residual: Term, repair: RepairMap) -> None:
        after = bounded_substitute(residual, repair.replacements())
        if not self.runtime.valid(_all_equation(after)):
            raise TauQueryError("native_map_unsound")
        defect = join(*(xor(variable(name), term) for name, term in repair.assignments))
        if not self.runtime.valid(_implication(residual, defect)):
            raise TauQueryError("native_map_not_reproductive")

    def preserves(self, repair: RepairMap, requirement: Term) -> bool:
        changed = {name for name, term in repair.assignments if term != variable(name)}
        if not changed.intersection(requirement.variables()):
            return True
        after = bounded_substitute(requirement, repair.replacements())
        if after == requirement:
            return True
        query = _implication(requirement, after)
        if query in self._preservation:
            self.cache_hits += 1
            return self._preservation[query]
        try:
            result = self.runtime.valid(query)
        except TauQueryError:
            # Unproved preservation keeps a conservative dependency edge.
            return False
        self._preservation[query] = result
        return result

    def _edges(self, groups: tuple[Contract, ...], repairs: tuple[RepairMap, ...]) -> frozenset[tuple[int, int]]:
        return frozenset(
            (source, target)
            for source, repair in enumerate(repairs)
            for target, group in enumerate(groups)
            if source != target and not self.preserves(repair, group.residual)
        )

    def compile(self, contract: Contract) -> CompiledRepair:
        start_queries, start_hits = len(self.runtime.records), self.cache_hits
        groups = tuple(Contract(contract.name, contract.environment, contract.controls, (item,))
                       for item in contract.requirements)
        rounds = 0
        while True:
            repairs = tuple(self.native_repair(group) for group in groups)
            edges = self._edges(groups, repairs)
            schedule = topological_order(len(groups), edges)
            if schedule is not None:
                break
            partitions = strongly_connected_groups(len(groups), edges)
            if len(partitions) >= len(groups):
                raise TauQueryError("scc_failed_to_reduce")
            groups = tuple(Contract(
                contract.name, contract.environment, contract.controls,
                tuple(item for index in indices for item in groups[index].requirements),
            ) for indices in partitions)
            rounds += 1
        composed = compose_maps(tuple(repairs[index] for index in schedule), contract.controls)
        return CompiledRepair(
            contract, composed, tuple(tuple(item.name for item in group.requirements) for group in groups),
            tuple(sorted(edges)), schedule, rounds,
            len(self.runtime.records) - start_queries, self.cache_hits - start_hits,
            self.runtime.binary_sha256,
        )

    def analyze_order(self, contract: Contract, repair: RepairMap) -> GuardAnalysis:
        """Derive and independently recheck exact guard and feasibility formulas."""
        names = contract.environment + contract.controls
        symbols = _symbols(names)
        aliases = {symbol: name for name, symbol in symbols.items()}
        after = bounded_substitute(contract.residual, repair.replacements())
        guard_query = _quantify("all", contract.controls, _equation(after, symbols), symbols)
        feasible_query = _quantify("ex", contract.controls, _equation(contract.residual, symbols), symbols)
        guard = _projection_term(self.runtime.project(guard_query), aliases)
        feasible = _projection_term(self.runtime.project(feasible_query), aliases)
        for term, query in ((guard, guard_query), (feasible, feasible_query)):
            if term.variables() - set(contract.environment):
                raise TauQueryError("projection_retains_control")
            equivalence = f"(({term.to_tau(_typed(symbols))} = 1:sbf) <-> ({query}))"
            if not self.runtime.valid(_quantify("all", contract.environment, equivalence, symbols)):
                raise TauQueryError("projection_equivalence_failed")
        complete = self.runtime.valid(_all_equation(xor(guard, feasible)))
        return GuardAnalysis(guard, feasible, complete)

    def compile_guarded_cover(
        self, contract: Contract, orders: tuple[tuple[int, ...], ...],
    ) -> CompiledRepair:
        """Glue a bounded set of order maps with orthogonal Boolean coefficients.

        Branching on ``p=0 or p=1`` covers host bool inputs only. The resulting
        polynomial map is separately checked over Tau's Boolean algebra; the
        join of guard terms is never substituted for that soundness check.
        An incomplete or unsound cover fails closed.
        """
        expected = set(range(len(contract.requirements)))
        if type(orders) is not tuple or not 1 <= len(orders) <= 8:
            raise ValueError("order_count_bound")
        for order in orders:
            if (type(order) is not tuple or any(type(i) is not int for i in order)
                    or len(order) != len(expected) or set(order) != expected):
                raise ValueError("order_must_be_full_permutation")
        start_queries, start_hits = len(self.runtime.records), self.cache_hits
        locals_ = tuple(self.native_repair(Contract(
            contract.name, contract.environment, contract.controls, (item,),
        )) for item in contract.requirements)
        maps = tuple(compose_maps(tuple(locals_[i] for i in order), contract.controls) for order in orders)
        guards = tuple(self.analyze_order(contract, repair).safe_environment for repair in maps)
        remaining = constant(True)
        result = {name: constant(False) for name in contract.controls}
        for guard, repair in zip(guards, maps, strict=True):
            coefficient = meet(remaining, guard)
            for name, term in repair.assignments:
                result[name] = join(result[name], meet(coefficient, term))
            remaining = meet(remaining, negate(guard))
        if not self.runtime.valid(_all_equation(remaining)):
            raise TauQueryError("incomplete_order_cover")
        glued = RepairMap(tuple((name, result[name]) for name in contract.controls))
        self._check_reproductive(contract.residual, glued)
        return CompiledRepair(
            contract, glued, tuple((item.name,) for item in contract.requirements),
            (), (), 0, len(self.runtime.records) - start_queries, self.cache_hits - start_hits,
            self.runtime.binary_sha256, orders, guards,
        )


def refines(runtime: TauRuntime, stronger: Contract, weaker: Contract) -> bool:
    if (stronger.environment, stronger.controls) != (weaker.environment, weaker.controls):
        raise ValueError("refinement_roles_mismatch")
    return runtime.valid(_implication(stronger.residual, weaker.residual))
