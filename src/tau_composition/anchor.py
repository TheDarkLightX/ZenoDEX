"""Native-checked common-anchor proposal maps for bounded Boolean contracts.

An anchor is an environment-only map for every proposal coordinate.  It is
checked against each original requirement by Tau before it may be used to make
an advisory host proposal.  This module does not synthesize anchors or grant
authority to a proposal.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from .models import Contract, RepairMap
from .resources import bounded_substitute, check_terms
from .runtime import TauQueryError, TauRuntime
from .terms import Term, constant, join, meet, negate, variable

__all__ = ["AnchorCompiler", "AnchoredRepair", "zero_anchor"]


def _validate_anchor(contract: Contract, anchor: RepairMap) -> None:
    if not isinstance(contract, Contract):
        raise ValueError("contract_type")
    if not isinstance(anchor, RepairMap):
        raise ValueError("anchor_type")
    if tuple(name for name, _term in anchor.assignments) != contract.controls:
        raise ValueError("anchor_control_coverage")
    environment = frozenset(contract.environment)
    for _name, term in anchor.assignments:
        if term.variables() - environment:
            raise ValueError("anchor_reads_non_environment")
    check_terms(tuple(term for _name, term in anchor.assignments))


def _all_equation(term: Term) -> str:
    """Render the closed universal Boolean-algebra equation ``term = 0``."""

    check_terms((term,))
    names = tuple(sorted(term.variables()))
    symbols = {name: f"v{index}" for index, name in enumerate(names)}
    rendered = {name: f"{symbol}:sbf" for name, symbol in symbols.items()}
    equation = f"({term.to_tau(rendered)} = 0:sbf)"
    if not names:
        return equation
    binders = ", ".join(f"{symbols[name]}:sbf" for name in names)
    return f"all {binders} ({equation})"


def _normalized_queries(contract: Contract, anchor: RepairMap) -> tuple[str, ...]:
    """Return role-normalized, closed validity queries for every requirement."""

    canonical_names = {
        name: f"e{index}" for index, name in enumerate(contract.environment)
    }
    canonical_names.update(
        (name, f"c{index}") for index, name in enumerate(contract.controls)
    )
    aliases = {name: variable(alias) for name, alias in canonical_names.items()}
    normalized_anchor = {
        canonical_names[name]: bounded_substitute(term, aliases)
        for name, term in anchor.assignments
    }
    return tuple(
        _all_equation(
            bounded_substitute(
                bounded_substitute(requirement.residual, aliases), normalized_anchor
            )
        )
        for requirement in contract.requirements
    )


@dataclass(frozen=True, slots=True)
class AnchoredRepair:
    """An immutable common anchor and evidence counts for one contract.

    The host transition retains an already-valid proposal.  For a nonzero joint
    residual it applies the environment-only anchor, then checks the original
    contract again before returning the candidate.
    """

    contract: Contract
    anchor: RepairMap
    native_queries: int
    cache_hits: int
    binary_sha256: str

    def __post_init__(self) -> None:
        _validate_anchor(self.contract, self.anchor)
        if type(self.native_queries) is not int or self.native_queries < 0:
            raise ValueError("native_query_count")
        if type(self.cache_hits) is not int or self.cache_hits < 0:
            raise ValueError("cache_hit_count")
        if type(self.binary_sha256) is not str:
            raise ValueError("binary_sha256_type")

    def propose(self, values: Mapping[str, bool]) -> dict[str, bool]:
        """Return a checked advisory proposal without mutating ``values``."""

        self.contract.validate_values(values)
        joint_residual = self.contract.residual
        if not joint_residual.evaluate(values):
            return dict(values)
        candidate = self.anchor.apply(values)
        if not self.contract.satisfied(candidate):
            raise ValueError("anchored_proposal_failed_contract")
        return candidate

    def polynomial_map(self) -> RepairMap:
        """Return ``x_j & R' | a_j & R`` for each control under joint residual ``R``."""

        residual = self.contract.residual
        replacements = self.anchor.replacements()
        assignments = tuple(
            (
                name,
                join(
                    meet(variable(name), negate(residual)),
                    meet(replacements[name], residual),
                ),
            )
            for name in self.contract.controls
        )
        check_terms((residual, *(term for _name, term in assignments)))
        return RepairMap(assignments)


class AnchorCompiler:
    """Reuse exact role-normalized native validity results for one runtime."""

    def __init__(self, runtime: TauRuntime) -> None:
        self.runtime = runtime
        self._validity: dict[str, bool] = {}
        self.cache_hits = 0

    def compile(self, contract: Contract, anchor: RepairMap) -> AnchoredRepair:
        """Check every original residual under ``anchor`` and return its proposal map."""

        _validate_anchor(contract, anchor)
        start_queries = len(self.runtime.records)
        start_hits = self.cache_hits
        for query in _normalized_queries(contract, anchor):
            if query in self._validity:
                self.cache_hits += 1
                valid = self._validity[query]
            else:
                valid = self.runtime.valid(query)
                self._validity[query] = valid
            if not valid:
                raise TauQueryError("anchor_not_valid")
        return AnchoredRepair(
            contract=contract,
            anchor=anchor,
            native_queries=len(self.runtime.records) - start_queries,
            cache_hits=self.cache_hits - start_hits,
            binary_sha256=self.runtime.binary_sha256,
        )


def zero_anchor(contract: Contract) -> RepairMap:
    """Return the ordered all-zero environment-only anchor for ``contract``."""

    if not isinstance(contract, Contract):
        raise ValueError("contract_type")
    return RepairMap(tuple((name, constant(False)) for name in contract.controls))
