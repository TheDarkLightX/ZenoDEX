"""Tau cross-check of finite relation equivalence using generated Boolean terms."""

from dataclasses import dataclass

from src.tau_composition.runtime import TauQueryError, TauRuntime

from ..model import Evidence, LacunaError, Relation, Scope, relation


@dataclass(frozen=True, slots=True)
class TauComparison:
    scope_root: str
    evidence: Evidence
    code: str
    equivalent: bool | None
    formula: str
    binary_sha256: str
    authority: str = "NONE"


def _cell_term(cell: int, bits: int) -> str:
    return "(" + " & ".join(f"b{i}" if cell & (1 << i) else f"b{i}'"
                            for i in range(bits)) + ")"


def equivalence_formula(scope: Scope, left: Relation, right: Relation) -> str:
    """Enumerate projected cells, not text or a selected nondeterministic outcome."""
    relation(left, len(scope.contexts), len(scope.outcomes))
    relation(right, len(scope.contexts), len(scope.outcomes))
    observables = tuple(sorted({(o.kind.value, o.observation) for o in scope.outcomes}))
    cells = tuple((c, kind, observation) for c in scope.assumptions for kind, observation in observables)
    if not cells or len(cells) > 2048:
        raise LacunaError("TAU_PROFILE_LIMIT")
    bits = max(1, (len(cells) - 1).bit_length())

    def term(rows: Relation) -> str:
        terms = []
        for i, (c, kind, observation) in enumerate(cells):
            if any(scope.outcomes[o].kind.value == kind and scope.outcomes[o].observation == observation
                   for o in rows[c]):
                terms.append(_cell_term(i, bits))
        return "(" + " | ".join(terms) + ")" if terms else "0"

    return f"(({term(left)} ^ {term(right)}) = 0)"


def compare(runtime: TauRuntime, scope: Scope, left: Relation, right: Relation) -> TauComparison:
    formula = equivalence_formula(scope, left, right)
    try:
        verdict = runtime.valid(formula)
    except (TauQueryError, OSError, ValueError) as error:
        code = error.code if isinstance(error, TauQueryError) else "native_io"
        return TauComparison(scope.root, Evidence.UNKNOWN, "SOLVER_UNKNOWN:" + code, None,
                             formula, runtime.binary_sha256)
    if type(verdict) is not bool:
        return TauComparison(scope.root, Evidence.UNKNOWN, "SOLVER_UNKNOWN:verdict_type", None,
                             formula, runtime.binary_sha256)
    # Deliberately independent of the production semantic quotient helper.
    expected = all(
        any(scope.outcomes[p].kind is outcome.kind and scope.outcomes[p].observation == outcome.observation
            for p in left[c])
        == any(scope.outcomes[p].kind is outcome.kind and scope.outcomes[p].observation == outcome.observation
               for p in right[c])
        for c in scope.assumptions for outcome in scope.outcomes
    )
    if verdict != expected:
        return TauComparison(scope.root, Evidence.UNKNOWN, "SOLVER_DISAGREEMENT", None,
                             formula, runtime.binary_sha256)
    return TauComparison(scope.root, Evidence.EXHAUSTIVE_FINITE, "TAU_FINITE_RELATION_CHECKED",
                         verdict, formula, runtime.binary_sha256)


@dataclass(frozen=True, slots=True)
class QueueGuardProjection:
    evidence: Evidence
    code: str
    query: str
    guard: str | None
    binary_sha256: str
    authority: str = "NONE"


def project_queue_guard(runtime: TauRuntime) -> QueueGuardProjection:
    """Eliminate the proposed consumer's post-state variable from the queue invariant."""
    query = "ex cp ((cp = n) && ((q = 0) || (v = cp)))"
    try:
        guard = runtime.project(query)
        if not runtime.valid(f"(({guard}) <-> ((q = 0) || (v = n)))"):
            return QueueGuardProjection(Evidence.UNKNOWN, "SOLVER_DISAGREEMENT", query, None, runtime.binary_sha256)
    except (TauQueryError, OSError, ValueError) as error:
        code = error.code if isinstance(error, TauQueryError) else "native_io"
        return QueueGuardProjection(Evidence.UNKNOWN, "SOLVER_UNKNOWN:" + code, query, None, runtime.binary_sha256)
    return QueueGuardProjection(Evidence.EXHAUSTIVE_FINITE, "TAU_QUEUE_PREIMAGE_CHECKED",
                               query, guard, runtime.binary_sha256)
