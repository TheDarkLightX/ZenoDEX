"""Independent cell enumeration owns closure. No imported relation evaluator."""

from dataclasses import replace

from .engine import analyze
from .model import (
    Candidate,
    Evidence,
    LacunaError,
    OutcomeKind,
    Policy,
    Relation,
    Report,
    Scope,
    ScopeKind,
    Workflow,
    index_set,
    relation,
)


def _replay_rows(scope: Scope, rows: Relation, assumptions: tuple[int, ...]) -> tuple[frozenset[tuple[str, str]], ...]:
    relation(rows, len(scope.contexts), len(scope.outcomes))
    index_set(assumptions, len(scope.contexts))
    projections: list[frozenset[tuple[str, str]]] = []
    required_success = False
    for c in range(len(scope.contexts)):
        present = set(rows[c])
        if c in scope.assumptions:
            if c not in assumptions:
                raise LacunaError("PROTECTED_REQUIREMENT_LOST")
            if not present:
                raise LacunaError("UNREACHABLE_APPLICABILITY")
            permitted = set(scope.contract[c])
            if any(o in present and o not in permitted for o in range(len(scope.outcomes))):
                raise LacunaError("CONTRACT_VIOLATION")
            projections.append(frozenset((scope.outcomes[o].kind.value, scope.outcomes[o].observation)
                                        for o in range(len(scope.outcomes)) if o in present))
        for requirement in scope.protected:
            if c not in requirement.applicability:
                continue
            if c not in assumptions:
                raise LacunaError("PROTECTED_REQUIREMENT_LOST")
            permitted, required = set(requirement.allowed[c]), set(requirement.required[c])
            for o in range(len(scope.outcomes)):
                if o in present and o not in permitted:
                    raise LacunaError("PROTECTED_REQUIREMENT_LOST")
                if o in required:
                    if o not in present:
                        raise LacunaError("REQUIRED_BEHAVIOR_LOST")
                    required_success |= scope.outcomes[o].kind is OutcomeKind.ACCEPT
    if not required_success:
        raise LacunaError("MISSING_POSITIVE_WITNESS")
    return tuple(projections)


def close_model(scope: Scope, survivors: tuple[int, ...], candidate: Candidate) -> Report:
    """Replay all declared finite cells. Makes no source/runtime correspondence claim."""
    report = analyze(scope, survivors)
    if not survivors:
        raise LacunaError("EMPTY_H_CONFLICT")
    if len(report.classes) != 1:
        raise LacunaError("UNRESOLVED_DECISIONS")
    if scope.kind is ScopeKind.FINITE_STATE_GRAPH:
        return replace(report, workflow=Workflow.INCONCLUSIVE, evidence=Evidence.UNKNOWN,
                       code="GRAPH_EVIDENCE_REQUIRED")
    # Budget counts complete predicate-cell passes, including independent hypotheses.
    work_bound = len(scope.contexts) * len(scope.outcomes) * (2 + len(scope.protected)) * (1 + len(survivors))
    if work_bound > scope.max_work:
        raise LacunaError("REPLAY_BUDGET_EXCEEDED")
    replayed_classes = set()
    for h in survivors:
        replayed_classes.add(_replay_rows(scope, scope.hypotheses[h].allowed, scope.assumptions))
    if len(replayed_classes) != 1:
        raise LacunaError("UNRESOLVED_DECISIONS")
    expected = next(iter(replayed_classes))
    actual = _replay_rows(scope, candidate.allowed, candidate.assumptions)
    if any(not a <= e for a, e in zip(actual, expected, strict=True)):
        raise LacunaError("DECIDED_REQUIREMENT_VIOLATION")
    evidence = Evidence.BOUNDED_SEARCH if scope.kind is ScopeKind.BOUNDED_HISTORY else Evidence.EXHAUSTIVE_FINITE
    return Report(scope.root, Workflow.COMPLETE_FOR_SCOPE, evidence, "FINITE_MODEL_REPLAYED",
                  survivors, (survivors,), Policy("EXACT_MINIMAX", None, 0, 0), None,
                  scope_kind=scope.kind, history_bound=scope.history_bound)
