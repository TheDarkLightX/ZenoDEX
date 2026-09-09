"""Pure orchestration. Replaying a model is distinct from binding a runtime."""

from dataclasses import replace

from .model import Candidate, Evidence, LacunaError, Report, Scope, Workflow, index_set
from .questions import choose_question
from .relations import (
    admissible,
    check_witness,
    find_witness,
    preservation_error,
    semantic_classes,
)


def analyze(scope: Scope, survivors: tuple[int, ...] | None = None) -> Report:
    available = admissible(scope)
    active = available if survivors is None else survivors
    index_set(active, len(scope.hypotheses))
    if not set(active) <= set(available):
        raise LacunaError("INVALID_SURVIVORS")
    classes = semantic_classes(scope, active)
    policy = choose_question(scope, active)
    witness = find_witness(scope, active)
    if witness is not None:
        check_witness(scope, witness)
    if not classes:
        workflow, code = Workflow.INCONCLUSIVE, "EMPTY_H_CONFLICT"
    elif len(classes) == 1:
        workflow, code = Workflow.READY_FOR_REPLAY, "DECISIONS_RESOLVED"
    elif policy.question is not None:
        workflow, code = Workflow.NEEDS_DECISION, "MISSING_REQUIREMENT"
    else:
        workflow, code = Workflow.INCONCLUSIVE, policy.status
    pending = next((q for q in scope.questions if q.name == policy.question), None)
    return Report(scope.root, workflow, Evidence.MODEL_ONLY, code, active, classes,
                  policy, witness, scope_kind=scope.kind, history_bound=scope.history_bound,
                  pending_question=pending)


def assess_repair(scope: Scope, survivors: tuple[int, ...], candidate: Candidate) -> Report:
    report = analyze(scope, survivors)
    error = preservation_error(scope, candidate)
    if error is not None:
        return replace(report, workflow=Workflow.REPAIR_REQUIRED, code="CODE_BUG:" + error)
    if len(report.classes) != 1:
        return report
    target = scope.hypotheses[report.classes[0][0]].allowed
    for c in scope.assumptions:
        actual = {(scope.outcomes[o].kind, scope.outcomes[o].observation) for o in candidate.allowed[c]}
        expected = {(scope.outcomes[o].kind, scope.outcomes[o].observation) for o in target[c]}
        if not actual <= expected:
            return replace(report, workflow=Workflow.REPAIR_REQUIRED, code="CODE_BUG:DECIDED_REQUIREMENT_VIOLATION")
    return replace(report, workflow=Workflow.READY_FOR_REPLAY, code="REPAIR_PRESERVES_REQUIREMENTS")
