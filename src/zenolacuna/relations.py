"""Finite relation operations. Outcomes encode complete observations/traces."""

from .model import (
    Candidate,
    LacunaError,
    OutcomeKind,
    Relation,
    Scope,
    Witness,
    index_set,
    relation,
)


def preservation_error(scope: Scope, candidate: Candidate) -> str | None:
    relation(candidate.allowed, len(scope.contexts), len(scope.outcomes))
    index_set(candidate.assumptions, len(scope.contexts))
    if not set(scope.assumptions) <= set(candidate.assumptions):
        return "PROTECTED_REQUIREMENT_LOST"
    for requirement in scope.protected:
        for i in requirement.applicability:
            if i not in candidate.assumptions:
                return "PROTECTED_REQUIREMENT_LOST"
            if not set(candidate.allowed[i]) <= set(requirement.allowed[i]):
                return "PROTECTED_REQUIREMENT_LOST"
            if not set(requirement.required[i]) <= set(candidate.allowed[i]):
                return "REQUIRED_BEHAVIOR_LOST"
    for i in scope.assumptions:
        if not set(candidate.allowed[i]) <= set(scope.contract[i]):
            return "CONTRACT_VIOLATION"
        if not candidate.allowed[i]:
            return "UNREACHABLE_APPLICABILITY"
    return None


def observation_key(scope: Scope, allowed: Relation) -> tuple[tuple[tuple[str, str], ...], ...]:
    return tuple(tuple(sorted({(scope.outcomes[o].kind.value, scope.outcomes[o].observation)
                              for o in allowed[c]})) for c in scope.assumptions)


def validate_projection(scope: Scope) -> None:
    for c in scope.assumptions:
        verdicts: dict[tuple[str, str], tuple[bool, ...]] = {}
        for o, outcome in enumerate(scope.outcomes):
            key = (outcome.kind.value, outcome.observation)
            verdict = (o in scope.contract[c],) + tuple(
                flag for requirement in scope.protected if c in requirement.applicability
                for flag in (o in requirement.allowed[c], o in requirement.required[c])
            )
            if key in verdicts and verdicts[key] != verdict:
                raise LacunaError("OBSERVATION_LOSES_REQUIREMENT")
            verdicts[key] = verdict


def semantic_classes(scope: Scope, survivors: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    index_set(survivors, len(scope.hypotheses))
    validate_projection(scope)
    groups: dict[tuple, list[int]] = {}
    for h in survivors:
        key = observation_key(scope, scope.hypotheses[h].allowed)
        groups.setdefault(key, []).append(h)
    return tuple(tuple(group) for group in groups.values())


def admissible(scope: Scope) -> tuple[int, ...]:
    return tuple(i for i, h in enumerate(scope.hypotheses)
                 if preservation_error(scope, Candidate(h.name, h.allowed, scope.assumptions)) is None)


def validate_questions(scope: Scope) -> None:
    classes = semantic_classes(scope, tuple(range(len(scope.hypotheses))))
    for question in scope.questions:
        for group in classes:
            if len({question.answers[i] for i in group}) != 1:
                raise LacunaError("NON_CONGRUENT_QUESTION")


def find_witness(scope: Scope, survivors: tuple[int, ...]) -> Witness | None:
    classes = semantic_classes(scope, survivors)
    if len(classes) < 2:
        return None
    left_id, right_id = classes[0][0], classes[1][0]
    # Any two distinct classes suffice. Searching every class pair adds no evidence.
    for c in scope.assumptions:
        left, right = scope.hypotheses[left_id].allowed[c], scope.hypotheses[right_id].allowed[c]
        if not left or not right:
            continue
        left_keys = {(scope.outcomes[o].kind, scope.outcomes[o].observation) for o in left}
        right_keys = {(scope.outcomes[o].kind, scope.outcomes[o].observation) for o in right}
        for a in left:
            if (scope.outcomes[a].kind, scope.outcomes[a].observation) not in right_keys:
                return Witness(scope.root, c, left_id, right_id, a, right[0])
        for b in right:
            if (scope.outcomes[b].kind, scope.outcomes[b].observation) not in left_keys:
                return Witness(scope.root, c, left_id, right_id, left[0], b)
    return None


def check_witness(scope: Scope, witness: Witness) -> None:
    if type(witness) is not Witness or witness.scope_root != scope.root:
        raise LacunaError("WITNESS_PREMISE_FAILED")
    for value, bound in ((witness.context, len(scope.contexts)),
                         (witness.left_hypothesis, len(scope.hypotheses)),
                         (witness.right_hypothesis, len(scope.hypotheses)),
                         (witness.left_outcome, len(scope.outcomes)),
                         (witness.right_outcome, len(scope.outcomes))):
        if type(value) is not int or not 0 <= value < bound:
            raise LacunaError("WITNESS_PREMISE_FAILED")
    if witness.context not in scope.assumptions:
        raise LacunaError("WITNESS_PREMISE_FAILED")
    validate_projection(scope)
    for h, o in ((witness.left_hypothesis, witness.left_outcome),
                 (witness.right_hypothesis, witness.right_outcome)):
        hypothesis = scope.hypotheses[h]
        if preservation_error(scope, Candidate(hypothesis.name, hypothesis.allowed, scope.assumptions)) is not None:
            raise LacunaError("WITNESS_PREMISE_FAILED")
        if o not in hypothesis.allowed[witness.context]:
            raise LacunaError("WITNESS_PREMISE_FAILED")
    a, b = scope.outcomes[witness.left_outcome], scope.outcomes[witness.right_outcome]
    if (a.kind, a.observation) == (b.kind, b.observation):
        raise LacunaError("WITNESS_PREMISE_FAILED")
    left_keys = {(scope.outcomes[o].kind, scope.outcomes[o].observation)
                 for o in scope.hypotheses[witness.left_hypothesis].allowed[witness.context]}
    right_keys = {(scope.outcomes[o].kind, scope.outcomes[o].observation)
                  for o in scope.hypotheses[witness.right_hypothesis].allowed[witness.context]}
    if left_keys == right_keys or ((a.kind, a.observation) in right_keys and (b.kind, b.observation) in left_keys):
        raise LacunaError("WITNESS_PREMISE_FAILED")


def has_required_success(scope: Scope) -> bool:
    return any(scope.outcomes[o].kind is OutcomeKind.ACCEPT
               for k in scope.protected for c in k.applicability for o in k.required[c])
