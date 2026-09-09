"""Question policies over semantic classes, with integer costs and explicit infinity."""

from .model import LacunaError, Policy, Scope, index_set
from .relations import semantic_classes, validate_questions


def filter_answer(scope: Scope, survivors: tuple[int, ...], question_name: str, answer: str) -> tuple[int, ...]:
    validate_questions(scope)
    index_set(survivors, len(scope.hypotheses))
    question = next((q for q in scope.questions if q.name == question_name), None)
    if question is None:
        raise LacunaError("UNKNOWN_QUESTION")
    if answer not in question.answers:
        raise LacunaError("NEEDS_MODEL_REVISION")
    result = tuple(i for i in survivors if question.answers[i] == answer)
    if not result:
        raise LacunaError("EMPTY_H_CONFLICT")
    return result


def choose_question(scope: Scope, survivors: tuple[int, ...]) -> Policy:
    validate_questions(scope)
    classes = semantic_classes(scope, survivors)
    if not classes:
        return Policy("EMPTY_H_CONFLICT", None, None, 0)
    if len(classes) == 1:
        return Policy("EXACT_MINIMAX", None, 0, 0)
    if len(classes) > 12 or len(scope.questions) > 32:
        return Policy("DP_BUDGET_EXCEEDED", None, None, 0)
    representatives = tuple(group[0] for group in classes)
    memo: dict[tuple[int, ...], tuple[int | None, str | None]] = {}
    work = 0

    def solve(active: tuple[int, ...]) -> tuple[int | None, str | None]:
        nonlocal work
        if len(active) == 1:
            return 0, None
        if active in memo:
            return memo[active]
        best: tuple[int, str] | None = None
        for question in sorted(scope.questions, key=lambda q: q.name):
            work += 1
            if work > scope.max_work:
                raise LacunaError("DP_BUDGET_EXCEEDED")
            groups: dict[str, list[int]] = {}
            for h in active:
                groups.setdefault(question.answers[h], []).append(h)
            if len(groups) <= 1:
                continue
            children = [solve(tuple(group))[0] for group in groups.values()]
            if any(cost is None for cost in children):
                continue
            cost = question.cost + max(c for c in children if c is not None)
            choice = (cost, question.name)
            if best is None or choice < best:
                best = choice
        result = (None, None) if best is None else best
        memo[active] = result
        return result

    try:
        cost, name = solve(representatives)
    except LacunaError as error:
        return Policy(error.code, None, None, work)
    if cost is None:
        return Policy("UNSEPARABLE_IN_LANGUAGE", None, None, work)
    return Policy("EXACT_MINIMAX", name, cost, work)
