"""Deterministic question proposals that an LLM can explain but cannot approve."""

from dataclasses import replace

from .engine import analyze
from .model import Question, Scope
from .relations import semantic_classes


def membership_questions(scope: Scope, *, maximum: int = 32) -> tuple[Question, ...]:
    """Find distinct observable-membership partitions, with a reproducible bound."""
    if type(maximum) is not int or not 1 <= maximum <= 32:
        from .model import LacunaError
        raise LacunaError("QUESTION_LIMIT")
    semantic_classes(scope, tuple(range(len(scope.hypotheses))))
    seen: set[tuple[str, ...]] = set()
    proposals: list[Question] = []
    for c in scope.assumptions:
        for o, outcome in enumerate(scope.outcomes):
            answers = tuple("allowed" if any(
                scope.outcomes[p].kind is outcome.kind
                and scope.outcomes[p].observation == outcome.observation for p in h.allowed[c]
            ) else "forbidden" for h in scope.hypotheses)
            if len(set(answers)) < 2 or answers in seen:
                continue
            seen.add(answers)
            # Complement partitions carry the same information; retain the first.
            seen.add(tuple("forbidden" if a == "allowed" else "allowed" for a in answers))
            prompt = (f"For {scope.contexts[c]!r}, should the complete observation "
                      f"{outcome.kind.value}:{outcome.observation!r} be allowed? "
                      "Choose a requirement; use an unlisted answer if neither interpretation fits.")
            proposals.append(Question(f"membership-{c:03d}-{o:03d}", prompt, 1, answers))
            if len(proposals) == maximum:
                return tuple(proposals)
    return tuple(proposals)


def proposal_packet(scope: Scope) -> dict[str, object]:
    """Read-only swarm handoff. A proposed scope always requires a new frozen run."""
    report = analyze(scope)
    proposed = membership_questions(scope)
    question_scope = replace(scope, questions=proposed)
    return {
        "schema": "zenolacuna/proposal-packet-v1",
        "scope_root": scope.root,
        "authority": "NONE",
        "task": "Explain the checked witness, challenge H and O, and propose additional requirements as data.",
        "nonclaims": ["Human intent may lie outside H", "No approval or runtime authority"],
        "current": report,
        "suggested_questions": proposed,
        "suggested_policy": analyze(question_scope).policy,
        "protected_requirements": scope.protected,
        "omission_family": scope.omission_family,
    }
