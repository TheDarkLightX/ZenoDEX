"""Owned values for the finite ZenoLacuna profile. No IO or ambient authority."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass
from enum import Enum
from typing import TypeAlias

Relation: TypeAlias = tuple[tuple[int, ...], ...]


class LacunaError(ValueError):
    """Stable public rejection code; diagnostics never authorize a transition."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


class Profile(str, Enum):
    SIMULATED = "SIMULATED"
    REAL_OWNER = "REAL_OWNER"


class ScopeKind(str, Enum):
    FINITE_RELATION = "FINITE_RELATION"
    FINITE_STATE_GRAPH = "FINITE_STATE_GRAPH"
    BOUNDED_HISTORY = "BOUNDED_HISTORY"


class OutcomeKind(str, Enum):
    ACCEPT = "ACCEPT"
    REJECT = "REJECT"


class Workflow(str, Enum):
    NEEDS_DECISION = "NEEDS_DECISION"
    NEEDS_MODEL_REVISION = "NEEDS_MODEL_REVISION"
    REPAIR_REQUIRED = "REPAIR_REQUIRED"
    READY_FOR_REPLAY = "READY_FOR_REPLAY"
    COMPLETE_FOR_SCOPE = "COMPLETE_FOR_SCOPE"
    INCONCLUSIVE = "INCONCLUSIVE"
    CANCELLED = "CANCELLED"


class Evidence(str, Enum):
    EXHAUSTIVE_FINITE = "EXHAUSTIVE_FINITE"
    BOUNDED_SEARCH = "BOUNDED_SEARCH"
    MODEL_ONLY = "MODEL_ONLY"
    UNKNOWN = "UNKNOWN"


def text_value(value: str, maximum: int = 512) -> None:
    if type(value) is not str or not 1 <= len(value) <= maximum or "\x00" in value:
        raise LacunaError("INVALID_TEXT")


def exact_int(value: int, low: int, high: int) -> None:
    if type(value) is not int or not low <= value <= high:
        raise LacunaError("INVALID_INTEGER")


def index_set(values: tuple[int, ...], size: int) -> None:
    if type(values) is not tuple:
        raise LacunaError("INVALID_INDEX_SET")
    for value in values:
        exact_int(value, 0, size - 1)
    if tuple(sorted(set(values))) != values:
        raise LacunaError("NONCANONICAL_INDEX_SET")


def relation(value: Relation, contexts: int, outcomes: int) -> None:
    if type(value) is not tuple or len(value) != contexts:
        raise LacunaError("RELATION_SHAPE")
    for row in value:
        index_set(row, outcomes)


def owned_tuple(values: tuple, kind: type, maximum: int) -> None:
    if type(values) is not tuple or len(values) > maximum:
        raise LacunaError("INVALID_COLLECTION")
    if any(type(value) is not kind for value in values):
        raise LacunaError("INVALID_OWNED_TYPE")


def unique_names(values: tuple) -> None:
    if len({value.name for value in values}) != len(values):
        raise LacunaError("DUPLICATE_NAME")


@dataclass(frozen=True, slots=True)
class Outcome:
    name: str
    observation: str
    kind: OutcomeKind

    def __post_init__(self) -> None:
        text_value(self.name)
        text_value(self.observation, 4096)
        if type(self.kind) is not OutcomeKind:
            raise LacunaError("INVALID_OUTCOME_KIND")


@dataclass(frozen=True, slots=True)
class Requirement:
    name: str
    applicability: tuple[int, ...]
    allowed: Relation
    required: Relation

    def __post_init__(self) -> None:
        text_value(self.name)
        index_set(self.applicability, 256)
        relation(self.allowed, len(self.allowed), 512)
        relation(self.required, len(self.allowed), 512)


@dataclass(frozen=True, slots=True)
class Hypothesis:
    name: str
    allowed: Relation

    def __post_init__(self) -> None:
        text_value(self.name)
        relation(self.allowed, len(self.allowed), 512)


@dataclass(frozen=True, slots=True)
class Question:
    name: str
    prompt: str
    cost: int
    answers: tuple[str, ...]

    def __post_init__(self) -> None:
        text_value(self.name)
        text_value(self.prompt, 4096)
        exact_int(self.cost, 1, 1_000_000)
        owned_tuple(self.answers, str, 64)
        for answer in self.answers:
            text_value(answer)


@dataclass(frozen=True, slots=True)
class SourceRef:
    path: str
    sha256: str

    def __post_init__(self) -> None:
        text_value(self.path, 1024)
        if self.path.startswith("/") or any(p in ("", ".", "..") for p in self.path.split("/")) or "\\" in self.path:
            raise LacunaError("INVALID_SOURCE_PATH")
        if type(self.sha256) is not str or re.fullmatch("[0-9a-f]{64}", self.sha256) is None:
            raise LacunaError("INVALID_DIGEST")


@dataclass(frozen=True, slots=True)
class Scope:
    name: str
    contexts: tuple[str, ...]
    outcomes: tuple[Outcome, ...]
    assumptions: tuple[int, ...]
    contract: Relation
    protected: tuple[Requirement, ...]
    hypotheses: tuple[Hypothesis, ...]
    questions: tuple[Question, ...]
    sources: tuple[SourceRef, ...] = ()
    profile: Profile = Profile.SIMULATED
    kind: ScopeKind = ScopeKind.FINITE_RELATION
    history_bound: int | None = None
    omission_family: tuple[str, ...] = ()
    max_work: int = 100_000

    def __post_init__(self) -> None:
        text_value(self.name)
        owned_tuple(self.contexts, str, 256)
        owned_tuple(self.outcomes, Outcome, 512)
        if not self.contexts or not self.outcomes:
            raise LacunaError("EMPTY_DOMAIN")
        for context in self.contexts:
            text_value(context, 4096)
        if len(set(self.contexts)) != len(self.contexts):
            raise LacunaError("DUPLICATE_CONTEXT")
        n, m = len(self.contexts), len(self.outcomes)
        if n * m > 65_536:
            raise LacunaError("DOMAIN_TOO_LARGE")
        index_set(self.assumptions, n)
        relation(self.contract, n, m)
        owned_tuple(self.protected, Requirement, 32)
        owned_tuple(self.hypotheses, Hypothesis, 64)
        owned_tuple(self.questions, Question, 64)
        owned_tuple(self.sources, SourceRef, 32)
        owned_tuple(self.omission_family, str, 128)
        for family in self.omission_family:
            text_value(family)
        for values in (self.outcomes, self.protected, self.hypotheses, self.questions):
            unique_names(values)
        if len({source.path for source in self.sources}) != len(self.sources):
            raise LacunaError("DUPLICATE_SOURCE")
        for requirement in self.protected:
            index_set(requirement.applicability, n)
            relation(requirement.allowed, n, m)
            relation(requirement.required, n, m)
            for i in range(n):
                if not set(requirement.required[i]) <= set(requirement.allowed[i]):
                    raise LacunaError("INCONSISTENT_REQUIREMENT")
                if i not in requirement.applicability and requirement.required[i]:
                    raise LacunaError("REQUIRED_OUTSIDE_APPLICABILITY")
        for hypothesis in self.hypotheses:
            relation(hypothesis.allowed, n, m)
        for question in self.questions:
            if len(question.answers) != len(self.hypotheses):
                raise LacunaError("QUESTION_NOT_TOTAL")
        if type(self.profile) is not Profile or type(self.kind) is not ScopeKind:
            raise LacunaError("INVALID_SCOPE_VARIANT")
        if self.kind is ScopeKind.BOUNDED_HISTORY:
            exact_int(self.history_bound, 1, 1024)  # type: ignore[arg-type]
        elif self.history_bound is not None:
            raise LacunaError("UNEXPECTED_HISTORY_BOUND")
        exact_int(self.max_work, 1, 1_000_000)

    @property
    def root(self) -> str:
        return digest(self)


@dataclass(frozen=True, slots=True)
class Candidate:
    name: str
    allowed: Relation
    assumptions: tuple[int, ...]

    def __post_init__(self) -> None:
        text_value(self.name)
        relation(self.allowed, len(self.allowed), 512)
        index_set(self.assumptions, 256)


@dataclass(frozen=True, slots=True)
class Witness:
    scope_root: str
    context: int
    left_hypothesis: int
    right_hypothesis: int
    left_outcome: int
    right_outcome: int


@dataclass(frozen=True, slots=True)
class Policy:
    status: str
    question: str | None
    worst_cost: int | None
    work: int


@dataclass(frozen=True, slots=True)
class Report:
    scope_root: str
    workflow: Workflow
    evidence: Evidence
    code: str
    survivors: tuple[int, ...]
    classes: tuple[tuple[int, ...], ...]
    policy: Policy
    witness: Witness | None
    authority: str = "NONE"
    scope_kind: ScopeKind = ScopeKind.FINITE_RELATION
    history_bound: int | None = None
    claim: str = "FINITE_MODEL_ONLY"
    pending_question: Question | None = None


@dataclass(frozen=True, slots=True)
class Decision:
    command_id: str
    scope_root: str
    parent: str
    question: str
    answer: str
    witness_root: str
    profile: Profile
    actor: str

    def __post_init__(self) -> None:
        for value in (self.command_id, self.scope_root, self.parent, self.question,
                      self.answer, self.witness_root, self.actor):
            text_value(value, 4096)
        if type(self.profile) is not Profile:
            raise LacunaError("INVALID_PROFILE")


def digest(value: object) -> str:
    """Identity for owned dataclasses; this hash itself conveys no authority."""
    data = asdict(value)  # type: ignore[call-overload]
    encoded = json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(b"zenolacuna/v1\x00" + encoded.encode("ascii")).hexdigest()
