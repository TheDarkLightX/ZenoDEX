"""Deterministic signed transitions; runtime effects are requests to the shell."""

import hashlib
from dataclasses import dataclass, replace

from .authority import Action, SignedCommand, encode_signed, verify
from .check import close_model
from .codec import _array, _string, decode_candidate, encode
from .engine import analyze, assess_repair
from .model import LacunaError, Profile, Workflow, digest
from .project_types import (
    ProjectState,
    decode_task,
    payload_object,
    retired_requirements,
    sha_field,
)
from .questions import filter_answer


def revision_of(signed: SignedCommand) -> str:
    return hashlib.sha256(b"zenolacuna/project-revision/v1\0" + encode_signed(signed)).hexdigest()


def candidate_root(state: ProjectState) -> str | None:
    return None if state.candidate is None else digest(state.candidate)


def witness_root(state: ProjectState) -> str:
    witness = analyze(state.task.scope, state.survivors).witness
    return digest(witness) if witness is not None else hashlib.sha256(b"zenolacuna/project/no-witness/v1").hexdigest()


@dataclass(frozen=True, slots=True)
class Step:
    state: ProjectState
    check_runtime: bool = False


def initialize(signed: SignedCommand, *, owner_key: str, checker_sha256: str) -> Step:
    command = signed.command
    verify(signed, owner_key=owner_key, delegates=(), scope_root="0" * 64)
    if command.action is not Action.INIT or command.parent is not None:
        raise LacunaError("INITIALIZATION_REQUIRED")
    item = payload_object(command.payload, {"task", "checker_sha256"})
    if sha_field(item["checker_sha256"]) != checker_sha256:
        raise LacunaError("CHECKER_DRIFT")
    task = decode_task(item["task"])
    if task.scope.profile is not Profile.REAL_OWNER:
        raise LacunaError("AUTHORIZATION_PROFILE_MISMATCH")
    report = analyze(task.scope)
    revision = revision_of(signed)
    return Step(ProjectState(command.project_id, revision, revision, task, report.survivors,
                             None, False, (), None))


def _revise(state: ProjectState, signed: SignedCommand) -> Step:
    item = payload_object(signed.command.payload, {"scope_root", "task", "retired_protected", "reason"})
    successor = decode_task(item["task"])
    if successor.scope.profile is not state.task.scope.profile:
        raise LacunaError("AUTHORIZATION_PROFILE_MISMATCH")
    if not _string(item["reason"]).strip():
        raise LacunaError("REVISION_REASON_REQUIRED")
    retired = tuple(_string(name) for name in _array(item["retired_protected"]))
    if retired != retired_requirements(state.task.scope, successor.scope):
        raise LacunaError("PROTECTED_REQUIREMENT_LOST")
    if successor == state.task:
        raise LacunaError("UNCHANGED_TASK")
    report = analyze(successor.scope)
    revision = revision_of(signed)
    return Step(ProjectState(state.project_id, revision, revision, successor, report.survivors,
                             None, False, (), None))


def _answer(state: ProjectState, signed: SignedCommand) -> Step:
    item = payload_object(signed.command.payload, {"scope_root", "question", "answer", "witness_root"})
    question, answer = _string(item["question"]), _string(item["answer"])
    if any(q == question for q, _answer, _root, _parent in state.answers):
        raise LacunaError("DUPLICATE_CONFLICT")
    if sha_field(item["witness_root"]) != witness_root(state):
        raise LacunaError("STALE_ANSWER")
    report = analyze(state.task.scope, state.survivors)
    if report.pending_question is None or report.pending_question.name != question:
        raise LacunaError("QUESTION_NOT_PENDING")
    survivors = filter_answer(state.task.scope, state.survivors, question, answer)
    revision = revision_of(signed)
    return Step(replace(state, revision=revision, survivors=survivors, candidate=None, completion=None,
                        answers=state.answers + ((question, answer, revision, state.revision),)))


def transition(state: ProjectState, signed: SignedCommand, *, owner_key: str) -> Step:
    command = signed.command
    verify(signed, owner_key=owner_key, delegates=state.task.delegates, scope_root=state.task.scope.root)
    if command.project_id != state.project_id:
        raise LacunaError("WRONG_PROJECT")
    # A question already answered in this scope has exactly one authoritative binding.
    if command.action is Action.ANSWER:
        item = payload_object(command.payload, {"scope_root", "question", "answer", "witness_root"})
        if item["scope_root"] == state.task.scope.root and any(
            q == item["question"] and parent == command.parent for q, _, _, parent in state.answers
        ):
            raise LacunaError("DUPLICATE_CONFLICT")
    if command.parent != state.revision:
        raise LacunaError("STALE_ANSWER")
    if command.action is Action.INIT:
        raise LacunaError("ALREADY_INITIALIZED")
    expected = {
        Action.REVISE: {"scope_root", "task", "retired_protected", "reason"},
        Action.ANSWER: {"scope_root", "question", "answer", "witness_root"},
        Action.ASSESS: {"scope_root", "candidate"},
        Action.COMPLETE: {"scope_root", "candidate_root"},
        Action.CANCEL: {"scope_root"}, Action.RESUME: {"scope_root"},
    }
    item = payload_object(command.payload, expected[command.action])
    if sha_field(item["scope_root"]) != state.task.scope.root:
        raise LacunaError("STALE_ANSWER")
    revision = revision_of(signed)
    if command.action is Action.RESUME:
        if not state.cancelled:
            raise LacunaError("NOT_CANCELLED")
        return Step(replace(state, revision=revision, cancelled=False, candidate=None, completion=None))
    if command.action is Action.REVISE:
        # A new owner-approved generation can recover from cancellation even
        # after its working source files have changed. Old work stays obsolete.
        return _revise(state, signed)
    if state.cancelled:
        raise LacunaError("CANCELLED")
    if command.action is Action.CANCEL:
        return Step(replace(state, revision=revision, cancelled=True, candidate=None, completion=None))
    if command.action is Action.ANSWER:
        return _answer(state, signed)
    if command.action is Action.ASSESS:
        candidate = decode_candidate(encode(item["candidate"]))
        report = assess_repair(state.task.scope, state.survivors, candidate)
        if report.workflow is not Workflow.READY_FOR_REPLAY:
            raise LacunaError(report.code)
        return Step(replace(state, revision=revision, candidate=candidate, completion=None))
    if command.action is Action.COMPLETE:
        analysis = analyze(state.task.scope, state.survivors)
        if analysis.workflow is not Workflow.READY_FOR_REPLAY:
            raise LacunaError(analysis.code)
        if state.candidate is None:
            raise LacunaError("CANDIDATE_REQUIRED")
        if sha_field(item["candidate_root"]) != candidate_root(state):
            raise LacunaError("STALE_CANDIDATE")
        report = close_model(state.task.scope, state.survivors, state.candidate)
        if report.workflow is not Workflow.COMPLETE_FOR_SCOPE:
            raise LacunaError(report.code)
        return Step(replace(state, revision=revision, completion=None), True)
    raise LacunaError("UNSUPPORTED_ACTION")
