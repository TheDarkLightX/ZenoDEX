"""Remaining original acceptance cases exercised through the signed project."""

import itertools
from dataclasses import replace

import pytest

from src.zenolacuna.authority import Action, Command, sign
from src.zenolacuna.model import (
    Candidate,
    Hypothesis,
    LacunaError,
    Outcome,
    OutcomeKind,
    Profile,
    Requirement,
    Scope,
    ScopeKind,
)
from src.zenolacuna.project_types import RuntimeSpec, Task, task_value
from tests.test_zenolacuna_project import answer, initialize, signed
from tests.test_zenolacuna_project_evidence import _create
from tests.zenolacuna_project_helpers import OWNER_SECRET


def test_given_valid_duplicate_and_already_stale_jobs_when_reordered_then_same_state_and_codes(tmp_path):
    results = []
    for number, order in enumerate(itertools.permutations(("valid", "retry", "stale"))):
        root = tmp_path / str(number)
        root.mkdir()
        project = initialize(root)
        valid = answer(project)
        stale = sign(Command(valid.command.project_id, "f" * 64, Action.ANSWER, valid.command.payload), OWNER_SECRET)
        codes = []
        for operation in order:
            if operation == "stale":
                with pytest.raises(LacunaError, match="^STALE_ANSWER$"):
                    project.apply(stale)
            else:
                codes.append(project.apply(valid)["code"])
        assert codes == ["DECISIONS_RESOLVED", "IDEMPOTENT_DUPLICATE"]
        results.append(project.export_bytes())
    assert len(set(results)) == 1


def test_given_first_answer_when_conflicting_answer_reuses_binding_then_first_is_authoritative(tmp_path):
    project = initialize(tmp_path)
    first, conflicting = answer(project, "yes"), answer(project, "no")
    project.apply(first)
    before = project.export_bytes()
    with pytest.raises(LacunaError, match="^DUPLICATE_CONFLICT$"):
        project.apply(conflicting)
    assert project.export_bytes() == before
    assert project.state().survivors == (0, 2)


def _trace_task(bound):
    names = tuple(format(i, f"0{bound}b") for i in range(1 << bound))
    outcomes = tuple(Outcome(name, name, OutcomeKind.ACCEPT) for name in names)
    rows = ((0, len(names) - 1),)
    scope = Scope(f"whole-trace-{bound}", ("initial",), outcomes, (0,), rows,
                  (Requirement("constant-trace", (0,), rows, ((0,),)),),
                  (Hypothesis("whole-traces", rows),), (), profile=Profile.REAL_OWNER,
                  kind=ScopeKind.BOUNDED_HISTORY, history_bound=bound)
    return Task(scope, RuntimeSpec("RELATION", (), ()), (), None, None)


def _assess_trace(project):
    from src.zenolacuna.project_types import plain
    scope = project.state().task.scope
    candidate = Candidate("whole-traces", scope.contract, scope.assumptions)
    project.apply(signed(project, Action.ASSESS, {"scope_root": scope.root, "candidate": plain(candidate)}))


def test_given_set_valued_whole_traces_when_replay_order_varies_then_no_positionwise_union(tmp_path):
    project = _create(tmp_path, _trace_task(2))
    _assess_trace(project)
    before = project.export_bytes()
    for order in itertools.permutations(("00", "11", "01")):
        allowed = set()
        for trace in order:
            if trace == "01":
                with pytest.raises(LacunaError, match="^TRACE_NOT_ALLOWED$"):
                    project.admit_observation("initial", OutcomeKind.ACCEPT, trace,
                                               expected_revision=project.state().revision)
            else:
                receipt = project.admit_observation("initial", OutcomeKind.ACCEPT, trace,
                                                    expected_revision=project.state().revision)
                assert receipt["code"] == "OBSERVATION_ALLOWED"
                allowed.add(trace)
        assert allowed == {"00", "11"}
    assert project.export_bytes() == before
    assert project.state().candidate.allowed == ((0, 3),)


def test_given_bound_k_evidence_when_extended_to_k_plus_one_then_old_receipt_cannot_promote(tmp_path):
    project = _create(tmp_path, _trace_task(2))
    _assess_trace(project)
    result = project.apply(signed(project, Action.COMPLETE, {
        "scope_root": project.state().task.scope.root, "candidate_root": project.status()["candidate_root"],
    }))
    assert result["evidence"] == "BOUNDED_SEARCH"
    old_revision = project.state().revision
    old_bundle = project.export_bytes()
    stale_completion = signed(project, Action.COMPLETE, {
        "scope_root": project.state().task.scope.root, "candidate_root": project.status()["candidate_root"],
    })
    project.apply(signed(project, Action.REVISE, {
        "scope_root": project.state().task.scope.root, "task": task_value(_trace_task(3)),
        "retired_protected": ["constant-trace"], "reason": "Extend full trace observation bound",
    }))
    before = project.export_bytes()
    with pytest.raises(LacunaError, match="STALE_ANSWER"):
        project.admit_observation("initial", OutcomeKind.ACCEPT, "00", expected_revision=old_revision)
    with pytest.raises(LacunaError, match="^STALE_ANSWER$"):
        project.apply(stale_completion)
    from src.zenolacuna.project import replay_bundle
    from tests.zenolacuna_project_helpers import public_key
    historical = replay_bundle(old_bundle, owner_key=public_key(), expected_revision=old_revision)
    assert historical["completion"]["model"]["history_bound"] == 2
    with pytest.raises(LacunaError, match="^STALE_BUNDLE$"):
        replay_bundle(old_bundle, owner_key=public_key(), expected_revision=project.state().revision)
    assert project.status()["workflow"] != "COMPLETE_FOR_SCOPE"
    assert project.export_bytes() == before
    _assess_trace(project)
    result = project.apply(signed(project, Action.COMPLETE, {
        "scope_root": project.state().task.scope.root, "candidate_root": project.status()["candidate_root"],
    }))
    assert result["evidence"] == "BOUNDED_SEARCH"
    assert result["completion"]["model"]["history_bound"] == 3


def test_given_narrowed_applicability_with_surviving_positive_when_retirement_unacknowledged_then_reject(tmp_path):
    from tests.zenolacuna_project_helpers import scope
    original = scope()
    rows = ((0,), (0,))
    kept = Requirement("positive-0", (0,), rows, ((0,), ()))
    lost = Requirement("positive-1", (1,), rows, ((), (0,)))
    original = replace(original, protected=(kept, lost), questions=(), contract=rows,
                       hypotheses=(Hypothesis("both-positives", rows),))
    project = _create(tmp_path, Task(original, RuntimeSpec("RELATION", (), ()), (), None, None))
    _assess_trace(project)
    project.apply(signed(project, Action.COMPLETE, {
        "scope_root": original.root, "candidate_root": project.status()["candidate_root"],
    }))
    state = project.state()
    narrowed = replace(state.task, scope=replace(state.task.scope, assumptions=(0,), protected=(kept,)))
    payload = {"scope_root": state.task.scope.root, "task": task_value(narrowed),
               "retired_protected": [], "reason": "Narrow the declared domain"}
    before = project.export_bytes()
    for incorrect in ([], ["positive-0"], ["unknown"]):
        payload["retired_protected"] = incorrect
        with pytest.raises(LacunaError, match="PROTECTED_REQUIREMENT_LOST"):
            project.apply(signed(project, Action.REVISE, payload))
        assert project.export_bytes() == before
    # Domain changes conservatively require acknowledging every prior clause,
    # even the one explicitly retained under the successor's smaller A.
    payload["retired_protected"] = ["positive-0", "positive-1"]
    project.apply(signed(project, Action.REVISE, payload))
    assert project.state().task.scope.assumptions == (0,)
    assert project.state().task.scope.protected[0].required[0] == (0,)
    assert project.state().task.scope.protected == (kept,)
    assert project.state().candidate is None and project.state().completion is None
    assert project.state().scope_revision != state.scope_revision
