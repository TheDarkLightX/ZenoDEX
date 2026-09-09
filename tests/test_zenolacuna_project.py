"""Signed workflow scenarios. Keys below are public test credentials only."""

import json
from dataclasses import replace

import pytest

from src.zenolacuna.authority import Action, Command, sign
from src.zenolacuna.codec import encode
from src.zenolacuna.model import Candidate, LacunaError, Profile
from src.zenolacuna.project import Project
from src.zenolacuna.project_types import RuntimeSpec, Task, task_value
from tests.zenolacuna_project_helpers import AGENT_SECRET, OWNER_SECRET, public_key, scope


def initialize(tmp_path):
    task = Task(scope(), RuntimeSpec("RELATION", (), ()), (), None, None)
    project = Project(tmp_path / "run.sqlite", source_root=tmp_path, owner_key=public_key())
    command = Command("test-project", None, Action.INIT,
                      encode({"task": task_value(task), "checker_sha256": project.checker_sha256}))
    project.apply(sign(command, OWNER_SECRET))
    return project


def signed(project, action, value, secret=OWNER_SECRET, parent=None):
    state = project.state()
    return sign(Command("test-project", state.revision if parent is None else parent,
                        action, encode(value)), secret)


def answer(project, value="yes", secret=OWNER_SECRET):
    status = project.status()
    return signed(project, Action.ANSWER, {
        "scope_root": status["scope_root"], "question": "choice", "answer": value,
        "witness_root": status["witness_root"],
    }, secret)


def test_given_owner_when_answering_then_all_compatible_interpretations_survive(tmp_path):
    project = initialize(tmp_path)
    decision = answer(project)
    project.apply(decision)
    assert project.state().survivors == (0, 2)
    snapshot = project.export_bytes()
    assert project.apply(decision)["code"] == "IDEMPOTENT_DUPLICATE"
    assert project.export_bytes() == snapshot
    # A fresh host instance reconstructs and verifies the actual signatures.
    reopened = Project(project.path, source_root=tmp_path, owner_key=public_key())
    assert reopened.state() == project.state()


def test_given_agent_without_delegation_when_answering_then_no_accepted_change(tmp_path):
    project = initialize(tmp_path)
    snapshot = project.export_bytes()
    with pytest.raises(LacunaError, match="UNAUTHORIZED"):
        project.apply(answer(project, secret=AGENT_SECRET))
    assert project.export_bytes() == snapshot


def test_given_old_answer_when_owner_revises_then_old_approval_is_stale(tmp_path):
    project = initialize(tmp_path)
    old = answer(project)
    state = project.state()
    successor = replace(state.task, scope=replace(state.task.scope, name="owner-contract-v2"))
    revision = signed(project, Action.REVISE, {
        "scope_root": state.task.scope.root, "task": task_value(successor),
        "retired_protected": [], "reason": "Clarify version ownership",
    })
    project.apply(revision)
    snapshot = project.export_bytes()
    with pytest.raises(LacunaError, match="STALE_ANSWER"):
        project.apply(old)
    assert project.export_bytes() == snapshot
    assert project.state().candidate is None


def test_given_changed_protected_clause_when_not_explicitly_retired_then_reject(tmp_path):
    project = initialize(tmp_path)
    state = project.state()
    successor = replace(state.task, scope=replace(state.task.scope, protected=()))
    value = {"scope_root": state.task.scope.root, "task": task_value(successor),
             "retired_protected": [], "reason": "Retire required positive"}
    snapshot = project.export_bytes()
    with pytest.raises(LacunaError, match="PROTECTED_REQUIREMENT_LOST"):
        project.apply(signed(project, Action.REVISE, value))
    assert project.export_bytes() == snapshot
    value["retired_protected"] = ["positive"]
    project.apply(signed(project, Action.REVISE, value))
    assert project.state().task.scope.protected == ()
    assert project.state().scope_revision != state.scope_revision


def test_given_owner_when_downgrading_real_profile_then_no_change(tmp_path):
    project = initialize(tmp_path)
    state = project.state()
    successor = replace(state.task, scope=replace(state.task.scope, profile=Profile.SIMULATED))
    snapshot = project.export_bytes()
    with pytest.raises(LacunaError, match="AUTHORIZATION_PROFILE_MISMATCH"):
        project.apply(signed(project, Action.REVISE, {
            "scope_root": state.task.scope.root, "task": task_value(successor),
            "retired_protected": [], "reason": "Downgrade request",
        }))
    assert project.export_bytes() == snapshot


def test_given_decided_contract_when_repair_and_complete_then_replay_saved_evidence(tmp_path):
    project = initialize(tmp_path)
    project.apply(answer(project))
    candidate = Candidate("implementation", ((0,), (0,)), (0, 1))
    project.apply(signed(project, Action.ASSESS, {
        "scope_root": project.state().task.scope.root, "candidate": json.loads(encode(candidate)),
    }))
    result = project.apply(signed(project, Action.COMPLETE, {
        "scope_root": project.state().task.scope.root,
        "candidate_root": project.status()["candidate_root"],
    }))
    assert result["workflow"] == "COMPLETE_FOR_SCOPE"
    assert result["claim"] == "FINITE_MODEL_ONLY"
    from src.zenolacuna.project import replay_bundle
    assert replay_bundle(project.export_bytes(), owner_key=public_key())["revision"] == result["revision"]
