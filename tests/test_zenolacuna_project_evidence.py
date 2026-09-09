"""Adversarial receipts and archived-source refinement, with independent tables."""

import hashlib
import json
import sqlite3
from dataclasses import replace

import pytest

from src.zenolacuna.authority import Action, Command, Delegation, encode_signed, sign
from src.zenolacuna.codec import encode
from src.zenolacuna.model import (
    Candidate,
    Hypothesis,
    LacunaError,
    Outcome,
    OutcomeKind,
    Profile,
    Requirement,
    Scope,
    SourceRef,
)
from src.zenolacuna.project import Project, replay_bundle
from src.zenolacuna.project_types import RuntimeSpec, Task, task_value
from tests.test_zenolacuna_project import answer, initialize, signed
from tests.zenolacuna_project_helpers import AGENT_SECRET, OWNER_SECRET, public_key, scope


def _create(tmp_path, task):
    project = Project(tmp_path / "run.sqlite", source_root=tmp_path, owner_key=public_key())
    project.apply(sign(Command("test-project", None, Action.INIT,
                              encode({"task": task_value(task), "checker_sha256": project.checker_sha256})), OWNER_SECRET))
    return project


def test_given_exact_scope_delegation_when_agent_answers_then_owner_can_revoke(tmp_path):
    original = scope()
    delegate = Delegation(public_key(AGENT_SECRET), original.root, (Action.ANSWER, Action.ASSESS, Action.COMPLETE))
    project = _create(tmp_path, Task(original, RuntimeSpec("RELATION", (), ()), (delegate,), None, None))
    project.apply(answer(project, secret=AGENT_SECRET))
    assert project.state().survivors == (0, 2)
    state = project.state()
    revision = {"scope_root": state.task.scope.root, "task": task_value(replace(state.task, delegates=())),
                "retired_protected": [], "reason": "Owner revokes agent"}
    before = project.export_bytes()
    with pytest.raises(LacunaError, match="UNAUTHORIZED"):
        project.apply(signed(project, Action.REVISE, revision, AGENT_SECRET))
    assert project.export_bytes() == before
    project.apply(signed(project, Action.REVISE, revision))
    assert project.state().survivors == (0, 1, 2)
    with pytest.raises(LacunaError, match="UNAUTHORIZED"):
        project.apply(answer(project, secret=AGENT_SECRET))


def test_given_valid_witness_when_admitted_then_all_premises_and_observations_bound(tmp_path):
    project = initialize(tmp_path)
    from src.zenolacuna.engine import analyze
    witness = analyze(project.state().task.scope).witness
    assert witness is not None
    before = project.export_bytes()
    receipt = project.admit_witness(witness, expected_revision=project.state().revision)
    assert receipt["status"] == "ACCEPTED"
    assert receipt["observations"][0] != receipt["observations"][1]
    assert receipt["scope_root"] == project.state().task.scope.root
    # A separate JSON construction is the oracle, including full requirement
    # records and complete tagged observations, rather than digest length.
    value = json.loads(encode(project.state().task.scope))
    def canonical(value):
        return (json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")
    expected_premises = hashlib.sha256(b"zenolacuna/witness-premises/v1\0" + canonical([
        value["assumptions"], value["contract"], value["protected"], value["hypotheses"],
    ])).hexdigest()
    assert receipt["premise_digest"] == expected_premises
    assert receipt["revision"] == project.state().revision
    assert receipt["sources"] == value["sources"]
    assert receipt["observations"] == [value["outcomes"][witness.left_outcome], value["outcomes"][witness.right_outcome]]
    body = {key: receipt[key] for key in ("revision", "scope_root", "witness", "premise_digest", "sources", "observations")}
    assert receipt["receipt_sha256"] == hashlib.sha256(canonical(body)).hexdigest()
    with pytest.raises(LacunaError, match="WITNESS_PREMISE_FAILED"):
        project.admit_witness(replace(witness, context=0), expected_revision=project.state().revision)
    assert project.export_bytes() == before


def _assess(project):
    candidate = Candidate("implementation", ((0,), (0,)), (0, 1))
    project.apply(signed(project, Action.ASSESS, {
        "scope_root": project.state().task.scope.root, "candidate": json.loads(encode(candidate)),
    }))


def test_given_signed_complete_request_when_fabricated_receipt_is_stored_then_replay_rejects(tmp_path):
    project = initialize(tmp_path)
    project.apply(answer(project))
    _assess(project)
    request = signed(project, Action.COMPLETE, {"scope_root": project.state().task.scope.root,
                                              "candidate_root": project.status()["candidate_root"]})
    # The signature authenticates the request, not this invented success flag.
    with sqlite3.connect(project.path) as db:
        count = db.execute("SELECT count(*) FROM events").fetchone()[0]
        db.execute("INSERT INTO events VALUES (?, ?, ?)",
                   (count, encode_signed(request), encode({"verified": True, "workflow": "COMPLETE_FOR_SCOPE"})))
    with pytest.raises(LacunaError, match="EVIDENCE_MISMATCH"):
        project.status()


def test_given_missing_solver_when_complete_request_forged_into_history_then_no_success(tmp_path):
    task = Task(scope(), RuntimeSpec("RELATION", (), ()), (), "1" * 64, None)
    project = _create(tmp_path, task)
    project.apply(answer(project))
    _assess(project)
    request = signed(project, Action.COMPLETE, {"scope_root": task.scope.root,
                                              "candidate_root": project.status()["candidate_root"]})
    before = project.export_bytes()
    with pytest.raises(LacunaError, match="SOLVER_UNKNOWN:TAU_MISSING"):
        project.apply(request)
    assert project.export_bytes() == before
    with sqlite3.connect(project.path) as db:
        db.execute("INSERT INTO events VALUES (3, ?, ?)", (encode_signed(request), encode({"tau": {"verified": True}})))
    with pytest.raises(LacunaError, match="SOLVER_UNKNOWN:TAU_MISSING"):
        project.status()


def _pipeline_task(tmp_path, raw=b"def transform(x):\n    return x\n"):
    path = tmp_path / "transform.py"
    path.write_bytes(raw)
    rows = ((0,), (1,), (2,), (3,))
    finite = Scope("two-bits", ("0", "1", "2", "3"),
                   tuple(Outcome(str(i), str(i), OutcomeKind.ACCEPT) for i in range(4)),
                   (0, 1, 2, 3), rows,
                   (Requirement("identity", (0, 1, 2, 3), rows, rows),),
                   (Hypothesis("identity", rows),), (),
                   (SourceRef("transform.py", hashlib.sha256(raw).hexdigest()),), Profile.REAL_OWNER)
    return Task(finite, RuntimeSpec("RESTRICTED_PIPELINE", (0, 1, 2, 3), ("return",)), (), None, None)


def _pipeline_assess(project):
    candidate = Candidate("proposed-source", ((0,), (1,), (2,), (3,)), (0, 1, 2, 3))
    project.apply(signed(project, Action.ASSESS, {"scope_root": project.state().task.scope.root,
                                               "candidate": json.loads(encode(candidate))}))
    return signed(project, Action.COMPLETE, {"scope_root": project.state().task.scope.root,
                                             "candidate_root": project.status()["candidate_root"]})


@pytest.mark.parametrize("raw,code", (
    (b"def transform(x):\n    return x ^ 1\n", "CODE_BUG:RUNTIME_MODEL_MISMATCH:proposed-source"),
    (b"import os\nos._exit(33)\n", "UNALLOWLISTED_SOURCE"),
))
def test_given_invalid_candidate_source_when_verified_then_no_code_runs_or_claim_commits(tmp_path, raw, code):
    project = _create(tmp_path, _pipeline_task(tmp_path, raw))
    request = _pipeline_assess(project)
    before = project.export_bytes()
    with pytest.raises(LacunaError, match=code):
        project.apply(request)
    assert project.export_bytes() == before


def test_given_complete_pipeline_when_source_is_revised_then_archive_replays_old_bytes(tmp_path):
    task = _pipeline_task(tmp_path)
    project = _create(tmp_path, task)
    project.apply(_pipeline_assess(project))
    old_revision = project.state().revision
    old_bundle = project.export_bytes()
    # Change only representation here; the owner must approve a new source root.
    new_raw = b"def transform(x):\n    return x ^ 0\n"
    (tmp_path / "transform.py").write_bytes(new_raw)
    with pytest.raises(LacunaError, match="SOURCE_DRIFT"):
        project.status()
    successor = replace(task, scope=replace(task.scope, sources=(SourceRef("transform.py", hashlib.sha256(new_raw).hexdigest()),)))
    command = Command("test-project", old_revision, Action.REVISE, encode({
        "scope_root": task.scope.root, "task": task_value(successor), "retired_protected": [],
        "reason": "Approve equivalent new source bytes",
    }))
    project.apply(sign(command, OWNER_SECRET))
    assert project.state().completion is None
    assert project.state().candidate is None
    assert replay_bundle(old_bundle, owner_key=public_key(), expected_revision=old_revision)["workflow"] == "COMPLETE_FOR_SCOPE"
    project.apply(_pipeline_assess(project))
    assert replay_bundle(project.export_bytes(), owner_key=public_key())["workflow"] == "COMPLETE_FOR_SCOPE"


def test_given_cancelled_project_and_changed_source_when_owner_revises_then_recovery_succeeds(tmp_path):
    task = _pipeline_task(tmp_path)
    project = _create(tmp_path, task)
    project.apply(signed(project, Action.CANCEL, {"scope_root": task.scope.root}))
    cancelled = project.state()
    new_raw = b"def transform(x):\n    return x ^ 0\n"
    (tmp_path / "transform.py").write_bytes(new_raw)
    successor = replace(task, scope=replace(task.scope, sources=(SourceRef("transform.py", hashlib.sha256(new_raw).hexdigest()),)))
    revision = Command("test-project", cancelled.revision, Action.REVISE, encode({
        "scope_root": task.scope.root, "task": task_value(successor), "retired_protected": [],
        "reason": "Recover into a newly approved source generation",
    }))
    project.apply(sign(revision, OWNER_SECRET))
    assert project.state().cancelled is False
    assert project.state().candidate is None


def test_given_unenumerated_domain_when_runtime_completion_requested_then_no_promotion(tmp_path):
    task = _pipeline_task(tmp_path)
    task = replace(task, runtime=replace(task.runtime, inputs=(0, 1)))
    project = _create(tmp_path, task)
    request = _pipeline_assess(project)
    before = project.export_bytes()
    with pytest.raises(LacunaError, match="UNENUMERATED_INPUT"):
        project.apply(request)
    assert project.export_bytes() == before
