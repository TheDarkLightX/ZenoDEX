"""Signed closure cannot bypass unresolved, empty or unobservable obligations."""

from dataclasses import replace

import pytest

from src.zenolacuna.authority import Action, decode_signed
from src.zenolacuna.codec import encode
from src.zenolacuna.model import Candidate, Hypothesis, LacunaError, OutcomeKind
from src.zenolacuna.project_types import RuntimeSpec, Task, plain
from tests.test_zenolacuna_project import answer, initialize, signed
from tests.test_zenolacuna_project_evidence import _create
from tests.zenolacuna_project_helpers import scope


def test_given_empty_family_when_owner_requests_complete_then_inconclusive_no_effect(tmp_path):
    task = Task(replace(scope(), hypotheses=(), questions=()), RuntimeSpec("RELATION", (), ()), (), None, None)
    project = _create(tmp_path, task)
    before = project.export_bytes()
    with pytest.raises(LacunaError, match="^EMPTY_H_CONFLICT$"):
        project.apply(signed(project, Action.COMPLETE, {"scope_root": task.scope.root, "candidate_root": "0" * 64}))
    assert project.status()["workflow"] == "INCONCLUSIVE"
    assert project.export_bytes() == before


def test_given_pending_decision_when_complete_or_outside_answer_arrives_then_no_effect(tmp_path):
    project = initialize(tmp_path)
    before = project.export_bytes()
    with pytest.raises(LacunaError, match="^MISSING_REQUIREMENT$"):
        project.apply(signed(project, Action.COMPLETE, {
            "scope_root": project.state().task.scope.root, "candidate_root": "0" * 64,
        }))
    with pytest.raises(LacunaError, match="^NEEDS_MODEL_REVISION$"):
        project.apply(answer(project, "outside-the-language"))
    assert project.status()["code"] == "MISSING_REQUIREMENT"
    assert project.export_bytes() == before


def test_given_reject_only_scope_when_complete_requested_then_positive_witness_required(tmp_path):
    original = scope()
    rows = ((1,), (1,))
    rejected = replace(original, protected=(), questions=(),
                       outcomes=tuple(replace(o, kind=OutcomeKind.REJECT) for o in original.outcomes),
                       contract=rows, hypotheses=(Hypothesis("reject-everything", rows),))
    project = _create(tmp_path, Task(rejected, RuntimeSpec("RELATION", (), ()), (), None, None))
    project.apply(signed(project, Action.ASSESS, {
        "scope_root": rejected.root, "candidate": plain(Candidate("reject-everything", rows, (0, 1))),
    }))
    before = project.export_bytes()
    with pytest.raises(LacunaError, match="^MISSING_POSITIVE_WITNESS$"):
        project.apply(signed(project, Action.COMPLETE, {
            "scope_root": rejected.root, "candidate_root": project.status()["candidate_root"],
        }))
    assert project.export_bytes() == before


def test_given_real_owner_project_when_simulated_receipt_substituted_then_no_effect(tmp_path):
    project = initialize(tmp_path)
    before = project.export_bytes()
    # The legacy receipt wire format has no signature; decoding never upgrades it.
    simulated = encode({"profile": "SIMULATED", "actor": "owner", "answer": "yes",
                        "scope_root": project.state().task.scope.root, "verified": True})
    with pytest.raises(LacunaError, match="^MALFORMED_APPROVAL$"):
        project.apply(decode_signed(simulated))
    assert project.export_bytes() == before
