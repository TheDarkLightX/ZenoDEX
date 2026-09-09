"""Signed task-to-runtime binding, including omitted and relabeled observations."""

from dataclasses import replace
from pathlib import Path

import pytest

from src.zenolacuna.authority import Action
from src.zenolacuna.model import LacunaError, OutcomeKind, Profile
from src.zenolacuna.project_types import RuntimeSpec, Task, plain
from src.zenolacuna.signal_migration import (
    OBSERVATIONS,
    CandidateMode,
    migration_candidate,
    migration_scope,
)
from tests.test_zenolacuna_project import signed
from tests.test_zenolacuna_project_evidence import _create

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize("mutation,code", (
    ("omit-auth-and-freshness", "MODEL_OMISSION"),
    ("relabel-rejection-kind", "RUNTIME_ENCODING_MISMATCH"),
    ("rename-context", "RUNTIME_ENCODING_MISMATCH"),
    ("omit-last-input", "UNENUMERATED_INPUT"),
))
def test_given_incomplete_or_relabeled_runtime_contract_when_inspected_or_completed_then_unknown_no_effect(tmp_path, mutation, code):
    scope = replace(migration_scope(ROOT), profile=Profile.REAL_OWNER)
    runtime = RuntimeSpec("SIGNAL_MIGRATION", tuple(range(128)), OBSERVATIONS)
    if mutation == "omit-auth-and-freshness":
        runtime = replace(runtime, observations=tuple(o for o in OBSERVATIONS if o not in ("auth_ok", "freshness_ok")))
    elif mutation == "relabel-rejection-kind":
        scope = replace(scope, outcomes=scope.outcomes[:2] + (replace(scope.outcomes[2], kind=OutcomeKind.ACCEPT),))
    elif mutation == "rename-context":
        scope = replace(scope, contexts=("different-semantics",) + scope.contexts[1:])
    else:
        runtime = replace(runtime, inputs=tuple(range(127)))
    for source in scope.sources:
        path = tmp_path / source.path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes((ROOT / source.path).read_bytes())
    project = _create(tmp_path, Task(scope, runtime, (), None, None))
    project.apply(signed(project, Action.ANSWER, {
        "scope_root": scope.root, "question": "migration-controller-policy", "answer": "GUARDED",
        "witness_root": project.status()["witness_root"],
    }))
    candidate = migration_candidate(CandidateMode.GUARDED)
    before = project.export_bytes()
    diagnosis = project.inspect_candidate(candidate)
    assert diagnosis["classification"] == "MODEL_OMISSION"
    assert diagnosis["code"] == code
    assert diagnosis["report"]["workflow"] == "INCONCLUSIVE"
    assert diagnosis["report"]["evidence"] == "UNKNOWN"
    assert project.export_bytes() == before
    # ASSESS records a model candidate; it grants no runtime completion.
    project.apply(signed(project, Action.ASSESS, {"scope_root": scope.root, "candidate": plain(candidate)}))
    before = project.export_bytes()
    with pytest.raises(LacunaError, match=f"^{code}$"):
        project.apply(signed(project, Action.COMPLETE, {
            "scope_root": scope.root, "candidate_root": project.status()["candidate_root"],
        }))
    status = project.status()
    assert (status["workflow"], status["evidence"], status["code"]) == ("INCONCLUSIVE", "UNKNOWN", code)
    assert status["completion"] is None
    assert project.export_bytes() == before
