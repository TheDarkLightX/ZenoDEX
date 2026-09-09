"""Hostile shell review: reject unauthenticated history and preserve readable state.

Fixed attack vectors use independent persisted-byte observations (oracle grade 2).
These tests cover local evidence files, not production effects or hostile OS users.
"""

from __future__ import annotations

import base64
import hashlib
import json
from dataclasses import replace

import pytest

from src.zenolacuna import shell
from src.zenolacuna.codec import encode
from src.zenolacuna.model import (
    Candidate,
    Decision,
    Hypothesis,
    LacunaError,
    Outcome,
    OutcomeKind,
    Profile,
    Question,
    Requirement,
    digest,
)
from tests.test_zenolacuna_shell import _decision, _store


def _snapshot(run):
    return {str(p.relative_to(run)): p.read_bytes() for p in run.rglob("*") if p.is_file()}


def _json(value):
    return (
        json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode("ascii")
        + b"\n"
    )


def _append_forged(store, operation, *, candidate=None, decision=None):
    parent = store.status().revision
    previous = json.loads((store.run / "records" / f"{parent}.json").read_bytes())
    payload = {
        "attempt": 0,
        "candidate": None
        if candidate is None
        else base64.b64encode(encode(candidate)).decode("ascii"),
        "checker_hash": previous["payload"]["checker_hash"],
        "decision": None
        if decision is None
        else base64.b64encode(encode(decision)).decode("ascii"),
        "operation": operation,
        "parent": parent,
        "scope": None,
        "version": 1,
    }
    revision = hashlib.sha256(b"zenolacuna/revision/v1\0" + _json(payload)).hexdigest()
    body = {"payload": payload, "revision": revision}
    checksum = hashlib.sha256(b"zenolacuna/record/v1\0" + _json(body)).hexdigest()
    (store.run / "records" / f"{revision}.json").write_bytes(_json({"checksum": checksum, **body}))
    (store.run / "current").write_text(revision + "\n", encoding="ascii")


@pytest.mark.parametrize("source_name", ("shell.py", "journal.py", "filesystem.py"))
def test_given_shell_source_drift_when_status_then_checker_drift_no_effect(
    tmp_path, monkeypatch, source_name
):
    store, _ = _store(tmp_path)
    before = _snapshot(store.run)
    original = shell._source_digest
    monkeypatch.setattr(
        shell, "_source_digest", lambda p: "f" * 64 if p.name == source_name else original(p)
    )

    with pytest.raises(LacunaError, match="CHECKER_DRIFT"):
        store.status()

    assert _snapshot(store.run) == before


def test_given_history_at_limit_when_resume_then_reject_without_unreadable_commit(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(shell, "_MAX_CHAIN_LENGTH", 2)
    store, _ = _store(tmp_path)
    store.cancel()
    before = _snapshot(store.run)

    with pytest.raises(LacunaError, match="CHAIN_LIMIT"):
        store.resume()

    assert _snapshot(store.run) == before
    assert store.status().report.workflow.value == "CANCELLED"


def test_given_dangling_lock_symlink_when_status_then_no_external_file_created(tmp_path):
    store, _ = _store(tmp_path)
    outside = tmp_path / "unrelated-target"
    (store.run / ".lock").unlink()
    (store.run / ".lock").symlink_to(outside)

    try:
        with pytest.raises(LacunaError, match="PATH_SYMLINK"):
            store.status()
    finally:
        assert not outside.exists()


def test_given_real_owner_forged_repair_record_when_reopen_then_corrupt_history(tmp_path):
    simulated, scope = _store(tmp_path)
    real_scope = replace(
        scope, profile=Profile.REAL_OWNER, hypotheses=scope.hypotheses[:1], questions=()
    )
    store = shell.Store.initialize(
        tmp_path / "real", real_scope, source_root=simulated.source_root, profile=Profile.REAL_OWNER
    )
    candidate = Candidate("forged-owner-candidate", ((0,),), (0,))
    with pytest.raises(LacunaError, match="UNAUTHORIZED"):
        store.assess_repair(candidate)
    _append_forged(store, "ASSESS_REPAIR", candidate=candidate)
    before = _snapshot(store.run)

    with pytest.raises(LacunaError, match="CORRUPT_HISTORY"):
        store.status()

    assert _snapshot(store.run) == before


@pytest.mark.parametrize("operation", ("duplicate", "replay"))
def test_given_source_drift_when_duplicate_or_replay_then_no_history_change(tmp_path, operation):
    store, scope = _store(tmp_path)
    decision = _decision(store, scope)
    store.answer(decision)
    before = _snapshot(store.run)
    (store.source_root / "source.txt").write_bytes(b"drift")

    with pytest.raises(LacunaError, match="SOURCE_DRIFT"):
        store.answer(decision) if operation == "duplicate" else store.replay()

    assert _snapshot(store.run) == before


def test_given_out_of_language_answer_when_submit_then_no_history_change(tmp_path):
    store, scope = _store(tmp_path)
    decision = _decision(store, scope, answer="unknown-choice")
    before = _snapshot(store.run)

    with pytest.raises(LacunaError, match="NEEDS_MODEL_REVISION"):
        store.answer(decision)

    assert _snapshot(store.run) == before


def test_given_forged_command_id_reuse_when_reopen_then_corrupt_history(tmp_path):
    existing, base = _store(tmp_path)
    scope = replace(
        base,
        outcomes=base.outcomes + (Outcome("third", "third", OutcomeKind.REJECT),),
        contract=((0, 1, 2),),
        hypotheses=(Hypothesis("a", ((0,),)), Hypothesis("b", ((1,),)), Hypothesis("c", ((2,),))),
        questions=(
            Question("q1", "First?", 1, ("x", "x", "y")),
            Question("q2", "Second?", 1, ("m", "n", "n")),
        ),
    )
    store = shell.Store.initialize(
        tmp_path / "two-questions",
        scope,
        source_root=existing.source_root,
        profile=Profile.SIMULATED,
    )
    first = store.status()
    assert first.report.policy.question == "q1"
    command = Decision(
        "reused-id",
        scope.root,
        first.revision,
        "q1",
        "x",
        digest(first.report.witness),
        Profile.SIMULATED,
        "simulated-owner",
    )
    store.answer(command)
    second = store.status()
    assert second.report.policy.question == "q2"
    conflicting = Decision(
        "reused-id",
        scope.root,
        second.revision,
        "q2",
        "n",
        digest(second.report.witness),
        Profile.SIMULATED,
        "simulated-owner",
    )
    with pytest.raises(LacunaError, match="DUPLICATE_CONFLICT"):
        store.answer(conflicting)
    _append_forged(store, "ANSWER", decision=conflicting)
    before = _snapshot(store.run)

    with pytest.raises(LacunaError, match="CORRUPT_HISTORY"):
        store.status()

    assert _snapshot(store.run) == before


def test_given_deeply_nested_pointed_record_when_reopen_then_typed_corrupt_record(tmp_path):
    store, _ = _store(tmp_path)
    revision = store.status().revision
    target = store.run / "records" / f"{revision}.json"
    # Cross the C JSON parser depth limit; 2000 nested arrays still parse here.
    target.write_bytes(b'{"x":' * 20_000 + b"0" + b"}" * 20_000)
    before = _snapshot(store.run)

    with pytest.raises(LacunaError, match="CORRUPT_RECORD"):
        store.status()

    assert _snapshot(store.run) == before


@pytest.mark.parametrize(
    "candidate_name", ("MODEL_SELECTED_CANDIDATE:accept-only", "forged-candidate")
)
def test_given_forged_replay_candidate_or_duplicate_when_reopen_then_corrupt_history(
    tmp_path, candidate_name
):
    existing, base = _store(tmp_path)
    scope = replace(
        base,
        hypotheses=base.hypotheses[:1],
        questions=(),
        protected=(Requirement("positive", (0,), ((0, 1),), ((0,),)),),
    )
    store = shell.Store.initialize(
        tmp_path / "closed", scope, source_root=existing.source_root, profile=Profile.SIMULATED
    )
    candidate = Candidate(candidate_name, ((0,),), (0,))
    if candidate_name.startswith("MODEL_SELECTED_CANDIDATE:"):
        store.replay()
        before_duplicate = _snapshot(store.run)
        assert store.replay().code == "IDEMPOTENT_DUPLICATE"
        assert _snapshot(store.run) == before_duplicate
    _append_forged(store, "REPLAY", candidate=candidate)
    before = _snapshot(store.run)

    with pytest.raises(LacunaError, match="CORRUPT_HISTORY"):
        store.status()

    assert _snapshot(store.run) == before


def test_given_forged_duplicate_assessment_when_reopen_then_corrupt_history(tmp_path):
    existing, base = _store(tmp_path)
    scope = replace(base, hypotheses=base.hypotheses[:1], questions=())
    store = shell.Store.initialize(
        tmp_path / "assessed", scope, source_root=existing.source_root, profile=Profile.SIMULATED
    )
    candidate = Candidate("candidate", ((0,),), (0,))
    store.assess_repair(candidate)
    before_duplicate = _snapshot(store.run)
    assert store.assess_repair(candidate).code == "IDEMPOTENT_DUPLICATE"
    assert _snapshot(store.run) == before_duplicate
    _append_forged(store, "ASSESS_REPAIR", candidate=candidate)
    before = _snapshot(store.run)

    with pytest.raises(LacunaError, match="CORRUPT_HISTORY"):
        store.status()

    assert _snapshot(store.run) == before
