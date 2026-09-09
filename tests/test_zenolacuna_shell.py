"""Stateful regressions for the finite ZenoLacuna persistence boundary."""

from __future__ import annotations

import hashlib
import json

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
    Scope,
    SourceRef,
    digest,
)
from src.zenolacuna.shell import Store
from tools import zenolacuna


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _scope(source_digest: str, profile: Profile = Profile.SIMULATED) -> Scope:
    return Scope(
        name="shell-scope",
        contexts=("context",),
        outcomes=(
            Outcome("accept", "accepted", OutcomeKind.ACCEPT),
            Outcome("reject", "rejected", OutcomeKind.REJECT),
        ),
        assumptions=(0,),
        contract=((0, 1),),
        protected=(),
        hypotheses=(
            # The question resolves two valid, observationally distinct models.
            Hypothesis("accept-only", ((0,),)),
            Hypothesis("reject-only", ((1,),)),
        ),
        questions=(Question("choose-model", "Which model?", 1, ("accept", "reject")),),
        sources=(SourceRef("source.txt", source_digest),),
        profile=profile,
    )


def _large_low_budget_scope(source_digest: str) -> Scope:
    domain = 64
    relation = tuple((0,) for _ in range(domain))
    return Scope(
        name="large-low-budget-scope",
        contexts=tuple(f"context-{index}" for index in range(domain)),
        outcomes=tuple(
            Outcome(f"outcome-{index}", f"observation-{index}", OutcomeKind.ACCEPT)
            for index in range(domain)
        ),
        assumptions=tuple(range(domain)),
        contract=relation,
        protected=(),
        hypotheses=tuple(Hypothesis(f"hypothesis-{index}", relation) for index in range(64)),
        questions=(),
        sources=(SourceRef("source.txt", source_digest),),
        max_work=1,
    )


def _store(tmp_path, profile: Profile = Profile.SIMULATED) -> tuple[Store, Scope]:
    source_root = tmp_path / "source-root"
    source_root.mkdir()
    source_bytes = b"frozen source bytes\n"
    (source_root / "source.txt").write_bytes(source_bytes)
    scope = _scope(_sha256(source_bytes), profile)
    run = tmp_path / "run"
    store = Store.initialize(run, scope, source_root=source_root, profile=profile)
    return store, scope


def _decision(store: Store, scope: Scope, *, command_id: str = "command-1", answer: str = "accept", actor: str = "simulated-owner") -> Decision:
    result = store.status()
    assert result.report.policy.question == "choose-model"
    assert result.report.witness is not None
    return Decision(
        command_id=command_id,
        scope_root=scope.root,
        parent=result.revision,
        question="choose-model",
        answer=answer,
        witness_root=digest(result.report.witness),
        profile=scope.profile,
        actor=actor,
    )


def _code(exc: pytest.ExceptionInfo[LacunaError]) -> str:
    return exc.value.code


def _run_snapshot(store: Store) -> dict[str, bytes]:
    return {
        "current": (store.run / "current").read_bytes(),
        **{
            f"records/{path.name}": path.read_bytes()
            for path in sorted((store.run / "records").iterdir())
        },
    }


def test_given_source_drift_when_status_then_rejects_without_pointer_change(tmp_path) -> None:
    store, _ = _store(tmp_path)
    before = store.status().revision
    (tmp_path / "source-root" / "source.txt").write_bytes(b"changed")

    with pytest.raises(LacunaError) as error:
        store.status()

    assert _code(error) == "SOURCE_DRIFT"
    assert (tmp_path / "run" / "current").read_text(encoding="ascii").strip() == before


def test_given_unlisted_actor_when_answer_then_unauthorized_and_no_revision(tmp_path) -> None:
    store, scope = _store(tmp_path)
    before = store.status().revision
    decision = _decision(store, scope, actor="proposal-agent")

    with pytest.raises(LacunaError) as error:
        store.answer(decision, encode(decision))

    assert _code(error) == "UNAUTHORIZED"
    assert store.status().revision == before


def test_given_identical_and_conflicting_duplicates_then_one_effect_and_stable_codes(tmp_path) -> None:
    store, scope = _store(tmp_path)
    decision = _decision(store, scope)
    raw = encode(decision)
    accepted = store.answer(decision, raw)
    duplicate = store.answer(decision, raw)

    assert accepted.code == "ACCEPTED"
    assert duplicate.code == "IDEMPOTENT_DUPLICATE"
    assert duplicate.revision == accepted.revision

    conflicting = Decision(
        command_id="command-2",
        scope_root=decision.scope_root,
        parent=decision.parent,
        question=decision.question,
        answer="reject",
        witness_root=decision.witness_root,
        profile=decision.profile,
        actor=decision.actor,
    )
    with pytest.raises(LacunaError) as error:
        store.answer(conflicting, encode(conflicting))

    assert _code(error) == "DUPLICATE_CONFLICT"
    assert store.status().revision == accepted.revision


def test_given_cancelled_run_when_late_answer_then_stale_and_resume_requires_new_revision(tmp_path) -> None:
    store, scope = _store(tmp_path)
    late = _decision(store, scope)
    before_cancel = store.status().revision
    cancelled = store.cancel()

    assert cancelled.report.workflow.value == "CANCELLED"
    assert cancelled.revision != before_cancel
    with pytest.raises(LacunaError) as error:
        store.answer(late, encode(late))
    assert _code(error) == "STALE_ANSWER"

    resumed = store.resume()
    assert resumed.revision != cancelled.revision
    assert resumed.report.workflow.value == "NEEDS_DECISION"


def test_given_fault_before_pointer_when_reopened_then_previous_revision_is_current(tmp_path) -> None:
    store, _ = _store(tmp_path)
    before = store.status().revision

    def fail_before_pointer(point: str) -> None:
        if point == "before_pointer":
            raise OSError("injected")

    faulting = Store(
        store.run,
        source_root=tmp_path / "source-root",
        profile=Profile.SIMULATED,
        fault_hook=fail_before_pointer,
    )
    with pytest.raises(LacunaError) as error:
        faulting.cancel()
    assert _code(error) == "PERSISTENCE_FAILURE"

    recovered = Store(store.run, source_root=tmp_path / "source-root", profile=Profile.SIMULATED)
    result = recovered.status()
    assert result.revision == before
    assert result.report.workflow.value == "NEEDS_DECISION"


def test_given_history_byte_budget_at_exact_boundary_then_read_and_commit_are_bounded(
    tmp_path, monkeypatch
) -> None:
    store, scope = _store(tmp_path)
    chain = store._read_chain()
    parent = chain.records[-1].revision
    next_record = shell._record_for(
        parent,
        "CANCEL",
        scope_bytes=None,
        decision_bytes=None,
        candidate_bytes=None,
        checker_hash=chain.records[-1].checker_hash,
        attempt=0,
    )
    next_cost = shell._record_byte_cost(next_record, len(shell._record_bytes(next_record)))

    monkeypatch.setattr(shell, "_MAX_HISTORY_BYTES", chain.byte_cost)
    assert store.status().revision == parent
    before = _run_snapshot(store)
    with pytest.raises(LacunaError) as rejected:
        store.cancel()
    assert _code(rejected) == "HISTORY_BUDGET_EXCEEDED"
    assert _run_snapshot(store) == before

    monkeypatch.setattr(shell, "_MAX_HISTORY_BYTES", chain.byte_cost + next_cost)
    accepted = store.cancel()
    assert accepted.revision != parent
    assert store._read_chain().byte_cost == chain.byte_cost + next_cost
    assert store.status().revision == accepted.revision


def test_given_history_core_work_at_exact_boundary_then_no_extra_revision_is_accepted(
    tmp_path, monkeypatch
) -> None:
    store, scope = _store(tmp_path)
    exact_work = shell.Store._history_work_charge(scope) * shell._HISTORY_REBUILD_WORK_FACTOR
    monkeypatch.setattr(shell, "_MAX_HISTORY_CORE_WORK", exact_work)
    assert store.status().report.workflow.value == "NEEDS_DECISION"
    before = _run_snapshot(store)

    with pytest.raises(LacunaError) as rejected:
        store.cancel()
    assert _code(rejected) == "HISTORY_BUDGET_EXCEEDED"
    assert _run_snapshot(store) == before

    monkeypatch.setattr(shell, "_MAX_HISTORY_CORE_WORK", exact_work * 2)
    accepted = store.cancel()
    assert accepted.report.workflow.value == "CANCELLED"
    assert store.status().revision == accepted.revision


def test_given_large_low_declared_work_when_history_grows_then_preprocessing_charge_blocks_it(
    tmp_path, monkeypatch
) -> None:
    source_root = tmp_path / "source-root"
    source_root.mkdir()
    source = b"frozen source bytes\n"
    (source_root / "source.txt").write_bytes(source)
    scope = _large_low_budget_scope(_sha256(source))
    charge = shell.Store._history_work_charge(scope)
    assert charge > scope.max_work
    monkeypatch.setattr(
        shell,
        "_MAX_HISTORY_CORE_WORK",
        charge * shell._HISTORY_REBUILD_WORK_FACTOR,
    )
    store = Store.initialize(
        tmp_path / "run",
        scope,
        source_root=source_root,
        profile=Profile.SIMULATED,
    )
    before = _run_snapshot(store)

    with pytest.raises(LacunaError) as rejected:
        store.cancel()

    assert _code(rejected) == "HISTORY_BUDGET_EXCEEDED"
    assert _run_snapshot(store) == before


def test_given_source_mutates_before_pointer_then_old_revision_remains_current(tmp_path) -> None:
    store, _ = _store(tmp_path)
    before = store.status().revision
    source = store.source_root / "source.txt"
    original = source.read_bytes()

    def mutate_before_pointer(point: str) -> None:
        if point == "before_pointer":
            source.write_bytes(b"changed after record write")

    faulting = Store(
        store.run,
        source_root=store.source_root,
        profile=Profile.SIMULATED,
        fault_hook=mutate_before_pointer,
    )
    with pytest.raises(LacunaError) as rejected:
        faulting.cancel()
    assert _code(rejected) == "SOURCE_DRIFT"
    assert (store.run / "current").read_text(encoding="ascii").strip() == before

    source.write_bytes(original)
    recovered = Store(store.run, source_root=store.source_root, profile=Profile.SIMULATED)
    assert recovered.status().revision == before


def test_given_checker_changes_before_pointer_then_old_revision_remains_current(tmp_path, monkeypatch) -> None:
    store, _ = _store(tmp_path)
    before = store.status().revision
    original_digest = shell._checker_digest

    def mutate_checker_before_pointer(point: str) -> None:
        if point == "before_pointer":
            monkeypatch.setattr(shell, "_checker_digest", lambda: "0" * 64)

    faulting = Store(
        store.run,
        source_root=store.source_root,
        profile=Profile.SIMULATED,
        fault_hook=mutate_checker_before_pointer,
    )
    with pytest.raises(LacunaError) as rejected:
        faulting.cancel()
    assert _code(rejected) == "CHECKER_DRIFT"
    assert (store.run / "current").read_text(encoding="ascii").strip() == before

    monkeypatch.setattr(shell, "_checker_digest", original_digest)
    recovered = Store(store.run, source_root=store.source_root, profile=Profile.SIMULATED)
    assert recovered.status().revision == before


def test_given_corrupt_pointed_record_when_reopened_then_no_fallback(tmp_path) -> None:
    store, _ = _store(tmp_path)
    revision = store.status().revision
    (store.run / "records" / f"{revision}.json").write_bytes(b"{}")

    with pytest.raises(LacunaError) as error:
        Store(store.run, source_root=tmp_path / "source-root", profile=Profile.SIMULATED).status()

    assert _code(error) == "CORRUPT_RECORD"


def test_given_profile_mismatch_or_unavailable_real_owner_then_no_decision_mutates(tmp_path) -> None:
    source_root = tmp_path / "source-root"
    source_root.mkdir()
    source_bytes = b"source"
    (source_root / "source.txt").write_bytes(source_bytes)
    simulated_scope = _scope(_sha256(source_bytes), Profile.SIMULATED)

    with pytest.raises(LacunaError) as mismatch:
        Store.initialize(tmp_path / "mismatch", simulated_scope, source_root=source_root, profile=Profile.REAL_OWNER)
    assert _code(mismatch) == "AUTHORIZATION_PROFILE_MISMATCH"

    real_scope = _scope(_sha256(source_bytes), Profile.REAL_OWNER)
    real_store = Store.initialize(tmp_path / "real", real_scope, source_root=source_root, profile=Profile.REAL_OWNER)
    report = real_store.status()
    assert report.report.witness is not None
    decision = Decision(
        command_id="real-command",
        scope_root=real_scope.root,
        parent=report.revision,
        question="choose-model",
        answer="accept",
        witness_root=digest(report.report.witness),
        profile=Profile.REAL_OWNER,
        actor="real-owner",
    )
    with pytest.raises(LacunaError) as unauthorized:
        real_store.answer(decision, encode(decision))
    assert _code(unauthorized) == "UNAUTHORIZED"


def test_assess_repair_persists_only_valid_candidate_after_resolution(tmp_path) -> None:
    store, scope = _store(tmp_path)
    unresolved_candidate = Candidate("candidate", ((0,),), (0,))
    before = store.status().revision
    with pytest.raises(LacunaError) as unresolved:
        store.assess_repair(unresolved_candidate, encode(unresolved_candidate))
    assert _code(unresolved) == "NEEDS_DECISION"
    assert store.status().revision == before

    decision = _decision(store, scope)
    store.answer(decision, encode(decision))
    repaired = store.assess_repair(unresolved_candidate, encode(unresolved_candidate))
    assert repaired.code == "REPAIR_ASSESSED"
    assert repaired.revision == store.status().revision


def test_given_cli_lifecycle_when_scope_and_bound_answer_are_supplied_then_json_is_stable(
    tmp_path, capsys
) -> None:
    source_root = tmp_path / "source-root"
    source_root.mkdir()
    source_bytes = b"frozen source bytes\n"
    (source_root / "source.txt").write_bytes(source_bytes)
    scope = _scope(_sha256(source_bytes))
    task = tmp_path / "task.json"
    task.write_bytes(encode(scope))
    run = tmp_path / "run"

    assert (
        zenolacuna.main(
            (
                "analyze",
                "--task",
                str(task),
                "--out",
                str(run),
                "--source-root",
                str(source_root),
            )
        )
        == 0
    )
    analyzed = json.loads(capsys.readouterr().out)
    assert analyzed["status"] == "STATUS"
    assert analyzed["report"]["workflow"] == "NEEDS_DECISION"
    assert analyzed["report"]["pending_question"] == {
        "answers": ["accept", "reject"],
        "cost": 1,
        "name": "choose-model",
        "prompt": "Which model?",
    }

    store = Store(run, source_root=source_root, profile=Profile.SIMULATED)
    decision = _decision(store, scope, command_id="cli-command")
    decision_path = tmp_path / "decision.json"
    decision_path.write_bytes(encode(decision))
    assert (
        zenolacuna.main(
            (
                "answer",
                "--run",
                str(run),
                "--decision",
                str(decision_path),
                "--source-root",
                str(source_root),
            )
        )
        == 0
    )
    answered = json.loads(capsys.readouterr().out)
    assert answered["code"] == "ACCEPTED"
    assert answered["status"] == "ACCEPTED"
    assert answered["revision"] != analyzed["revision"]


def test_given_describe_when_parser_changes_then_command_registry_matches_cli(tmp_path, capsys) -> None:
    parser = zenolacuna._parser()
    assert zenolacuna.main(("describe", "--source-root", str(tmp_path))) == 0
    described = json.loads(capsys.readouterr().out)
    assert described["commands"] == list(zenolacuna._command_names(parser))
    assert described["persistence"] == "COOPERATIVE_LOCAL_FILESYSTEM"


def test_given_real_scope_in_simulated_program_check_then_profile_mismatch_is_rejected(
    tmp_path, capsys
) -> None:
    task = tmp_path / "real-task.json"
    task.write_bytes(encode(_scope("0" * 64, Profile.REAL_OWNER)))

    assert (
        zenolacuna.main(
            (
                "check-programs",
                "--task",
                str(task),
                "--candidate",
                str(tmp_path / "not-read.json"),
                "--bits",
                "1",
                "--program",
                str(tmp_path / "not-read.py"),
            )
        )
        == 2
    )
    assert json.loads(capsys.readouterr().out) == {
        "code": "AUTHORIZATION_PROFILE_MISMATCH",
        "status": "REJECTED",
    }
    assert (
        zenolacuna.main(
            (
                "check-programs",
                "--profile",
                "REAL_OWNER",
                "--task",
                str(task),
                "--candidate",
                str(tmp_path / "not-read.json"),
                "--bits",
                "1",
                "--program",
                str(tmp_path / "not-read.py"),
            )
        )
        == 2
    )
    assert json.loads(capsys.readouterr().out) == {
        "code": "UNAUTHORIZED",
        "status": "REJECTED",
    }
