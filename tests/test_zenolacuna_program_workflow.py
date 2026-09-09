"""BDD regressions for read-only restricted-program replay from a bound run."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from src.tau_workbench.programs import Program
from src.zenolacuna import shell
from src.zenolacuna.model import (
    Candidate,
    Decision,
    Hypothesis,
    LacunaError,
    Outcome,
    OutcomeKind,
    Profile,
    Question,
    Report,
    Requirement,
    Scope,
    SourceRef,
    digest,
)
from src.zenolacuna.shell import Store
from tools import zenolacuna

_IDENTITY = b"def transform(x): return x\n"
_FOURTH_INPUT_MUTANT = b"def transform(x): return 0 if x == 3 else x\n"


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _program_scope(
    source_digest: str | None, profile: Profile = Profile.SIMULATED
) -> tuple[Scope, Candidate]:
    identity = tuple((value,) for value in range(4))
    zero = ((0,), (0,), (0,), (0,))
    all_outcomes = tuple(tuple(range(4)) for _ in range(4))
    required = ((0,), (), (), ())
    scope = Scope(
        name="program-workflow",
        contexts=("0", "1", "2", "3"),
        outcomes=tuple(Outcome(str(value), str(value), OutcomeKind.ACCEPT) for value in range(4)),
        assumptions=(0, 1, 2, 3),
        contract=all_outcomes,
        protected=(Requirement("positive-at-zero", (0,), all_outcomes, required),),
        hypotheses=(
            Hypothesis("identity", identity),
            Hypothesis("zero", zero),
        ),
        questions=(Question("choose-program", "Which behavior?", 1, ("identity", "zero")),),
        sources=() if source_digest is None else (SourceRef("identity.py", source_digest),),
        profile=profile,
    )
    return scope, Candidate("identity-candidate", identity, (0, 1, 2, 3))


def _empty_scope() -> Scope:
    identity = tuple((value,) for value in range(4))
    return Scope(
        name="empty-program-workflow",
        contexts=("0", "1", "2", "3"),
        outcomes=tuple(Outcome(str(value), str(value), OutcomeKind.ACCEPT) for value in range(4)),
        assumptions=(0, 1, 2, 3),
        contract=identity,
        protected=(),
        hypotheses=(),
        questions=(),
    )


def _initialize(
    tmp_path: Path,
    *,
    source_bound: bool = True,
    profile: Profile = Profile.SIMULATED,
) -> tuple[Store, Scope, Candidate, Path]:
    source_root = tmp_path / "source-root"
    source_root.mkdir()
    source_path = source_root / "identity.py"
    source_path.write_bytes(_IDENTITY)
    scope, candidate = _program_scope(_sha256(_IDENTITY) if source_bound else None, profile)
    store = Store.initialize(
        tmp_path / "run",
        scope,
        source_root=source_root,
        profile=profile,
    )
    return store, scope, candidate, source_path


def _answer_identity(store: Store, scope: Scope) -> str:
    current = store.status()
    assert current.report.witness is not None
    decision = Decision(
        command_id="identity-decision",
        scope_root=scope.root,
        parent=current.revision,
        question="choose-program",
        answer="identity",
        witness_root=digest(current.report.witness),
        profile=scope.profile,
        actor="simulated-owner",
    )
    return store.answer(decision).revision


def _assessed_store(
    tmp_path: Path, *, source_bound: bool = True
) -> tuple[Store, Candidate, Path, str]:
    store, scope, candidate, source_path = _initialize(tmp_path, source_bound=source_bound)
    _answer_identity(store, scope)
    assessed = store.assess_repair(candidate)
    return store, candidate, source_path, assessed.revision


def _snapshot(store: Store) -> dict[str, bytes]:
    return {
        str(path.relative_to(store.run)): path.read_bytes()
        for path in store.run.rglob("*")
        if path.is_file()
    }


def _identity_program(path: Path) -> tuple[Program, ...]:
    return (Program("identity", path.read_bytes()),)


def test_given_accepted_answer_and_assessed_candidate_when_programs_replay_then_surviving_branch_is_checked(
    tmp_path: Path,
) -> None:
    store, _, source_path, revision = _assessed_store(tmp_path)
    before = _snapshot(store)

    result = store.check_programs(_identity_program(source_path), 2, expected_revision=revision)

    assert result.revision == revision
    assert result.status == "CHECKED"
    assert result.code == "RESTRICTED_PROGRAM_REPLAYED"
    assert result.report.survivors == (0,)
    assert result.report.authority == "NONE"
    assert _snapshot(store) == before
    assert store.status().revision == revision


def test_given_no_assessed_candidate_when_programs_replay_then_candidate_required_without_history_change(
    tmp_path: Path,
) -> None:
    store, scope, _, source_path = _initialize(tmp_path)
    revision = _answer_identity(store, scope)
    before = _snapshot(store)

    with pytest.raises(LacunaError) as raised:
        store.check_programs(_identity_program(source_path), 2, expected_revision=revision)

    assert raised.value.code == "CANDIDATE_REQUIRED"
    assert _snapshot(store) == before


def test_given_stale_revision_when_programs_replay_then_stale_revision_preserves_history(
    tmp_path: Path,
) -> None:
    store, _, source_path, revision = _assessed_store(tmp_path)
    stale_revision = store.run.joinpath("current").read_text(encoding="ascii").strip()
    assert stale_revision == revision
    before = _snapshot(store)

    with pytest.raises(LacunaError) as raised:
        store.check_programs(_identity_program(source_path), 2, expected_revision="0" * 64)

    assert raised.value.code == "STALE_REVISION"
    assert _snapshot(store) == before


def test_given_cancelled_run_when_programs_replay_then_cancelled_without_history_change(
    tmp_path: Path,
) -> None:
    store, _, source_path, _ = _assessed_store(tmp_path)
    cancelled = store.cancel()
    before = _snapshot(store)

    with pytest.raises(LacunaError) as raised:
        store.check_programs(
            _identity_program(source_path), 2, expected_revision=cancelled.revision
        )

    assert raised.value.code == "CANCELLED"
    assert _snapshot(store) == before


def test_given_real_owner_run_when_programs_replay_then_unavailable_authority_rejects(
    tmp_path: Path,
) -> None:
    store, _, _, source_path = _initialize(tmp_path, profile=Profile.REAL_OWNER)
    revision = store.status().revision
    before = _snapshot(store)

    with pytest.raises(LacunaError) as raised:
        store.check_programs(_identity_program(source_path), 2, expected_revision=revision)

    assert raised.value.code == "UNAUTHORIZED"
    assert _snapshot(store) == before


def test_given_runtime_program_mismatch_when_replayed_then_rejects_without_history_change(
    tmp_path: Path,
) -> None:
    store, _, _, revision = _assessed_store(tmp_path, source_bound=False)
    mutant = (Program("fourth_input_mutant", _FOURTH_INPUT_MUTANT),)
    before = _snapshot(store)

    with pytest.raises(LacunaError) as raised:
        store.check_programs(mutant, 2, expected_revision=revision)

    assert raised.value.code == "RUNTIME_MODEL_MISMATCH"
    assert _snapshot(store) == before


def test_given_source_drifts_during_program_replay_then_completion_is_not_returned(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    store, _, source_path, revision = _assessed_store(tmp_path)
    original_replay = shell.replay_pipeline

    def replay_then_drift(
        scope: Scope,
        survivors: tuple[int, ...],
        candidate: Candidate,
        programs: tuple[Program, ...],
        bits: int,
        inputs: tuple[int, ...],
    ) -> Report:
        report = original_replay(scope, survivors, candidate, programs, bits, inputs)
        source_path.write_bytes(_FOURTH_INPUT_MUTANT)
        return report

    monkeypatch.setattr(shell, "replay_pipeline", replay_then_drift)
    before = _snapshot(store)
    with pytest.raises(LacunaError) as raised:
        store.check_programs(_identity_program(source_path), 2, expected_revision=revision)

    assert raised.value.code == "SOURCE_DRIFT"
    assert _snapshot(store) == before
    source_path.write_bytes(_IDENTITY)
    assert store.status().revision == revision


def test_given_program_checker_drift_before_replay_then_bound_run_rejects(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    store, _, source_path, revision = _assessed_store(tmp_path)
    original_digest = shell._source_digest

    def changed_program_port(path: Path) -> str:
        if str(path).endswith("zenolacuna/ports/programs.py"):
            return "0" * 64
        return original_digest(path)

    monkeypatch.setattr(shell, "_source_digest", changed_program_port)
    before = _snapshot(store)
    with pytest.raises(LacunaError) as raised:
        store.check_programs(_identity_program(source_path), 2, expected_revision=revision)

    assert "ports/programs.py" in shell._CHECKER_FILES
    assert "../tau_workbench/programs.py" in shell._CHECKER_FILES
    assert raised.value.code == "CHECKER_DRIFT"
    assert _snapshot(store) == before


def test_given_program_checker_drifts_after_replay_then_completion_is_not_returned(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    store, _, source_path, revision = _assessed_store(tmp_path)
    original_replay = shell.replay_pipeline
    original_digest = shell._source_digest

    def replay_then_drift(
        scope: Scope,
        survivors: tuple[int, ...],
        candidate: Candidate,
        programs: tuple[Program, ...],
        bits: int,
        inputs: tuple[int, ...],
    ) -> Report:
        report = original_replay(scope, survivors, candidate, programs, bits, inputs)

        def changed_interpreter(path: Path) -> str:
            if str(path).endswith("../tau_workbench/programs.py"):
                return "f" * 64
            return original_digest(path)

        monkeypatch.setattr(shell, "_source_digest", changed_interpreter)
        return report

    monkeypatch.setattr(shell, "replay_pipeline", replay_then_drift)
    before = _snapshot(store)
    with pytest.raises(LacunaError) as raised:
        store.check_programs(_identity_program(source_path), 2, expected_revision=revision)

    assert raised.value.code == "CHECKER_DRIFT"
    assert _snapshot(store) == before


def test_given_empty_family_when_assessment_or_replay_runs_then_exact_empty_code_preserves_history(
    tmp_path: Path,
) -> None:
    source_root = tmp_path / "source-root"
    source_root.mkdir()
    store = Store.initialize(
        tmp_path / "run",
        _empty_scope(),
        source_root=source_root,
        profile=Profile.SIMULATED,
    )
    candidate = Candidate("identity", tuple((value,) for value in range(4)), (0, 1, 2, 3))
    before = _snapshot(store)

    with pytest.raises(LacunaError) as assessment:
        store.assess_repair(candidate)
    with pytest.raises(LacunaError) as replay:
        store.replay()

    assert assessment.value.code == "EMPTY_H_CONFLICT"
    assert replay.value.code == "EMPTY_H_CONFLICT"
    assert _snapshot(store) == before


def test_given_run_selector_when_cli_replays_programs_then_result_is_read_only_json(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    store, _, source_path, revision = _assessed_store(tmp_path)
    before = _snapshot(store)

    assert (
        zenolacuna.main(
            (
                "check-programs",
                "--run",
                str(store.run),
                "--expected-revision",
                revision,
                "--bits",
                "2",
                "--program",
                str(source_path),
                "--source-root",
                str(store.source_root),
            )
        )
        == 0
    )
    result = json.loads(capsys.readouterr().out)
    assert result["revision"] == revision
    assert result["status"] == "CHECKED"
    assert result["code"] == "RESTRICTED_PROGRAM_REPLAYED"
    assert _snapshot(store) == before

    assert (
        zenolacuna.main(
            (
                "check-programs",
                "--run",
                str(store.run),
                "--candidate",
                str(tmp_path / "candidate.json"),
                "--expected-revision",
                revision,
                "--bits",
                "2",
                "--program",
                str(source_path),
                "--source-root",
                str(store.source_root),
            )
        )
        == 2
    )
    assert json.loads(capsys.readouterr().out) == {
        "code": "INVALID_ARGUMENT",
        "status": "REJECTED",
    }


def test_given_invalid_bits_when_programs_replay_then_range_is_rejected_before_history_changes(
    tmp_path: Path,
) -> None:
    store, _, source_path, revision = _assessed_store(tmp_path)
    before = _snapshot(store)

    with pytest.raises(LacunaError) as raised:
        store.check_programs(_identity_program(source_path), 0, expected_revision=revision)

    assert raised.value.code == "INVALID_INTEGER"
    assert _snapshot(store) == before
