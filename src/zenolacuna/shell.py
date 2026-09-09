"""Filesystem shell for the bounded, finite ZenoLacuna profile.

The authoritative relation checker stays in the pure core. This module owns
source binding, append-only persistence, lifecycle serialization, and nothing
that can grant a real-owner decision authority.

It assumes a cooperative local filesystem. It uses lstat/O_NOFOLLOW and flock
for its own writers. A same-host principal able to replace directories lies
outside this bounded local profile.
"""

from __future__ import annotations

import fcntl
import hashlib
import os
import stat
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Final, NoReturn

from src.tau_workbench.programs import Program

from .check import close_model
from .codec import decode_candidate, decode_decision, decode_scope, encode
from .engine import analyze, assess_repair
from .filesystem import (
    _MAX_SOURCE_BYTES,
    _checked_directory,
    _path_stat,
    _read_regular,
    _source_digest,
)
from .journal import (
    _MAX_ATTEMPTS,
    _MAX_RECORD_BYTES,
    _is_digest,
    _Record,
    _record_byte_cost,
    _record_bytes,
    _record_for,
    _record_from_bytes,
)
from .model import (
    Candidate,
    Decision,
    LacunaError,
    Profile,
    Report,
    Scope,
    Workflow,
    digest,
    exact_int,
)
from .ports.programs import replay_pipeline
from .questions import filter_answer

FaultHook = Callable[[str], None]

_NO_WITNESS_PREFIX: Final = b"zenolacuna/v1/no-witness\x00"
_NO_WITNESS_ROOT: Final = hashlib.sha256(_NO_WITNESS_PREFIX).hexdigest()
_SIMULATED_ACTOR: Final = "simulated-owner"
_CHECKER_FILES: Final = (
    "model.py",
    "relations.py",
    "questions.py",
    "engine.py",
    "check.py",
    "codec.py",
    "shell.py",
    "journal.py",
    "filesystem.py",
    "ports/programs.py",
    "../tau_workbench/programs.py",
)
_MAX_CHAIN_LENGTH: Final = 1_024
_MAX_HISTORY_BYTES: Final = 32 * 1024 * 1024
_MAX_HISTORY_CORE_WORK: Final = 64 * 1_000_000
_HISTORY_REBUILD_WORK_FACTOR: Final = 4


@dataclass(frozen=True, slots=True)
class ShellResult:
    """A freshly recomputed report bound to the current persisted revision."""

    revision: str
    report: Report
    status: str
    code: str


@dataclass(frozen=True, slots=True)
class _Chain:
    records: tuple[_Record, ...]
    byte_cost: int


@dataclass(frozen=True, slots=True)
class _DecisionBinding:
    decision: Decision
    raw: bytes


@dataclass(frozen=True, slots=True)
class _State:
    scope: Scope
    survivors: tuple[int, ...]
    candidate: Candidate | None
    candidate_bytes: bytes | None
    completed_candidate: Candidate | None
    cancelled: bool
    decisions: tuple[_DecisionBinding, ...]
    checker_hash: str


def _raise(code: str) -> NoReturn:
    raise LacunaError(code)


def _require_ready_for_replay(report: Report) -> None:
    """Reject a non-ready finite report without erasing its diagnostic."""

    if report.workflow is Workflow.READY_FOR_REPLAY:
        return
    if report.workflow is Workflow.NEEDS_DECISION:
        _raise("NEEDS_DECISION")
    _raise(report.code)


def _checker_digest() -> str:
    package = _checked_directory(Path(__file__).parent, "CHECKER_SOURCE_MISSING")
    result = hashlib.sha256(b"zenolacuna/checker-package/v1\x00")
    for name in _CHECKER_FILES:
        path = package / name
        details = _path_stat(path, "CHECKER_SOURCE_MISSING")
        if not stat.S_ISREG(details.st_mode) or details.st_size > _MAX_SOURCE_BYTES:
            _raise("CHECKER_SOURCE_MISSING")
        result.update(name.encode("ascii") + b"\x00" + _source_digest(path).encode("ascii"))
    return result.hexdigest()


class Store:
    """Typed boundary for one local append-only ZenoLacuna run.

    `REAL_OWNER` deliberately has no locally callable approval port. Therefore
    no answer or candidate mutation can be committed under that profile.
    """

    def __init__(
        self,
        run: str | Path,
        *,
        source_root: str | Path,
        profile: Profile,
        fault_hook: FaultHook | None = None,
    ) -> None:
        if type(profile) is not Profile:
            _raise("INVALID_PROFILE")
        self.run = Path(os.path.abspath(os.fspath(run)))
        self.source_root = Path(os.path.abspath(os.fspath(source_root)))
        self.profile = profile
        self.fault_hook = fault_hook

    @classmethod
    def initialize(
        cls,
        run: str | Path,
        scope: Scope,
        *,
        source_root: str | Path,
        profile: Profile,
        fault_hook: FaultHook | None = None,
    ) -> Store:
        store = cls(run, source_root=source_root, profile=profile, fault_hook=fault_hook)
        try:
            store._require_profile(scope)
            store._verify_sources(scope)
            checker_hash = _checker_digest()
            with store._locked(create=True):
                store._require_profile(scope)
                store._verify_sources(scope)
                store._reject_existing_run()
                scope_bytes = encode(scope)
                store._require_history_work(1, scope)
                analyze(decode_scope(scope_bytes))
                record = store._commit(
                    _Chain((), 0),
                    None,
                    "INIT",
                    scope_bytes=scope_bytes,
                    decision_bytes=None,
                    candidate_bytes=None,
                    checker_hash=checker_hash,
                    scope=scope,
                )
                store._apply_initial(record)
                return store
        except LacunaError:
            raise
        except OSError as exc:
            raise LacunaError("PERSISTENCE_FAILURE") from exc

    def answer(self, decision: Decision, raw_decision: bytes | None = None) -> ShellResult:
        try:
            with self._locked():
                state, revision, chain = self._load_bound_state()
                self._authorize_decision(state.scope, decision)
                raw = self._decision_bytes(decision, raw_decision)
                duplicate = self._duplicate_result(state, revision, raw, decision)
                if duplicate is not None:
                    return duplicate
                self._require_history_work(len(chain.records) + 1, state.scope)
                next_state = self._answer_state(state, revision, decision, raw)
                record = self._commit(
                    chain,
                    revision,
                    "ANSWER",
                    scope_bytes=None,
                    decision_bytes=raw,
                    candidate_bytes=None,
                    checker_hash=state.checker_hash,
                    scope=state.scope,
                )
                return self._result(record.revision, next_state, "ACCEPTED", "ACCEPTED")
        except LacunaError:
            raise
        except OSError as exc:
            raise LacunaError("PERSISTENCE_FAILURE") from exc

    def assess_repair(
        self,
        candidate: Candidate,
        raw_candidate: bytes | None = None,
    ) -> ShellResult:
        try:
            with self._locked():
                state, revision, chain = self._load_bound_state()
                self._authorize_candidate_mutation(state.scope)
                if state.cancelled:
                    _raise("STALE_ANSWER")
                raw = self._candidate_bytes(candidate, raw_candidate)
                report = self._report(state)
                _require_ready_for_replay(report)
                if state.candidate_bytes == raw:
                    return self._result(revision, state, "ACCEPTED", "IDEMPOTENT_DUPLICATE")
                self._require_history_work(len(chain.records) + 1, state.scope)
                assessment = assess_repair(state.scope, state.survivors, candidate)
                if assessment.workflow is not Workflow.READY_FOR_REPLAY:
                    _raise(assessment.code)
                next_state = replace(
                    state,
                    candidate=candidate,
                    candidate_bytes=raw,
                    completed_candidate=None,
                )
                record = self._commit(
                    chain,
                    revision,
                    "ASSESS_REPAIR",
                    scope_bytes=None,
                    decision_bytes=None,
                    candidate_bytes=raw,
                    checker_hash=state.checker_hash,
                    scope=state.scope,
                )
                return self._result(record.revision, next_state, "ACCEPTED", "REPAIR_ASSESSED")
        except LacunaError:
            raise
        except OSError as exc:
            raise LacunaError("PERSISTENCE_FAILURE") from exc

    def replay(self) -> ShellResult:
        """Recompute closure; a non-complete replay is deliberately unpersisted.

        With no assessed candidate, the selected surviving relation is encoded as
        a `MODEL_SELECTED_CANDIDATE` record only if the checker reaches complete
        finite closure. It is a model candidate, never a runtime adapter choice.
        """

        try:
            with self._locked():
                state, revision, chain = self._load_bound_state()
                self._require_profile(state.scope)
                if state.cancelled:
                    _raise("CANCELLED")
                if state.completed_candidate is not None:
                    return self._result(revision, state, "ACCEPTED", "IDEMPOTENT_DUPLICATE")
                report = analyze(state.scope, state.survivors)
                _require_ready_for_replay(report)
                self._require_history_work(len(chain.records) + 1, state.scope)
                candidate, raw = self._replay_candidate(state)
                replayed = close_model(state.scope, state.survivors, candidate)
                if replayed.workflow is not Workflow.COMPLETE_FOR_SCOPE:
                    return ShellResult(revision, replayed, "INCONCLUSIVE", replayed.code)
                next_state = replace(
                    state,
                    completed_candidate=candidate,
                )
                record = self._commit(
                    chain,
                    revision,
                    "REPLAY",
                    scope_bytes=None,
                    decision_bytes=None,
                    candidate_bytes=raw,
                    checker_hash=state.checker_hash,
                    scope=state.scope,
                )
                return self._result(record.revision, next_state, "ACCEPTED", replayed.code)
        except LacunaError:
            raise
        except OSError as exc:
            raise LacunaError("PERSISTENCE_FAILURE") from exc

    def check_programs(
        self,
        programs: tuple[Program, ...],
        bits: int,
        *,
        expected_revision: str,
    ) -> ShellResult:
        """Replay a restricted runtime against an assessed candidate without a commit.

        This returns diagnostic evidence for the current revision. It creates no
        journal record and no persisted runtime certificate.
        """

        exact_int(bits, 1, 8)
        try:
            with self._locked():
                state, revision, _ = self._load_bound_state()
                if state.scope.profile is not Profile.SIMULATED:
                    _raise("UNAUTHORIZED")
                if expected_revision != revision:
                    _raise("STALE_REVISION")
                if state.cancelled:
                    _raise("CANCELLED")
                report = analyze(state.scope, state.survivors)
                _require_ready_for_replay(report)
                if state.candidate is None or state.candidate_bytes is None:
                    _raise("CANDIDATE_REQUIRED")
                replayed = replay_pipeline(
                    state.scope,
                    state.survivors,
                    state.candidate,
                    programs,
                    bits,
                    tuple(range(1 << bits)),
                )
                self._verify_commit_binding(state.scope, state.checker_hash)
                return ShellResult(revision, replayed, "CHECKED", replayed.code)
        except LacunaError:
            raise
        except OSError as exc:
            raise LacunaError("PERSISTENCE_FAILURE") from exc

    def status(self) -> ShellResult:
        try:
            with self._locked():
                state, revision, _ = self._load_bound_state()
                return self._result(revision, state, "STATUS", self._report(state).code)
        except LacunaError:
            raise
        except OSError as exc:
            raise LacunaError("PERSISTENCE_FAILURE") from exc

    def cancel(self) -> ShellResult:
        try:
            with self._locked():
                state, revision, chain = self._load_bound_state()
                self._require_profile(state.scope)
                if state.cancelled:
                    return self._result(revision, state, "ACCEPTED", "IDEMPOTENT_DUPLICATE")
                self._require_history_work(len(chain.records) + 1, state.scope)
                next_state = replace(state, cancelled=True)
                record = self._commit(
                    chain,
                    revision,
                    "CANCEL",
                    scope_bytes=None,
                    decision_bytes=None,
                    candidate_bytes=None,
                    checker_hash=state.checker_hash,
                    scope=state.scope,
                )
                return self._result(record.revision, next_state, "ACCEPTED", "CANCELLED")
        except LacunaError:
            raise
        except OSError as exc:
            raise LacunaError("PERSISTENCE_FAILURE") from exc

    def resume(self) -> ShellResult:
        try:
            with self._locked():
                state, revision, chain = self._load_bound_state()
                self._require_profile(state.scope)
                if not state.cancelled:
                    _raise("NOT_CANCELLED")
                self._require_history_work(len(chain.records) + 1, state.scope)
                next_state = replace(state, cancelled=False)
                record = self._commit(
                    chain,
                    revision,
                    "RESUME",
                    scope_bytes=None,
                    decision_bytes=None,
                    candidate_bytes=None,
                    checker_hash=state.checker_hash,
                    scope=state.scope,
                )
                return self._result(record.revision, next_state, "ACCEPTED", "RESUMED")
        except LacunaError:
            raise
        except OSError as exc:
            raise LacunaError("PERSISTENCE_FAILURE") from exc

    def _decision_bytes(self, decision: Decision, raw: bytes | None) -> bytes:
        result = encode(decision) if raw is None else raw
        if type(result) is not bytes or decode_decision(result) != decision:
            _raise("DECISION_BYTES_MISMATCH")
        return result

    def _candidate_bytes(self, candidate: Candidate, raw: bytes | None) -> bytes:
        result = encode(candidate) if raw is None else raw
        if type(result) is not bytes or decode_candidate(result) != candidate:
            _raise("CANDIDATE_BYTES_MISMATCH")
        return result

    def _replay_candidate(self, state: _State) -> tuple[Candidate, bytes]:
        if state.candidate is not None and state.candidate_bytes is not None:
            return state.candidate, state.candidate_bytes
        if not state.survivors:
            _raise("EMPTY_H_CONFLICT")
        selected = state.scope.hypotheses[state.survivors[0]]
        candidate = Candidate(
            "MODEL_SELECTED_CANDIDATE:" + selected.name,
            selected.allowed,
            state.scope.assumptions,
        )
        return candidate, encode(candidate)

    def _result(self, revision: str, state: _State, status: str, code: str) -> ShellResult:
        return ShellResult(revision, self._report(state), status, code)

    def _report(self, state: _State) -> Report:
        report = analyze(state.scope, state.survivors)
        if state.cancelled:
            return replace(report, workflow=Workflow.CANCELLED, code="CANCELLED")
        if state.completed_candidate is not None:
            replayed = close_model(state.scope, state.survivors, state.completed_candidate)
            if replayed.workflow is not Workflow.COMPLETE_FOR_SCOPE:
                _raise("CORRUPT_HISTORY")
            return replayed
        return report

    def _duplicate_result(
        self,
        state: _State,
        revision: str,
        raw: bytes,
        decision: Decision,
    ) -> ShellResult | None:
        for binding in state.decisions:
            if binding.raw == raw:
                return self._result(revision, state, "ACCEPTED", "IDEMPOTENT_DUPLICATE")
            if (
                binding.decision.command_id == decision.command_id
                or (binding.decision.parent, binding.decision.question)
                == (decision.parent, decision.question)
            ):
                _raise("DUPLICATE_CONFLICT")
        return None

    def _answer_state(self, state: _State, revision: str, decision: Decision, raw: bytes) -> _State:
        if state.cancelled or decision.parent != revision or decision.scope_root != state.scope.root:
            _raise("STALE_ANSWER")
        report = self._report(state)
        if report.workflow is not Workflow.NEEDS_DECISION:
            _raise("NO_PENDING_DECISION")
        if decision.question != report.policy.question:
            _raise("QUESTION_MISMATCH")
        witness_root = _NO_WITNESS_ROOT if report.witness is None else digest(report.witness)
        if decision.witness_root != witness_root:
            _raise("WITNESS_MISMATCH")
        survivors = filter_answer(state.scope, state.survivors, decision.question, decision.answer)
        return replace(
            state,
            survivors=survivors,
            candidate=None,
            candidate_bytes=None,
            completed_candidate=None,
            decisions=state.decisions + (_DecisionBinding(decision, raw),),
        )

    def _require_profile(self, scope: Scope) -> None:
        if scope.profile is not self.profile:
            _raise("AUTHORIZATION_PROFILE_MISMATCH")

    def _authorize_decision(self, scope: Scope, decision: Decision) -> None:
        self._require_profile(scope)
        if decision.profile is not scope.profile:
            _raise("AUTHORIZATION_PROFILE_MISMATCH")
        if scope.profile is Profile.REAL_OWNER:
            _raise("UNAUTHORIZED")
        if decision.actor != _SIMULATED_ACTOR:
            _raise("UNAUTHORIZED")

    def _authorize_candidate_mutation(self, scope: Scope) -> None:
        self._require_profile(scope)
        if scope.profile is Profile.REAL_OWNER:
            _raise("UNAUTHORIZED")

    def _verify_sources(self, scope: Scope) -> None:
        root = _checked_directory(self.source_root, "SOURCE_ROOT_MISSING")
        for source in scope.sources:
            path = root
            for part in source.path.split("/"):
                path /= part
                try:
                    details = os.lstat(path)
                except OSError as exc:
                    raise LacunaError("SOURCE_MISSING") from exc
                if stat.S_ISLNK(details.st_mode):
                    _raise("SOURCE_SYMLINK")
            if _source_digest(path) != source.sha256:
                _raise("SOURCE_DRIFT")

    @contextmanager
    def _locked(self, create: bool = False) -> Iterator[None]:
        if create:
            self._ensure_layout()
        else:
            self._require_layout()
        lock_path = self.run / ".lock"
        try:
            details = os.lstat(lock_path)
        except FileNotFoundError:
            details = None
        if details is not None:
            if stat.S_ISLNK(details.st_mode):
                _raise("PATH_SYMLINK")
            if not stat.S_ISREG(details.st_mode):
                _raise("INVALID_PATH")
        descriptor = os.open(
            lock_path,
            os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
        try:
            if not stat.S_ISREG(os.fstat(descriptor).st_mode):
                _raise("INVALID_PATH")
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            yield
        finally:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)

    def _ensure_layout(self) -> None:
        parent = _checked_directory(self.run.parent, "RUN_PARENT_MISSING")
        try:
            details = os.lstat(self.run)
        except FileNotFoundError:
            os.mkdir(self.run, 0o700)
            self._fsync_directory(parent)
        else:
            if stat.S_ISLNK(details.st_mode):
                _raise("PATH_SYMLINK")
            if not stat.S_ISDIR(details.st_mode):
                _raise("INVALID_PATH")
        for name in ("records", "quarantine"):
            path = self.run / name
            try:
                details = os.lstat(path)
            except FileNotFoundError:
                os.mkdir(path, 0o700)
                self._fsync_directory(self.run)
            else:
                if stat.S_ISLNK(details.st_mode):
                    _raise("PATH_SYMLINK")
                if not stat.S_ISDIR(details.st_mode):
                    _raise("INVALID_PATH")

    def _require_layout(self) -> None:
        _checked_directory(self.run, "RUN_NOT_INITIALIZED")
        _checked_directory(self.run / "records", "RUN_NOT_INITIALIZED")
        _checked_directory(self.run / "quarantine", "RUN_NOT_INITIALIZED")

    def _reject_existing_run(self) -> None:
        current = self.run / "current"
        try:
            details = os.lstat(current)
        except FileNotFoundError:
            details = None
        if details is not None:
            if stat.S_ISLNK(details.st_mode):
                _raise("PATH_SYMLINK")
            _raise("RUN_ALREADY_INITIALIZED")
        records = self.run / "records"
        if any(records.iterdir()):
            _raise("RUN_INCOMPLETE")

    def _load_bound_state(self) -> tuple[_State, str, _Chain]:
        chain = self._read_chain()
        records = chain.records
        checker_hash = records[0].checker_hash
        if _checker_digest() != checker_hash:
            _raise("CHECKER_DRIFT")
        self._require_history_work(len(records), self._history_scope(records))
        state = self._rebuild(records)
        self._require_profile(state.scope)
        self._verify_sources(state.scope)
        return state, records[-1].revision, chain

    def _read_chain(self) -> _Chain:
        revision = self._read_current()
        reverse: list[_Record] = []
        seen: set[str] = set()
        byte_cost = 0
        while True:
            if revision in seen or len(reverse) >= _MAX_CHAIN_LENGTH:
                _raise("CORRUPT_HISTORY")
            seen.add(revision)
            record, serialized_bytes = self._read_record(revision)
            next_cost = _record_byte_cost(record, serialized_bytes)
            self._require_history_bytes(byte_cost, next_cost)
            byte_cost += next_cost
            reverse.append(record)
            if record.parent is None:
                break
            revision = record.parent
        return _Chain(tuple(reversed(reverse)), byte_cost)

    def _read_current(self) -> str:
        path = self.run / "current"
        raw = _read_regular(path, "RUN_NOT_INITIALIZED", 80)
        try:
            value = raw.decode("ascii")
        except UnicodeDecodeError as exc:
            raise LacunaError("CORRUPT_CURRENT") from exc
        if not value.endswith("\n") or not _is_digest(value[:-1]):
            _raise("CORRUPT_CURRENT")
        return value[:-1]

    def _read_record(self, revision: str) -> tuple[_Record, int]:
        if not _is_digest(revision):
            _raise("CORRUPT_CURRENT")
        raw = _read_regular(
            self.run / "records" / f"{revision}.json",
            "CORRUPT_RECORD",
            _MAX_RECORD_BYTES,
        )
        record = _record_from_bytes(raw)
        if record.revision != revision:
            _raise("CORRUPT_RECORD")
        return record, len(raw)

    @staticmethod
    def _require_history_bytes(current: int, additional: int) -> None:
        if additional > _MAX_HISTORY_BYTES - current:
            _raise("HISTORY_BUDGET_EXCEEDED")

    @staticmethod
    def _history_scope(records: tuple[_Record, ...]) -> Scope:
        if (
            not records
            or records[0].operation != "INIT"
            or records[0].parent is not None
            or records[0].scope_bytes is None
        ):
            _raise("CORRUPT_HISTORY")
        try:
            return decode_scope(records[0].scope_bytes)
        except LacunaError as exc:
            raise LacunaError("CORRUPT_HISTORY") from exc

    @staticmethod
    def _history_work_charge(scope: Scope) -> int:
        relation_preprocessing = (
            len(scope.contexts)
            * len(scope.outcomes)
            * (2 + len(scope.protected)) * (1 + len(scope.hypotheses))
            + len(scope.hypotheses) * len(scope.questions)
        )
        return max(scope.max_work, relation_preprocessing)

    @classmethod
    def _require_history_work(cls, record_count: int, scope: Scope) -> None:
        # Deterministic admission units for repeated replay, not a theorem about
        # Python instruction counts, allocations, or elapsed time.
        if (
            record_count * cls._history_work_charge(scope) * _HISTORY_REBUILD_WORK_FACTOR
            > _MAX_HISTORY_CORE_WORK
        ):
            _raise("HISTORY_BUDGET_EXCEEDED")

    def _rebuild(self, records: tuple[_Record, ...]) -> _State:
        if not records or records[0].operation != "INIT" or records[0].parent is not None:
            _raise("CORRUPT_HISTORY")
        try:
            state = self._apply_initial(records[0])
            previous = records[0].revision
            for record in records[1:]:
                if record.parent != previous or record.checker_hash != state.checker_hash:
                    _raise("CORRUPT_HISTORY")
                state = self._apply_record(state, previous, record)
                previous = record.revision
            return state
        except LacunaError as exc:
            if exc.code == "CORRUPT_HISTORY":
                raise
            raise LacunaError("CORRUPT_HISTORY") from exc

    def _apply_initial(self, record: _Record) -> _State:
        if (
            record.scope_bytes is None
            or record.decision_bytes is not None
            or record.candidate_bytes is not None
            or record.operation != "INIT"
        ):
            _raise("CORRUPT_HISTORY")
        scope = decode_scope(record.scope_bytes)
        return _State(
            scope=scope,
            survivors=analyze(scope).survivors,
            candidate=None,
            candidate_bytes=None,
            completed_candidate=None,
            cancelled=False,
            decisions=(),
            checker_hash=record.checker_hash,
        )

    def _apply_record(self, state: _State, previous: str, record: _Record) -> _State:
        if record.scope_bytes is not None:
            _raise("CORRUPT_HISTORY")
        if record.operation == "ANSWER":
            if record.decision_bytes is None or record.candidate_bytes is not None:
                _raise("CORRUPT_HISTORY")
            decision = decode_decision(record.decision_bytes)
            if decision.profile is not state.scope.profile:
                _raise("CORRUPT_HISTORY")
            if state.scope.profile is not Profile.SIMULATED or decision.actor != _SIMULATED_ACTOR:
                _raise("CORRUPT_HISTORY")
            if any(
                binding.decision.command_id == decision.command_id
                or (binding.decision.parent, binding.decision.question)
                == (decision.parent, decision.question)
                for binding in state.decisions
            ):
                _raise("CORRUPT_HISTORY")
            return self._answer_state(state, previous, decision, record.decision_bytes)
        if record.operation == "ASSESS_REPAIR":
            if (
                record.candidate_bytes is None
                or record.decision_bytes is not None
                or state.cancelled
                or state.scope.profile is not Profile.SIMULATED
            ):
                _raise("CORRUPT_HISTORY")
            if state.candidate_bytes == record.candidate_bytes:
                _raise("CORRUPT_HISTORY")
            candidate = decode_candidate(record.candidate_bytes)
            report = self._report(state)
            if report.workflow is not Workflow.READY_FOR_REPLAY:
                _raise("CORRUPT_HISTORY")
            if assess_repair(state.scope, state.survivors, candidate).workflow is not Workflow.READY_FOR_REPLAY:
                _raise("CORRUPT_HISTORY")
            return replace(
                state,
                candidate=candidate,
                candidate_bytes=record.candidate_bytes,
                completed_candidate=None,
            )
        if record.operation == "REPLAY":
            if (
                record.candidate_bytes is None
                or record.decision_bytes is not None
                or state.cancelled
                or state.completed_candidate is not None
            ):
                _raise("CORRUPT_HISTORY")
            candidate = decode_candidate(record.candidate_bytes)
            expected_candidate, expected_bytes = self._replay_candidate(state)
            if candidate != expected_candidate or record.candidate_bytes != expected_bytes:
                _raise("CORRUPT_HISTORY")
            if analyze(state.scope, state.survivors).workflow is not Workflow.READY_FOR_REPLAY:
                _raise("CORRUPT_HISTORY")
            if close_model(state.scope, state.survivors, candidate).workflow is not Workflow.COMPLETE_FOR_SCOPE:
                _raise("CORRUPT_HISTORY")
            return replace(
                state,
                completed_candidate=candidate,
            )
        if record.operation == "CANCEL":
            if record.decision_bytes is not None or record.candidate_bytes is not None or state.cancelled:
                _raise("CORRUPT_HISTORY")
            return replace(state, cancelled=True)
        if record.operation == "RESUME":
            if record.decision_bytes is not None or record.candidate_bytes is not None or not state.cancelled:
                _raise("CORRUPT_HISTORY")
            return replace(state, cancelled=False)
        _raise("CORRUPT_HISTORY")

    def _commit(
        self,
        chain: _Chain,
        parent: str | None,
        operation: str,
        *,
        scope_bytes: bytes | None,
        decision_bytes: bytes | None,
        candidate_bytes: bytes | None,
        checker_hash: str,
        scope: Scope,
    ) -> _Record:
        self._verify_commit_binding(scope, checker_hash)
        records = self.run / "records"
        if parent is None:
            if chain.records:
                _raise("CORRUPT_HISTORY")
        else:
            if not chain.records or chain.records[-1].revision != parent:
                _raise("CORRUPT_HISTORY")
            if len(chain.records) >= _MAX_CHAIN_LENGTH:
                _raise("CHAIN_LIMIT")
        self._require_history_work(len(chain.records) + 1, scope)
        for attempt in range(_MAX_ATTEMPTS + 1):
            record = _record_for(
                parent,
                operation,
                scope_bytes=scope_bytes,
                decision_bytes=decision_bytes,
                candidate_bytes=candidate_bytes,
                checker_hash=checker_hash,
                attempt=attempt,
            )
            raw = _record_bytes(record)
            self._require_history_bytes(chain.byte_cost, _record_byte_cost(record, len(raw)))
            target = records / f"{record.revision}.json"
            try:
                os.lstat(target)
            except FileNotFoundError:
                self._write_record(target, raw)
                self._fault("before_pointer")
                self._verify_commit_binding(scope, checker_hash)
                self._write_current(record.revision)
                return record
        _raise("PERSISTENCE_FAILURE")

    def _verify_commit_binding(self, scope: Scope, checker_hash: str) -> None:
        self._verify_sources(scope)
        if _checker_digest() != checker_hash:
            _raise("CHECKER_DRIFT")

    def _write_record(self, target: Path, raw: bytes) -> None:
        if len(raw) > _MAX_RECORD_BYTES:
            _raise("PERSISTENCE_FAILURE")
        temporary = self._fresh_temporary(target.parent, f".{target.name}.tmp")
        self._write_durable(temporary, raw)
        os.replace(temporary, target)
        self._fsync_directory(target.parent)

    def _write_current(self, revision: str) -> None:
        target = self.run / "current"
        try:
            details = os.lstat(target)
        except FileNotFoundError:
            details = None
        if details is not None and stat.S_ISLNK(details.st_mode):
            _raise("PATH_SYMLINK")
        temporary = self._fresh_temporary(self.run, ".current.tmp")
        self._write_durable(temporary, (revision + "\n").encode("ascii"))
        os.replace(temporary, target)
        self._fsync_directory(self.run)

    def _fresh_temporary(self, directory: Path, prefix: str) -> Path:
        for index in range(_MAX_ATTEMPTS + 1):
            path = directory / f"{prefix}.{os.getpid()}.{index}"
            try:
                os.lstat(path)
            except FileNotFoundError:
                return path
        _raise("PERSISTENCE_FAILURE")

    def _write_durable(self, path: Path, raw: bytes) -> None:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        try:
            offset = 0
            while offset < len(raw):
                offset += os.write(descriptor, raw[offset:])
            os.fsync(descriptor)
        finally:
            os.close(descriptor)

    def _fsync_directory(self, path: Path) -> None:
        descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)

    def _fault(self, point: str) -> None:
        if self.fault_hook is not None:
            self.fault_hook(point)


__all__ = ["FaultHook", "ShellResult", "Store"]
