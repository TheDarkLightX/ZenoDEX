"""Signed local project lifecycle, durable evidence and independent archive replay."""

import hashlib
import os
from dataclasses import replace
from pathlib import Path
from typing import Callable

from .authority import Action, SignedCommand, decode_signed, encode_signed
from .codec import _parse, encode
from .engine import analyze, assess_repair
from .model import Candidate, Evidence, LacunaError, OutcomeKind, ScopeKind, Witness, Workflow
from .project_bindings import checker_fingerprint
from .project_core import candidate_root, initialize, transition, witness_root
from .project_execution import execution_context
from .project_runtime import ExternalTools, complete, declaration_error
from .project_storage import (
    MAX_BLOBS,
    MAX_BYTES,
    MAX_EVENTS,
    bundle_bytes,
    database,
    decode_bundle,
    read_blobs,
    read_events,
    require_sources,
    snapshot_sources,
)
from .project_types import ProjectState, plain
from .proposals import proposal_packet
from .relations import check_witness

Events = tuple[tuple[bytes, bytes | None], ...]
NO_EXTERNAL_TOOLS = ExternalTools()


def _rebuild(events: Events, blobs: dict[str, bytes], *, owner_key: str,
             checker_sha256: str, tools: ExternalTools) -> ProjectState:
    if not events:
        raise LacunaError("INITIALIZATION_REQUIRED")
    if len(events) > MAX_EVENTS or sum(len(s) + (len(e) if e else 0) for s, e in events) > MAX_BYTES:
        raise LacunaError("PROJECT_BUDGET_EXCEEDED")
    if len(blobs) > MAX_BLOBS or sum(map(len, blobs.values())) > MAX_BYTES:
        raise LacunaError("PROJECT_BUDGET_EXCEEDED")
    state = None
    used_sources: set[str] = set()
    work = 0
    for signed_bytes, stored_evidence in events:
        signed = decode_signed(signed_bytes)
        step = initialize(signed, owner_key=owner_key, checker_sha256=checker_sha256) if state is None else transition(
            state, signed, owner_key=owner_key,
        )
        state = step.state
        scope = state.task.scope
        work += len(scope.contexts) * len(scope.outcomes) * (3 + len(scope.protected)) * (1 + len(scope.hypotheses))
        if work > 64_000_000:
            raise LacunaError("PROJECT_BUDGET_EXCEEDED")
        used_sources.update(source.sha256 for source in scope.sources)
        require_sources(scope, blobs)
        evidence = complete(state, blobs, checker_sha256=checker_sha256, tools=tools) if step.check_runtime else None
        if evidence != stored_evidence:
            raise LacunaError("EVIDENCE_MISMATCH")
        if evidence is not None:
            state = replace(state, completion=evidence)
    if used_sources != set(blobs):
        raise LacunaError("UNBOUND_SOURCE")
    if state is None:
        raise LacunaError("INITIALIZATION_REQUIRED")
    return state


def _status(state: ProjectState) -> dict[str, object]:
    report = analyze(state.task.scope, state.survivors)
    workflow, evidence, code = report.workflow.value, report.evidence.value, report.code
    claim = "FINITE_MODEL_ONLY"
    completion = None
    if state.completion is not None:
        completion = _parse(state.completion)
        # This value was recomputed by _rebuild, never admitted from a saved flag.
        if not isinstance(completion, dict) or not isinstance(completion["runtime"], dict):
            raise LacunaError("EVIDENCE_MISMATCH")
        workflow, code = "COMPLETE_FOR_SCOPE", "PROJECT_REPLAYED"
        evidence = "BOUNDED_SEARCH" if state.task.scope.history_bound is not None else "EXHAUSTIVE_FINITE"
        claim = completion["runtime"]["claim"]
    omission = declaration_error(state.task)
    if omission is not None:
        workflow, evidence, code = "INCONCLUSIVE", "UNKNOWN", omission
    if state.cancelled:
        workflow, code = "CANCELLED", "CANCELLED"
    return {
        "schema": "zenolacuna/project-status/v1", "project_id": state.project_id,
        "revision": state.revision, "scope_revision": state.scope_revision,
        "scope_root": state.task.scope.root, "workflow": workflow, "evidence": evidence,
        "code": code, "claim": claim, "authority": "NONE", "approval": "OWNER_PIN_VERIFIED",
        "execution_context": execution_context(),
        "survivors": state.survivors, "candidate_root": candidate_root(state),
        "witness_root": witness_root(state), "analysis": plain(report),
        "completion": completion, "effect_plan": (), "outbox": (),
    }


class Project:
    """Imperative shell. Operator-supplied owner_key is never read from a bundle."""

    def __init__(self, path: str | Path, *, source_root: str | Path, owner_key: str,
                 tools: ExternalTools = NO_EXTERNAL_TOOLS, fault_hook: Callable[[str], None] | None = None):
        self.path = Path(os.path.abspath(path))
        self.source_root = Path(os.path.abspath(source_root))
        self.owner_key = owner_key
        self.tools = tools
        self.fault_hook = fault_hook

    @property
    def checker_sha256(self) -> str:
        return checker_fingerprint()

    def _fault(self, point: str) -> None:
        if self.fault_hook is not None:
            self.fault_hook(point)

    def _load(self, events: Events, blobs: dict[str, bytes], *, fresh: bool = True) -> ProjectState:
        fingerprint = checker_fingerprint()
        state = _rebuild(events, blobs, owner_key=self.owner_key, checker_sha256=fingerprint, tools=self.tools)
        if fresh:
            snapshot_sources(state.task.scope, self.source_root)
        if checker_fingerprint() != fingerprint:
            raise LacunaError("CHECKER_DRIFT")
        return state

    def state(self) -> ProjectState:
        with database(self.path) as db:
            return self._load(read_events(db), read_blobs(db))

    def status(self) -> dict[str, object]:
        return _status(self.state())

    def revision_status(self) -> dict[str, object]:
        """Read authenticated history to prepare a successor after source edits.

        This does not assert correspondence to the current working source tree.
        It never applies a command or substitutes history for a current run.
        """
        with database(self.path) as db:
            state = self._load(read_events(db), read_blobs(db), fresh=False)
            return {**_status(state), "replay_scope": "ARCHIVED_REVISION_FOR_SUCCESSOR",
                    "working_sources_checked": False}

    def apply(self, signed: SignedCommand) -> dict[str, object]:
        raw = encode_signed(signed)
        signed = decode_signed(raw)
        fingerprint = checker_fingerprint()
        with database(self.path, create=signed.command.action is Action.INIT) as db:
            events, blobs = read_events(db), read_blobs(db)
            if events:
                previous = self._load(events, blobs, fresh=signed.command.action is not Action.REVISE)
                if any(old == raw for old, _ in events):
                    return {**_status(previous), "code": "IDEMPOTENT_DUPLICATE"}
                step = transition(previous, signed, owner_key=self.owner_key)
            else:
                step = initialize(signed, owner_key=self.owner_key, checker_sha256=fingerprint)
            state = step.state
            blobs.update(snapshot_sources(state.task.scope, self.source_root))
            self._fault("after_source_snapshot")
            evidence = complete(state, blobs, checker_sha256=fingerprint, tools=self.tools) if step.check_runtime else None
            self._fault("after_verification")
            new_events = events + ((raw, evidence),)
            # Admission and reconstruction have exactly the same rules and budgets.
            # Rebuild also reruns COMPLETE: serialized evidence cannot skip a gate.
            rebuilt = self._load(new_events, blobs)
            # Every accepted state must remain exportable under the public
            # bundle codec's tighter serialized-size bound.
            try:
                bundle_bytes(new_events, blobs, rebuilt.revision)
            except LacunaError as exc:
                if exc.code == "JSON_TOO_LARGE":
                    raise LacunaError("PROJECT_BUDGET_EXCEEDED") from exc
                raise
            if checker_fingerprint() != fingerprint:
                raise LacunaError("CHECKER_DRIFT")
            for sha, content in sorted(blobs.items()):
                db.execute("INSERT OR IGNORE INTO sources VALUES (?, ?)", (sha, content))
            self._fault("after_source_insert")
            db.execute("INSERT INTO events VALUES (?, ?, ?)", (len(events), raw, evidence))
            self._fault("after_event_insert")
            self._fault("before_commit")
            snapshot_sources(state.task.scope, self.source_root)
            if checker_fingerprint() != fingerprint:
                raise LacunaError("CHECKER_DRIFT")
            db.commit()
            self._fault("after_commit")
            return _status(rebuilt)

    def export_bytes(self) -> bytes:
        with database(self.path) as db:
            events, blobs = read_events(db), read_blobs(db)
            state = self._load(events, blobs)
            return bundle_bytes(events, blobs, state.revision)

    def proposals(self) -> dict[str, object]:
        state = self.state()
        packet = proposal_packet(state.task.scope)
        packet["current"] = analyze(state.task.scope, state.survivors)
        return {"revision": state.revision, "scope_revision": state.scope_revision,
                "witness_root": witness_root(state), "packet": plain(packet),
                "admitted_survivors": state.survivors, "authority": "NONE"}

    def admit_witness(self, witness: Witness, *, expected_revision: str) -> dict[str, object]:
        state = self.state()
        if expected_revision != state.revision or state.cancelled:
            raise LacunaError("STALE_ANSWER")
        if witness.left_hypothesis not in state.survivors or witness.right_hypothesis not in state.survivors:
            raise LacunaError("WITNESS_PREMISE_FAILED")
        check_witness(state.task.scope, witness)
        scope = state.task.scope
        body = {"revision": state.revision, "scope_root": scope.root, "witness": plain(witness),
                "premise_digest": hashlib.sha256(b"zenolacuna/witness-premises/v1\0" + encode(
                    plain((scope.assumptions, scope.contract, scope.protected, scope.hypotheses)))).hexdigest(),
                "sources": plain(scope.sources),
                "observations": plain((scope.outcomes[witness.left_outcome], scope.outcomes[witness.right_outcome]))}
        return {"status": "ACCEPTED", "code": "WITNESS_REPLAYED", "authority": "NONE", **body,
                "receipt_sha256": hashlib.sha256(encode(body)).hexdigest()}

    def inspect_candidate(self, candidate: Candidate) -> dict[str, object]:
        state = self.state()
        report = assess_repair(state.task.scope, state.survivors, candidate)
        classification, code = report.code.split(":", 1)[0], report.code
        omission = declaration_error(state.task)
        if omission is not None:
            classification, code = "MODEL_OMISSION", omission
            report = replace(report, workflow=Workflow.INCONCLUSIVE, evidence=Evidence.UNKNOWN, code=code)
        elif report.workflow.value == "READY_FOR_REPLAY":
            try:
                complete(replace(state, candidate=candidate), snapshot_sources(state.task.scope, self.source_root),
                         checker_sha256=checker_fingerprint(), tools=self.tools)
                classification, code = "CHECKED_FOR_SCOPE", "CANDIDATE_REPLAYED"
            except LacunaError as exc:
                code = exc.code
                classification = "MODEL_OMISSION" if code in ("MODEL_OMISSION", "UNENUMERATED_INPUT", "RUNTIME_ENCODING_MISMATCH") else code.split(":", 1)[0]
                if not code.startswith("CODE_BUG"):
                    report = replace(report, workflow=Workflow.INCONCLUSIVE, evidence=Evidence.UNKNOWN, code=code)
        return {"revision": state.revision, "scope_revision": state.scope_revision,
                "candidate": candidate.name, "classification": classification, "code": code,
                "report": plain(report), "authority": "NONE"}

    def admit_observation(self, context: str, kind: OutcomeKind, observation: str, *,
                          expected_revision: str) -> dict[str, object]:
        """Check a complete observation/trace, preserving set-valued behavior.

        This is membership in the decided finite model. It does not authenticate
        the producer of the observation or prove a program produced this trace.
        """
        state = self.state()
        if expected_revision != state.revision or state.cancelled:
            raise LacunaError("STALE_ANSWER")
        scope = state.task.scope
        if type(context) is not str or context not in scope.contexts or type(kind) is not OutcomeKind:
            raise LacunaError("MODEL_OMISSION")
        if type(observation) is not str:
            raise LacunaError("MODEL_OMISSION")
        matching = tuple(i for i, o in enumerate(scope.outcomes) if (o.kind, o.observation) == (kind, observation))
        if not matching:
            raise LacunaError("MODEL_OMISSION")
        row = scope.contexts.index(context)
        if row not in scope.assumptions:
            raise LacunaError("MODEL_OMISSION")
        if state.candidate is None:
            raise LacunaError("CANDIDATE_REQUIRED")
        if not any(i in state.candidate.allowed[row] for i in matching):
            raise LacunaError("TRACE_NOT_ALLOWED" if scope.kind is ScopeKind.BOUNDED_HISTORY else "OBSERVATION_NOT_ALLOWED")
        body = {"revision": state.revision, "scope_root": scope.root, "candidate_root": candidate_root(state),
                "context": context, "kind": kind.value, "observation": observation,
                "history_bound": scope.history_bound}
        return {**body, "code": "OBSERVATION_ALLOWED", "authority": "NONE", "claim": "FINITE_MODEL_MEMBERSHIP",
                "receipt_sha256": hashlib.sha256(b"zenolacuna/observation/v1\0" + encode(body)).hexdigest()}


def replay_bundle(raw: bytes, *, owner_key: str, expected_revision: str | None = None,
                  tools: ExternalTools = NO_EXTERNAL_TOOLS) -> dict[str, object]:
    """Verify an exact historical snapshot; never restore it over a live project."""
    events, blobs, recorded_revision = decode_bundle(raw)
    if expected_revision is not None and expected_revision != recorded_revision:
        raise LacunaError("STALE_BUNDLE")
    fingerprint = checker_fingerprint()
    state = _rebuild(events, blobs, owner_key=owner_key, checker_sha256=fingerprint, tools=tools)
    if state.revision != recorded_revision or checker_fingerprint() != fingerprint:
        raise LacunaError("EVIDENCE_MISMATCH")
    return {**_status(state), "replay_scope": "EXACT_HISTORICAL_SNAPSHOT"}
