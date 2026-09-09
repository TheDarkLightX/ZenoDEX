"""Runtime correspondence on archived bytes and a closed installed adapter set."""

import hashlib
from dataclasses import dataclass
from pathlib import Path

from src.tau_workbench.programs import Program

from .check import close_model
from .codec import encode
from .model import LacunaError, Workflow
from .ports.programs import replay_pipeline
from .project_core import candidate_root
from .project_storage import require_sources
from .project_types import ProjectState, Task, plain, task_value


@dataclass(frozen=True, slots=True)
class ExternalTools:
    tau_bin: Path | None = None
    esso_root: Path | None = None


def declaration_error(task: Task) -> str | None:
    """Check the observation/domain contract before interpreting any candidate."""
    scope, runtime = task.scope, task.runtime
    if runtime.adapter == "RESTRICTED_PIPELINE":
        if runtime.observations != ("return",):
            return "MODEL_OMISSION"
        size = len(runtime.inputs)
        if size < 2 or size > 256 or size & (size - 1) or runtime.inputs != tuple(range(size)):
            return "UNENUMERATED_INPUT"
    elif runtime.adapter == "SIGNAL_MIGRATION":
        from .project_bindings import ROOT
        from .signal_migration import OBSERVATIONS, migration_scope
        if runtime.observations != OBSERVATIONS:
            return "MODEL_OMISSION"
        if runtime.inputs != tuple(range(128)):
            return "UNENUMERATED_INPUT"
        fixed = migration_scope(ROOT)
        if (scope.contexts, scope.outcomes, scope.assumptions, scope.kind, scope.history_bound) != (
            fixed.contexts, fixed.outcomes, fixed.assumptions, fixed.kind, fixed.history_bound,
        ):
            return "RUNTIME_ENCODING_MISMATCH"
    return None


def _pipeline(state: ProjectState, blobs: dict[str, bytes]) -> dict[str, object]:
    scope, runtime = state.task.scope, state.task.runtime
    if runtime.observations != ("return",):
        raise LacunaError("MODEL_OMISSION")
    size = len(runtime.inputs)
    if size < 2 or size > 256 or size & (size - 1) or runtime.inputs != tuple(range(size)):
        raise LacunaError("UNENUMERATED_INPUT")
    if not 1 <= len(scope.sources) <= 4:
        raise LacunaError("UNALLOWLISTED_SOURCE")
    programs = tuple(Program(f"program_{index}", blobs[source.sha256]) for index, source in enumerate(scope.sources))
    if state.candidate is None:
        raise LacunaError("CANDIDATE_REQUIRED")
    try:
        report = replay_pipeline(scope, state.survivors, state.candidate, programs, size.bit_length() - 1, runtime.inputs)
    except LacunaError as exc:
        if exc.code.startswith("UNSUPPORTED_PROGRAM"):
            raise LacunaError("UNALLOWLISTED_SOURCE") from exc
        if exc.code == "INCOMPLETE_RUNTIME_DOMAIN":
            raise LacunaError("UNENUMERATED_INPUT") from exc
        if exc.code == "RUNTIME_MODEL_MISMATCH":
            raise LacunaError("CODE_BUG:RUNTIME_MODEL_MISMATCH:" + state.candidate.name) from exc
        raise
    return {"adapter": runtime.adapter, "claim": report.claim, "report": plain(report)}


def _migration(state: ProjectState, blobs: dict[str, bytes]) -> dict[str, object]:
    from .signal_migration import (
        CandidateMode,
        check_migration,
        migration_candidate,
    )

    matched = [mode for mode in CandidateMode if state.candidate == migration_candidate(mode)]
    if len(matched) != 1:
        raise LacunaError("UNALLOWLISTED_SOURCE")
    report = check_migration(mode=matched[0], inputs=state.task.runtime.inputs,
                             declared_observations=state.task.runtime.observations)
    # The allowlisted adapter is installed checker code; it verifies its load-time
    # bindings and the project must archive the same complete dependency set.
    installed = dict(report.source_sha256)
    if {s.path: s.sha256 for s in state.task.scope.sources} != installed:
        raise LacunaError("SOURCE_DRIFT")
    if any(hashlib.sha256(blobs[sha]).hexdigest() != sha for sha in installed.values()):
        raise LacunaError("SOURCE_DRIFT")
    if report.code != "SIGNAL_MIGRATION_CHECKED":
        raise LacunaError(report.code)
    return {"adapter": "SIGNAL_MIGRATION", "claim": "FINITE_SIGNAL_MIGRATION_GRAPH", "report": plain(report)}


def complete(state: ProjectState, blobs: dict[str, bytes], *, checker_sha256: str,
             tools: ExternalTools) -> bytes:
    """Recompute every result before it can be persisted or shown as checked."""
    require_sources(state.task.scope, blobs)
    error = declaration_error(state.task)
    if error is not None:
        raise LacunaError(error)
    if state.candidate is None:
        raise LacunaError("CANDIDATE_REQUIRED")
    report = close_model(state.task.scope, state.survivors, state.candidate)
    if report.workflow is not Workflow.COMPLETE_FOR_SCOPE:
        raise LacunaError(report.code)
    adapter = state.task.runtime.adapter
    runtime: dict[str, object]
    if adapter == "RELATION":
        runtime = {"adapter": adapter, "claim": "FINITE_MODEL_ONLY"}
    elif adapter == "RESTRICTED_PIPELINE":
        runtime = _pipeline(state, blobs)
    elif adapter == "SIGNAL_MIGRATION":
        runtime = _migration(state, blobs)
    else:
        raise LacunaError("UNALLOWLISTED_SOURCE")
    from .project_solvers import check_required_tools
    solver_evidence = check_required_tools(state, tools)
    return encode({
        "schema": "zenolacuna/completion/v1", "authority": "NONE",
        "project_id": state.project_id, "revision": state.revision,
        "scope_revision": state.scope_revision, "scope_root": state.task.scope.root,
        "task_sha256": hashlib.sha256(encode(task_value(state.task))).hexdigest(),
        "candidate_root": candidate_root(state), "checker_sha256": checker_sha256,
        "approval_roots": [root for _, _, root, _ in state.answers],
        "sources": plain(state.task.scope.sources), "runtime": runtime,
        "model": plain(report), "solvers": solver_evidence,
        "survivors_root": hashlib.sha256(b"zenolacuna/survivors/v1\0" + encode(state.survivors)).hexdigest(),
    })
