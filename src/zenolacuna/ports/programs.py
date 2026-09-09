"""Bounded integer runtime binding through the existing restricted interpreter."""

from dataclasses import replace

from src.tau_workbench.programs import Program, analyze

from ..check import close_model
from ..model import (
    Candidate,
    LacunaError,
    OutcomeKind,
    Report,
    Scope,
    ScopeKind,
    exact_int,
    owned_tuple,
)


def pipeline_outputs(programs: tuple[Program, ...], bits: int) -> tuple[int, ...]:
    exact_int(bits, 1, 8)
    owned_tuple(programs, Program, 4)
    if not programs:
        raise LacunaError("EMPTY_PIPELINE")
    try:
        tables = tuple(analyze(program, bits).outputs for program in programs)
    except ValueError as error:
        raise LacunaError("UNSUPPORTED_PROGRAM:" + str(error)) from error
    outputs = tuple(range(1 << bits))
    for table in tables:
        outputs = tuple(table[value] for value in outputs)
    return outputs


def replay_pipeline(scope: Scope, survivors: tuple[int, ...], candidate: Candidate,
                    programs: tuple[Program, ...], bits: int, inputs: tuple[int, ...]) -> Report:
    exact_int(bits, 1, 8)
    if type(inputs) is not tuple or any(type(i) is not int for i in inputs):
        raise LacunaError("INVALID_RUNTIME_INPUTS")
    if inputs != tuple(range(1 << bits)) or scope.contexts != tuple(map(str, inputs)):
        raise LacunaError("INCOMPLETE_RUNTIME_DOMAIN")
    if scope.kind is not ScopeKind.FINITE_RELATION or scope.assumptions != inputs:
        raise LacunaError("INCOMPLETE_RUNTIME_DOMAIN")
    if tuple(o.name for o in scope.outcomes) != tuple(map(str, inputs)):
        raise LacunaError("RUNTIME_ENCODING_MISMATCH")
    # This interpreter observes an integer return, not an application rejection
    # event. A caller's label cannot supply an unobserved verdict projection.
    if any(o.observation != o.name or o.kind is not OutcomeKind.ACCEPT for o in scope.outcomes):
        raise LacunaError("RUNTIME_ENCODING_MISMATCH")
    if scope.sources and tuple(source.sha256 for source in scope.sources) != tuple(program.sha256 for program in programs):
        raise LacunaError("SOURCE_DRIFT")
    observed = tuple((value,) for value in pipeline_outputs(programs, bits))
    if observed != candidate.allowed:
        raise LacunaError("RUNTIME_MODEL_MISMATCH")
    report = close_model(scope, survivors, candidate)
    return replace(report, code="RESTRICTED_PROGRAM_REPLAYED",
                   claim="EXHAUSTIVE_RESTRICTED_INTEGER_PROGRAM;PROGRAM_SHA256=" +
                   ",".join(program.sha256 for program in programs))
