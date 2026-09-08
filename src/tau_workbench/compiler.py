"""Compile source-derived finite compatibility into per-agent Tau choices."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product

from src.tau_composition.models import Contract, RepairMap, Requirement
from src.tau_composition.runtime import TauRuntime
from src.tau_composition.terms import constant
from src.tau_swarm.compiler import AutonomyCompiler
from src.tau_swarm.models import AgentBlock, AutonomyEnvelope, SwarmProblem

from .catalog import Catalog, build_catalog, outputs_of
from .models import Task
from .programs import Program, analyze
from .relation import residuals


def _controls(index: int, count: int) -> tuple[str, ...]:
    return tuple(f"stage{index}_bit{bit}" for bit in range(max(1, (count - 1).bit_length())))


def _bits(names: tuple[str, ...], code: int) -> dict[str, bool]:
    return {name: bool(code & (1 << i)) for i, name in enumerate(names)}


def problem_for(task: Task) -> SwarmProblem:
    """Derive a normative relation from raw source, never from claimed tables."""
    return _problem_for_catalog(build_catalog(task))


def _problem_for_catalog(catalog: Catalog) -> SwarmProblem:
    blocks = tuple(AgentBlock(stage.name, _controls(i, len(classes)))
                   for i, (stage, classes) in enumerate(
                       zip(catalog.task.stages, catalog.stages, strict=True)))
    controls = tuple(name for block in blocks for name in block.controls)
    allowed = frozenset(tuple(value for block, code in zip(blocks, codes, strict=True)
                              for value in _bits(block.controls, code).values())
                        for codes in catalog.legal)
    _reference, residual = residuals(controls, allowed)
    contract = Contract(catalog.task.name, (), controls,
                        (Requirement("exact_pipeline_behavior", residual),))
    anchor = RepairMap(tuple((name, constant(value)) for block, code in
                             zip(blocks, catalog.anchor, strict=True)
                             for name, value in _bits(block.controls, code).items()))
    return SwarmProblem(contract, blocks, anchor)


def _check_domains(catalog: Catalog, domains: tuple[tuple[int, ...], ...]) -> None:
    if any(not domain for domain in domains):
        raise ValueError("empty_behavior_domain")
    if any(codes not in catalog.legal for codes in product(*domains)):
        raise ValueError("unsafe_behavior_product")
    for i, classes in enumerate(catalog.stages):
        others = tuple(domain if j != i else (0,) for j, domain in enumerate(domains))
        for own in range(len(classes)):
            compatible = all(row[:i] + (own,) + row[i + 1:] in catalog.legal
                             for row in product(*others))
            if (own in domains[i]) != compatible:
                raise ValueError("inexact_behavior_domain")


@dataclass(frozen=True, slots=True)
class CompiledWorkbench:
    """Advisory observations; selections are checked against original source."""

    catalog: Catalog
    envelope: AutonomyEnvelope
    domains: tuple[tuple[int, ...], ...]

    def members(self, stage_index: int) -> tuple[Program, ...]:
        if type(stage_index) is not int or not 0 <= stage_index < len(self.domains):
            raise ValueError("stage_index")
        return tuple(member for code in self.domains[stage_index]
                     for member in self.catalog.stages[stage_index][code].members)

    def check_selection(self, names: tuple[str, ...]) -> tuple[Program, ...]:
        if type(names) is not tuple or len(names) != len(self.domains):
            raise ValueError("selection_shape")
        selected = []
        for i, name in enumerate(names):
            if type(name) is not str:
                raise ValueError("selection_program")
            matches = tuple(p for p in self.members(i) if p.name == name)
            if len(matches) != 1:
                raise ValueError("selection_program")
            selected.append(matches[0])
        programs = tuple(selected)
        check_pipeline(self.catalog.task, programs)
        return programs

    def assess_replacement(self, stage: str, program: Program) -> dict[str, object]:
        names = tuple(s.name for s in self.catalog.task.stages)
        if type(stage) is not str or stage not in names:
            raise ValueError("replacement_stage")
        index = names.index(stage)
        observed = analyze(program, self.catalog.task.bits)
        for code, cls in enumerate(self.catalog.stages[index]):
            if observed.outputs == cls.outputs:
                admitted = code in self.domains[index]
                return {"status": "local_equivalent" if admitted else "renegotiation_required",
                        "task_id": self.catalog.task.subject_id, "program_sha256": program.sha256,
                        "stage": stage, "behavior_class": code, "native_queries": 0,
                        "authority": "NONE"}
        return {"status": "renegotiation_required", "task_id": self.catalog.task.subject_id,
                "program_sha256": program.sha256, "stage": stage, "behavior_class": None,
                "native_queries": 0, "authority": "NONE"}

    def check_revision(self, programs: tuple[Program, ...]) -> tuple[Program, ...]:
        """Accept independently supplied replacements only after fresh local and joint checks."""
        if type(programs) is not tuple or len(programs) != len(self.domains):
            raise ValueError("selection_shape")
        task = self.catalog.task
        tables = tuple(analyze(program, task.bits).outputs for program in programs)
        for i, table in enumerate(tables):
            allowed = tuple(self.catalog.stages[i][code].outputs for code in self.domains[i])
            if table not in allowed:
                raise ValueError("revision_requires_renegotiation")
        if outputs_of(tables, task.inputs) != task.expected:
            raise ValueError("pipeline_behavior_mismatch")
        return programs


def check_pipeline(task: Task, programs: tuple[Program, ...]) -> None:
    """Re-evaluate exact selected bytes; never accept a supplied behavior table."""
    if type(programs) is not tuple or len(programs) != len(task.stages):
        raise ValueError("selection_shape")
    tables = tuple(analyze(program, task.bits).outputs for program in programs)
    if outputs_of(tables, task.inputs) != task.expected:
        raise ValueError("pipeline_behavior_mismatch")


def compile_task(task: Task, runtime: TauRuntime, order: tuple[str, ...] | None = None) -> CompiledWorkbench:
    catalog = build_catalog(task)
    problem = _problem_for_catalog(catalog)
    envelope = AutonomyCompiler(runtime).compile(problem, order)
    domains = []
    for block, classes in zip(problem.blocks, catalog.stages, strict=True):
        width = len(block.controls)
        codes = tuple(code for code in range(1 << width)
                      if envelope.permits(block.name, _bits(block.controls, code)))
        if any(code >= len(classes) for code in codes):
            raise ValueError("absent_behavior_class")
        domains.append(codes)
    frozen = tuple(domains)
    _check_domains(catalog, frozen)
    return CompiledWorkbench(catalog, envelope, frozen)
