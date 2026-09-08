"""Exact finite behavior classes and their compositional compatibility relation.

All candidate source is analyzed on the complete component domain. These
observations confer no execution authority and are never loaded from a claimed
external behavior table.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from math import prod

from .models import Task
from .programs import Program, analyze

MAX_CLASS_COMBINATIONS = 256


@dataclass(frozen=True, slots=True)
class BehaviorClass:
    outputs: tuple[int, ...]
    members: tuple[Program, ...]


@dataclass(frozen=True, slots=True)
class Catalog:
    task: Task
    stages: tuple[tuple[BehaviorClass, ...], ...]
    legal: frozenset[tuple[int, ...]]
    anchor: tuple[int, ...]

    @property
    def artifact_combinations(self) -> int:
        return prod(len(stage.programs) for stage in self.task.stages)

    @property
    def class_combinations(self) -> int:
        return prod(len(classes) for classes in self.stages)


def outputs_of(tables: tuple[tuple[int, ...], ...], inputs: tuple[int, ...]) -> tuple[int, ...]:
    values = inputs
    for table in tables:
        values = tuple(table[value] for value in values)
    return values


def build_catalog(task: Task) -> Catalog:
    if type(task) is not Task:
        raise ValueError("task_type")
    stages = []
    anchors = []
    for stage, anchor in zip(task.stages, task.anchor, strict=True):
        groups: dict[tuple[int, ...], list[Program]] = {}
        for program in stage.programs:
            outputs = analyze(program, task.bits).outputs
            groups.setdefault(outputs, []).append(program)
        classes = tuple(BehaviorClass(outputs, tuple(members))
                        for outputs, members in groups.items())
        stages.append(classes)
        anchors.append(next(i for i, cls in enumerate(classes)
                            if any(p.name == anchor for p in cls.members)))
    frozen = tuple(stages)
    if prod(len(classes) for classes in frozen) > MAX_CLASS_COMBINATIONS:
        raise ValueError("class_combination_bound")
    legal = frozenset(
        codes for codes in product(*(range(len(classes)) for classes in frozen))
        if outputs_of(tuple(classes[code].outputs for classes, code in
                            zip(frozen, codes, strict=True)), task.inputs) == task.expected
    )
    if tuple(anchors) not in legal:
        raise ValueError("anchor_pipeline_invalid")
    return Catalog(task, frozen, legal, tuple(anchors))


def central_counts(task: Task) -> dict[str, int]:
    """Bound public work by rebuilding observations from exact source inputs."""
    return _central_counts_catalog(build_catalog(task))


def _central_counts_catalog(catalog: Catalog) -> dict[str, int]:
    """Count exact cached checking and quotient checking over the same catalog."""
    expanded = tuple(tuple(cls.outputs for cls in classes for _ in cls.members)
                     for classes in catalog.stages)
    accepted = sum(outputs_of(tables, catalog.task.inputs) == catalog.task.expected
                   for tables in product(*expanded))
    weighted = sum(prod(len(classes[code].members) for classes, code in
                        zip(catalog.stages, codes, strict=True)) for codes in catalog.legal)
    if accepted != weighted:
        raise ValueError("quotient_baseline_disagreement")
    return {"cached_artifact_checks": catalog.artifact_combinations,
            "quotient_class_checks": catalog.class_combinations,
            "accepted_artifact_bundles": accepted,
            "accepted_behavior_bundles": len(catalog.legal),
            "source_input_evaluations": sum(len(s.programs) for s in catalog.task.stages)
                                        * (1 << catalog.task.bits)}
