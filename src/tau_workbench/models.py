"""Owned finite task inputs for source-backed component experiments."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from math import prod

from .programs import Program


def check_name(name: object) -> None:
    if type(name) is not str or re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{0,47}", name) is None:
        raise ValueError("workbench_name")


@dataclass(frozen=True, slots=True)
class Stage:
    name: str
    programs: tuple[Program, ...]

    def __post_init__(self) -> None:
        check_name(self.name)
        if type(self.programs) is not tuple or not 1 <= len(self.programs) <= 32:
            raise ValueError("stage_program_bound")
        if any(type(program) is not Program for program in self.programs):
            raise ValueError("stage_program_type")
        names = tuple(program.name for program in self.programs)
        if len(set(names)) != len(names):
            raise ValueError("duplicate_program_name")


@dataclass(frozen=True, slots=True)
class Task:
    """A complete component domain and a human-specified end-to-end table."""

    name: str
    bits: int
    stages: tuple[Stage, ...]
    inputs: tuple[int, ...]
    expected: tuple[int, ...]
    anchor: tuple[str, ...]

    def __post_init__(self) -> None:
        check_name(self.name)
        if type(self.bits) is not int or not 1 <= self.bits <= 8:
            raise ValueError("domain_bits")
        if type(self.stages) is not tuple or not 1 <= len(self.stages) <= 4:
            raise ValueError("stage_bound")
        if any(type(stage) is not Stage for stage in self.stages):
            raise ValueError("stage_type")
        if len({stage.name for stage in self.stages}) != len(self.stages):
            raise ValueError("duplicate_stage_name")
        if prod(len(stage.programs) for stage in self.stages) > 4096:
            raise ValueError("artifact_combination_bound")
        self._check_table()
        if type(self.anchor) is not tuple or len(self.anchor) != len(self.stages):
            raise ValueError("anchor_shape")
        for stage, name in zip(self.stages, self.anchor, strict=True):
            if type(name) is not str or name not in {p.name for p in stage.programs}:
                raise ValueError("anchor_program")

    def _check_table(self) -> None:
        for values in (self.inputs, self.expected):
            if type(values) is not tuple or not 1 <= len(values) <= 1 << self.bits:
                raise ValueError("task_table_shape")
            if any(type(v) is not int or not 0 <= v < 1 << self.bits for v in values):
                raise ValueError("task_table_value")
        if len(self.inputs) != len(self.expected):
            raise ValueError("task_table_cardinality")
        if tuple(sorted(set(self.inputs))) != self.inputs:
            raise ValueError("task_input_order")

    @property
    def subject_id(self) -> str:
        data = {"schema": "tau-workbench/task-v1", "profile": "pure-integer-python-v1",
                "name": self.name, "bits": self.bits,
                "inputs": self.inputs, "expected": self.expected, "anchor": self.anchor,
                "stages": [{"name": stage.name,
                            "programs": [(p.name, p.sha256) for p in stage.programs]}
                           for stage in self.stages]}
        encoded = json.dumps(data, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(encoded).hexdigest()
