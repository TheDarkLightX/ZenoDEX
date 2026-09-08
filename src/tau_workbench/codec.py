"""Closed, bounded JSON data for finite source-artifact tasks."""

from __future__ import annotations

import json
from typing import Any

from src.tau_composition.codec import _unique_object

from .models import Stage, Task
from .programs import Program

SCHEMA = "tau-workbench/task-v1"
MAX_TASK_BYTES = 512_000


def _object(value: object, fields: set[str]) -> dict[str, Any]:
    if type(value) is not dict or set(value) != fields:
        raise ValueError("task_object_shape")
    return value


def _list(value: object, bound: int) -> list[Any]:
    if type(value) is not list or not 1 <= len(value) <= bound:
        raise ValueError("task_list_bound")
    return value


def decode_task(text: str) -> Task:
    if type(text) is not str:
        raise ValueError("task_text_type")
    try:
        if len(text.encode("utf-8")) > MAX_TASK_BYTES:
            raise ValueError("task_byte_bound")
        data = _object(json.loads(text, object_pairs_hook=_unique_object),
                       {"schema", "name", "bits", "stages", "inputs", "expected", "anchor"})
        if data["schema"] != SCHEMA:
            raise ValueError("task_schema")
        stages = tuple(_stage(raw) for raw in _list(data["stages"], 4))
        return Task(data["name"], data["bits"], stages, tuple(_list(data["inputs"], 256)),
                    tuple(_list(data["expected"], 256)), tuple(_list(data["anchor"], 4)))
    except (TypeError, RecursionError, UnicodeError) as exc:
        raise ValueError("malformed_task_data") from exc


def _stage(raw: object) -> Stage:
    stage = _object(raw, {"name", "programs"})
    programs = []
    for item in _list(stage["programs"], 32):
        data = _object(item, {"name", "source"})
        if type(data["source"]) is not str:
            raise ValueError("program_source_text")
        programs.append(Program(data["name"], data["source"].encode("utf-8")))
    return Stage(stage["name"], tuple(programs))


def encode_task(task: Task) -> dict[str, object]:
    if type(task) is not Task:
        raise ValueError("task_type")
    data = {"schema": SCHEMA, "name": task.name, "bits": task.bits,
            "inputs": list(task.inputs), "expected": list(task.expected), "anchor": list(task.anchor),
            "stages": [{"name": stage.name, "programs": [
                {"name": p.name, "source": p.source.decode("utf-8")} for p in stage.programs]}
                for stage in task.stages]}
    if decode_task(json.dumps(data, separators=(",", ":"))) != task:
        raise ValueError("task_not_roundtrippable")
    return data
