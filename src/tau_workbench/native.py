"""Independent CPython replay of the exact admitted source artifacts.

The source profile is checked over the entire closed domain before any source
is loaded. This is a bounded experiment, not an unrestricted Python sandbox.
IO and child processes live only in this shell module.
"""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from src.integration.tau_runner import _run_subprocess_with_output_caps
from src.tau_composition.codec import _unique_object

from .models import Task
from .programs import analyze

_RUNNER = '''import importlib.util, json, sys
from pathlib import Path
root = Path(__file__).resolve().parent
data = json.loads((root / "input.json").read_text())
stages = []
component_outputs = []
for names in data["files"]:
    functions = []
    tables = []
    for name in names:
        spec = importlib.util.spec_from_file_location(name[:-3], root / name)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        functions.append(module.transform)
        row = tuple(module.transform(x) for x in range(data["size"]))
        if any(type(x) is not int or not 0 <= x < data["size"] for x in row):
            raise ValueError("native_component_domain")
        tables.append(row)
    stages.append(functions)
    component_outputs.append(tables)
outcomes = []
pipeline_inputs_checked = 0
for bundle in data["bundles"]:
    first_failure = None
    for initial, expected in zip(data["inputs"], data["expected"], strict=True):
        pipeline_inputs_checked += 1
        value = initial
        for functions, code in zip(stages, bundle, strict=True):
            value = functions[code](value)
        if type(value) is not int or value != expected:
            first_failure = {"input": initial, "expected": expected, "observed": value}
            break
    outcomes.append(first_failure)
print(json.dumps({"component_outputs": component_outputs, "outcomes": outcomes,
                  "pipeline_inputs_checked": pipeline_inputs_checked}))
'''


@dataclass(frozen=True, slots=True)
class PipelineFailure:
    input: int
    expected: int
    observed: int


@dataclass(frozen=True, slots=True)
class NativeReplay:
    task_id: str
    bundle_sha256: str
    outcomes: tuple[PipelineFailure | None, ...]
    source_hashes: tuple[tuple[str, ...], ...]
    component_inputs_checked: int
    pipeline_inputs_checked: int
    runner_sha256: str


def replay_bundles(task: Task, bundles: tuple[tuple[int, ...], ...]) -> NativeReplay:
    """Check exact candidate indices; reanalyze sources before isolated loading."""
    _check_bundles(task, bundles)
    measured = tuple(tuple(analyze(program, task.bits).outputs for program in stage.programs)
                     for stage in task.stages)
    files = [[f"stage_{i}_candidate_{j}.py" for j in range(len(stage.programs))]
             for i, stage in enumerate(task.stages)]
    payload = {"files": files, "size": 1 << task.bits, "inputs": task.inputs,
               "expected": task.expected, "bundles": bundles}
    with tempfile.TemporaryDirectory(prefix="tau-workbench-") as directory:
        root = Path(directory)
        for stage, names in zip(task.stages, files, strict=True):
            for program, name in zip(stage.programs, names, strict=True):
                (root / name).write_bytes(program.source)
        (root / "input.json").write_text(json.dumps(payload), encoding="utf-8")
        (root / "runner.py").write_text(_RUNNER, encoding="utf-8")
        code, stdout, stderr = _run_subprocess_with_output_caps(
            [sys.executable, "-I", "-S", "-B", str(root / "runner.py")],
            input_text="", cwd=root, timeout_s=30,
            max_stdout_bytes=1_000_000, max_stderr_bytes=16_000,
        )
    if code != 0 or stderr:
        raise ValueError("native_replay_failed")
    observed = _decode_result(stdout, task, len(bundles))
    if observed[0] != measured:
        raise ValueError("interpreter_native_disagreement")
    if (observed[1], observed[2]) != _composed_outcomes(task, bundles, measured):
        raise ValueError("native_pipeline_disagreement")
    return NativeReplay(task.subject_id, hashlib.sha256(json.dumps(
                        bundles, separators=(",", ":")).encode()).hexdigest(), observed[1],
                        tuple(tuple(p.sha256 for p in s.programs) for s in task.stages),
                        sum(len(s.programs) for s in task.stages) * (1 << task.bits), observed[2],
                        hashlib.sha256(_RUNNER.encode()).hexdigest())


def _composed_outcomes(
    task: Task, bundles: tuple[tuple[int, ...], ...],
    tables: tuple[tuple[tuple[int, ...], ...], ...],
) -> tuple[tuple[PipelineFailure | None, ...], int]:
    outcomes: list[PipelineFailure | None] = []
    checked = 0
    for bundle in bundles:
        failure = None
        for initial, expected in zip(task.inputs, task.expected, strict=True):
            checked += 1
            value = initial
            for stage, code in zip(tables, bundle, strict=True):
                value = stage[code][value]
            if value != expected:
                failure = PipelineFailure(initial, expected, value)
                break
        outcomes.append(failure)
    return tuple(outcomes), checked


def _check_bundles(task: Task, bundles: tuple[tuple[int, ...], ...]) -> None:
    if type(task) is not Task or type(bundles) is not tuple or not 1 <= len(bundles) <= 4096:
        raise ValueError("native_bundle_bound")
    for bundle in bundles:
        if type(bundle) is not tuple or len(bundle) != len(task.stages):
            raise ValueError("native_bundle_shape")
        if any(type(code) is not int or not 0 <= code < len(stage.programs)
               for code, stage in zip(bundle, task.stages, strict=True)):
            raise ValueError("native_bundle_index")


def _decode_result(text: str, task: Task, count: int) -> tuple[
    tuple[tuple[tuple[int, ...], ...], ...], tuple[PipelineFailure | None, ...], int,
]:
    data = json.loads(text, object_pairs_hook=_unique_object)
    if type(data) is not dict or set(data) != {"component_outputs", "outcomes", "pipeline_inputs_checked"}:
        raise ValueError("native_result_shape")
    tables = data["component_outputs"]
    if type(tables) is not list or len(tables) != len(task.stages):
        raise ValueError("native_result_shape")
    frozen = []
    for rows, stage in zip(tables, task.stages, strict=True):
        if type(rows) is not list or len(rows) != len(stage.programs):
            raise ValueError("native_result_shape")
        for row in rows:
            if type(row) is not list or len(row) != 1 << task.bits:
                raise ValueError("native_result_shape")
            if any(type(v) is not int or not 0 <= v < 1 << task.bits for v in row):
                raise ValueError("native_result_value")
        frozen.append(tuple(tuple(row) for row in rows))
    outcomes = data["outcomes"]
    if type(outcomes) is not list or len(outcomes) != count:
        raise ValueError("native_result_shape")
    for outcome in outcomes:
        if outcome is not None and (type(outcome) is not dict or
                set(outcome) != {"input", "expected", "observed"} or
                any(type(v) is not int for v in outcome.values())):
            raise ValueError("native_outcome_shape")
    checked = data["pipeline_inputs_checked"]
    if type(checked) is not int or not count <= checked <= count * len(task.inputs):
        raise ValueError("native_input_count")
    decoded = tuple(None if o is None else PipelineFailure(o["input"], o["expected"], o["observed"])
                    for o in outcomes)
    return tuple(frozen), decoded, checked
