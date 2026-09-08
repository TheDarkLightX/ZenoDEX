"""Replay generated controllers through the native executable, retaining definitions."""

from __future__ import annotations

import json
import tempfile
import time
from pathlib import Path

from src.integration.tau_runner import _run_subprocess_with_output_caps

from .anchor import AnchoredRepair
from .anchor_export import export_anchor_tau
from .codec import export_tau
from .compiler import CompiledRepair
from .runtime import QueryRecord, TauQueryError, TauRuntime

Controller = CompiledRepair | AnchoredRepair


def _source(compiled: Controller) -> str:
    return export_anchor_tau(compiled) if isinstance(compiled, AnchoredRepair) else export_tau(compiled)


def replay_controller(
    runtime: TauRuntime, compiled: Controller, steps: tuple[dict[str, bool], ...],
) -> tuple[dict[str, bool], ...]:
    """Bounded native file-stream replay; unavailable output is never success.

    This bypasses the legacy host runner's definition-inlining subset and feeds
    the intact generated source to Tau. It performs no network operation.
    """
    if type(steps) is not tuple or not 1 <= len(steps) <= 4096:
        raise ValueError("trace_length_bound")
    for step in steps:
        compiled.contract.validate_values(step)
    runtime.check_subject()
    with tempfile.TemporaryDirectory(prefix="tau-composition-replay-") as directory:
        root = Path(directory)
        declarations = _write_streams(root, compiled, steps)
        source = root / "controller.tau"
        source.write_text("\n".join(declarations) + "\n" + _source(compiled), encoding="utf-8")
        started = time.perf_counter()
        rc, stdout, stderr = _run_subprocess_with_output_caps(
            [str(runtime.binary), "--charvar", "false", "--severity", "error", str(source)],
            input_text="", cwd=root, timeout_s=runtime.timeout_seconds,
            max_stdout_bytes=32_000, max_stderr_bytes=16_000,
        )
        runtime.records.append(QueryRecord(
            "execute", _source(compiled) + "\n# Input rows: " + json.dumps(steps, sort_keys=True),
            stdout, stderr, time.perf_counter() - started, runtime.binary_sha256,
        ))
        if rc != 0 or "error" in (stdout + stderr).lower():
            raise TauQueryError("native_replay_failed")
        try:
            outputs = _read_outputs(root, compiled, len(steps))
        except TauQueryError as exc:
            if exc.code != "native_single_step_trace" or len(steps) == 1:
                raise
            # Tau elides irrelevant inputs for constant controllers. Replay
            # every row in a new invocation; never manufacture repeated outputs.
            return tuple(replay_controller(runtime, compiled, (step,))[0] for step in steps)
    for step, actual in zip(steps, outputs, strict=True):
        expected = compiled.propose(step)
        if any(actual[name] != expected[name] for name in compiled.contract.controls):
            raise TauQueryError("native_replay_disagreement")
    return outputs


def _write_streams(root: Path, compiled: Controller, steps: tuple[dict[str, bool], ...]) -> list[str]:
    declarations = []
    names = compiled.contract.environment + compiled.contract.controls
    for index, name in enumerate(names, 1):
        filename = f"input{index}.txt"
        (root / filename).write_text("\n".join(str(int(step[name])) for step in steps) + "\n", encoding="utf-8")
        declarations.append(f'i{index}:sbf := in file("{filename}").')
    for index, _ in enumerate(compiled.contract.controls, 1):
        declarations.append(f'o{index}:sbf := out file("output{index}.txt").')
    return declarations


def _read_outputs(root: Path, compiled: Controller, count: int) -> tuple[dict[str, bool], ...]:
    result: list[dict[str, bool]] = [{} for _ in range(count)]
    for index, name in enumerate(compiled.contract.controls, 1):
        path = root / f"output{index}.txt"
        if not path.is_file() or path.stat().st_size > count * 4 + 100:
            raise TauQueryError("native_output_missing_or_large")
        values = path.read_text(encoding="utf-8").splitlines()
        if len(values) == 1 and count > 1 and values[0] in {"0", "1"}:
            raise TauQueryError("native_single_step_trace")
        if len(values) != count or any(value not in {"0", "1"} for value in values):
            raise TauQueryError("native_trace_shape")
        for step, value in zip(result, values, strict=True):
            step[name] = value == "1"
    return tuple(result)
