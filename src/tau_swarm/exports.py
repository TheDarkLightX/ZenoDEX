"""Standalone advisory Tau choice gates and bounded native file-stream replay."""

from __future__ import annotations

import json
import re
import tempfile
import time
from pathlib import Path

from src.integration.tau_runner import _run_subprocess_with_output_caps
from src.tau_composition.models import Contract
from src.tau_composition.resources import check_terms
from src.tau_composition.runtime import QueryRecord, TauQueryError, TauRuntime
from src.tau_composition.terms import negate

from .models import AutonomyEnvelope

_MAX_GATE_BYTES = 256_000
_MAX_TRACE_STEPS = 4096
_NATIVE_ERROR = re.compile(r"\b(?:error|exception)\b", re.IGNORECASE)


def export_agent_gate(envelope: AutonomyEnvelope, agent: str) -> str:
    """Render an independent same-step gate for exact host Boolean choices.

    Inputs follow environment then owned-control tuple order. The sole output
    o1 is the complement of the local residual: 1 means formal compatibility.
    This artifact confers no credentials or external execution authority.
    """
    contract = envelope.local_contract(agent)
    names = contract.environment + contract.controls
    symbols = {name: f"v{index}" for index, name in enumerate(names)}
    permit = negate(contract.residual)
    check_terms((permit,))
    lines = [
        f"# Original Tau choice gate for human-directed swarm agent {agent}.",
        "# Exact host Boolean inputs; o1 = 1 means formal compatibility.",
        "# authority: NONE. Human and runtime execution checks remain separate.",
        "# Generic local stream artifact for independently proposed choices.",
    ]
    for index, name in enumerate(names, 1):
        role = "environment" if name in contract.environment else "choice"
        lines.append(f"# i{index}: {role} {name} (sbf)")
    lines.append("# o1: local domain compatibility (sbf)")
    arguments = ", ".join(symbols[name] for name in names)
    inputs = ", ".join(f"i{index}[t]:sbf" for index in range(1, len(names) + 1))
    lines.append(f"permit({arguments}):sbf := {permit.to_tau(symbols)}.")
    lines.append(f"always (o1[t]:sbf = permit({inputs})).")
    source = "\n".join(lines) + "\n"
    if len(source.encode("utf-8")) > _MAX_GATE_BYTES:
        raise ValueError("agent_gate_byte_bound")
    return source


def replay_agent_gate(
    runtime: TauRuntime, envelope: AutonomyEnvelope, agent: str,
    steps: tuple[dict[str, bool], ...],
) -> tuple[bool, ...]:
    """Replay 1..4096 local rows, returning only observed and checked bits.

    Invalid inputs reject before IO. Native errors, unavailable output and
    disagreement are UNKNOWN via TauQueryError. All file IO is temporary.
    """
    contract = envelope.local_contract(agent)
    rows = _snapshot_rows(contract, steps)
    source = export_agent_gate(envelope, agent)
    names = contract.environment + contract.controls
    try:
        outputs = _execute_gate(runtime, source, names, rows)
    except TauQueryError as exc:
        if exc.code != "native_gate_single_step_trace" or len(rows) == 1:
            raise
        # Tau can elide every input of a constant gate. Every row still needs
        # an actual native run; this same-step artifact has no hidden history.
        outputs = tuple(_execute_gate(runtime, source, names, (row,))[0] for row in rows)
    expected = tuple(envelope.permits(agent, row) for row in rows)
    if outputs != expected:
        raise TauQueryError("native_gate_replay_disagreement")
    return outputs


def _snapshot_rows(contract: Contract, steps: tuple[dict[str, bool], ...]) -> tuple[dict[str, bool], ...]:
    if type(steps) is not tuple or not 1 <= len(steps) <= _MAX_TRACE_STEPS:
        raise ValueError("trace_length_bound")
    if any(type(step) is not dict for step in steps):
        raise ValueError("trace_row_shape")
    rows = tuple(dict(step) for step in steps)
    for row in rows:
        contract.validate_values(row)
    return rows


def _execute_gate(
    runtime: TauRuntime, source: str, names: tuple[str, ...], rows: tuple[dict[str, bool], ...],
) -> tuple[bool, ...]:
    runtime.check_subject()
    with tempfile.TemporaryDirectory(prefix="tau-swarm-gate-") as directory:
        root = Path(directory)
        declarations = _write_inputs(root, names, rows)
        declarations.append('o1:sbf := out file("permit.txt").')
        path = root / "gate.tau"
        path.write_text("\n".join(declarations) + "\n" + source, encoding="utf-8")
        started = time.perf_counter()
        rc, stdout, stderr = _run_subprocess_with_output_caps(
            [str(runtime.binary), "--charvar", "false", "--severity", "error", str(path)],
            input_text="", cwd=root, timeout_s=runtime.timeout_seconds,
            max_stdout_bytes=32_000, max_stderr_bytes=16_000,
        )
        runtime.records.append(QueryRecord(
            "execute_agent_gate", source + "\n# Input rows: " + json.dumps(rows, sort_keys=True),
            stdout, stderr, time.perf_counter() - started, runtime.binary_sha256,
        ))
        if rc != 0:
            reason = "native_timeout" if "timed out" in stderr else "native_gate_replay_failed"
            raise TauQueryError(reason)
        if _NATIVE_ERROR.search(stdout + " " + stderr):
            raise TauQueryError("native_gate_replay_failed")
        return _read_permits(root / "permit.txt", len(rows))


def _write_inputs(root: Path, names: tuple[str, ...], rows: tuple[dict[str, bool], ...]) -> list[str]:
    declarations = []
    for index, name in enumerate(names, 1):
        filename = f"input{index}.txt"
        text = "\n".join("1" if row[name] else "0" for row in rows) + "\n"
        (root / filename).write_text(text, encoding="ascii")
        declarations.append(f'i{index}:sbf := in file("{filename}").')
    return declarations


def _read_permits(path: Path, count: int) -> tuple[bool, ...]:
    if not path.is_file() or path.stat().st_size > count * 4 + 100:
        raise TauQueryError("native_gate_output_missing_or_large")
    payload = path.read_bytes()
    if not payload.endswith(b"\n"):
        raise TauQueryError("native_gate_trace_shape")
    values = payload.split(b"\n")[:-1]
    if any(value not in {b"0", b"1"} for value in values):
        raise TauQueryError("native_gate_trace_shape")
    if len(values) == 1 and count > 1:
        raise TauQueryError("native_gate_single_step_trace")
    if len(values) != count:
        raise TauQueryError("native_gate_trace_shape")
    return tuple(value == b"1" for value in values)
