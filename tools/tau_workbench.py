#!/usr/bin/env python3
"""Compile finite Tau workbench domains and emit source-bound JSON evidence.

This command performs the restricted local program interpretation supplied by
the workbench and native Tau queries supplied by ``compile_task``.  It never
loads candidate source into CPython.  An optional output directory is created
only after all input checks and native compilation succeed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from dataclasses import asdict
from pathlib import Path
from typing import NoReturn

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.tau_composition.resources import ExpressionBudgetError  # noqa: E402
from src.tau_composition.runtime import TauQueryError, TauRuntime  # noqa: E402
from src.tau_swarm.exports import export_agent_gate  # noqa: E402
from src.tau_workbench.codec import MAX_TASK_BYTES, decode_task, encode_task  # noqa: E402
from src.tau_workbench.compiler import CompiledWorkbench, compile_task  # noqa: E402
from src.tau_workbench.examples import message_task  # noqa: E402
from src.tau_workbench.models import Task  # noqa: E402
from src.tau_workbench.programs import (  # noqa: E402
    MAX_AST_DEPTH,
    MAX_AST_NODES,
    MAX_BITS,
    MAX_LITERAL_VALUE,
    MAX_NAME_LENGTH,
    MAX_SHIFT,
    MAX_SOURCE_BYTES,
    MIN_BITS,
)

CLI_SCHEMA = "tau-workbench/cli-v1"
RESULT_SCHEMA = "tau-workbench/compile-v1"
MAX_STAGES = 4
MAX_PROGRAMS_PER_STAGE = 32
NONCLAIMS = (
    "No CPython candidate-source replay is performed by this CLI.",
    "No unrestricted Python sandbox or general-purpose program correctness claim.",
    "No novelty or prior-art determination.",
    "No maximum-volume, throughput, or scalability claim.",
    "No Tau Net admission, settlement, release, product, or production authority.",
)


class JsonArgumentParser(argparse.ArgumentParser):
    """Turn argparse failures into stable invalid-input values."""

    def error(self, message: str) -> NoReturn:
        raise ValueError("argument_error: " + message)


def parser() -> argparse.ArgumentParser:
    """Build the single parser used both for execution and discovery output."""

    result = JsonArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    commands.add_parser("describe")
    commands.add_parser("example")
    compile_command = commands.add_parser("compile")
    compile_command.add_argument("--task", type=Path)
    compile_command.add_argument("--tau", type=Path, required=True)
    compile_command.add_argument(
        "--order", nargs="+", metavar="STAGE",
        help="Full stage permutation, supplied as names or comma-separated names.",
    )
    compile_command.add_argument("--out", type=Path)
    return result


def _describe_action(action: argparse.Action) -> dict[str, object]:
    choices = action.choices
    return {
        "name": action.dest,
        "flags": list(action.option_strings),
        "required": bool(action.required),
        "nargs": action.nargs,
        "choices": None if choices is None else list(choices),
    }


def _describe_commands() -> dict[str, list[dict[str, object]]]:
    commands: dict[str, list[dict[str, object]]] = {}
    for action in parser()._actions:
        if not isinstance(action, argparse._SubParsersAction):
            continue
        for name, command in action.choices.items():
            commands[name] = [
                _describe_action(item)
                for item in command._actions
                if item.dest != "help"
            ]
    return commands


def describe() -> dict[str, object]:
    """Return parser-derived commands plus the bounded effect contract."""

    return {
        "schema": CLI_SCHEMA,
        "commands": _describe_commands(),
        "authority": "NONE",
        "runtime_mounted": False,
        "effects": {
            "describe": {"stdout": True, "filesystem": False, "native_tau": False},
            "example": {"stdout": True, "filesystem": False, "native_tau": False},
            "compile": {
                "stdout": True,
                "temporary_native_tau_queries": True,
                "candidate_source_execution": False,
                "output_directory": "optional fresh directory only",
            },
        },
        "limits": {
            "task_bytes": MAX_TASK_BYTES,
            "source_bytes": MAX_SOURCE_BYTES,
            "program_name_length": MAX_NAME_LENGTH,
            "ast_nodes": MAX_AST_NODES,
            "ast_depth": MAX_AST_DEPTH,
            "literal_value": [0, MAX_LITERAL_VALUE],
            "shift": [0, MAX_SHIFT],
            "bits": [MIN_BITS, MAX_BITS],
            "stages": [1, MAX_STAGES],
            "programs_per_stage": [1, MAX_PROGRAMS_PER_STAGE],
        },
        "artifacts": [
            "task.json",
            "report.json",
            "native_queries.json",
            "stage_NN.tau",
            "stage_NN_candidate_MM.py",
        ],
        "exit_codes": {"0": "completed", "2": "invalid_input", "3": "UNKNOWN"},
        "nonclaims": list(NONCLAIMS),
    }


def _read_task(path: Path | None) -> Task:
    if path is None:
        return message_task()
    try:
        with path.open("rb") as stream:
            payload = stream.read(MAX_TASK_BYTES + 1)
    except OSError as exc:
        raise ValueError("task_file") from exc
    if len(payload) > MAX_TASK_BYTES:
        raise ValueError("task_byte_bound")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError("task_encoding") from exc
    try:
        return decode_task(text)
    except json.JSONDecodeError as exc:
        raise ValueError("task_json") from exc
    except RecursionError as exc:
        raise ValueError("task_malformed_data") from exc


def _parse_order(values: list[str] | None, task: Task) -> tuple[str, ...] | None:
    if values is None:
        return None
    pieces = tuple(piece for value in values for piece in value.split(","))
    names = tuple(stage.name for stage in task.stages)
    if len(pieces) != len(names) or set(pieces) != set(names):
        raise ValueError("order_permutation")
    return pieces


def _validate_tau_path(path: Path) -> Path:
    try:
        resolved = path.expanduser().resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise ValueError("tau_binary") from exc
    if not resolved.is_file() or not os.access(resolved, os.X_OK):
        raise ValueError("tau_binary")
    return resolved


def _validate_output_path(path: Path | None) -> Path | None:
    if path is None:
        return None
    if path.exists():
        raise ValueError("output_directory_exists")
    parent = path.parent
    if not parent.exists() or not parent.is_dir():
        raise ValueError("output_parent_missing")
    return path


def _json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


def _query_labels(runtime: TauRuntime) -> list[dict[str, object]]:
    return [
        {
            "index": index,
            "operation": record.operation,
            "binary_sha256": record.binary_sha256,
            "query_sha256": hashlib.sha256(record.query.encode("utf-8")).hexdigest(),
        }
        for index, record in enumerate(runtime.records)
    ]


def _class_code(compiled: CompiledWorkbench, stage_index: int, program_name: str) -> int:
    for code, behavior_class in enumerate(compiled.catalog.stages[stage_index]):
        if any(program.name == program_name for program in behavior_class.members):
            return code
    raise RuntimeError("compiled catalog lost candidate")


def _candidate_rows(
    compiled: CompiledWorkbench,
    artifacts: dict[str, bytes],
) -> tuple[list[dict[str, object]], int, int]:
    task = compiled.catalog.task
    stage_rows: list[dict[str, object]] = []
    candidate_count = 0
    admitted_count = 0
    for stage_index, stage in enumerate(task.stages):
        admitted_codes = compiled.domains[stage_index]
        admitted_set = frozenset(admitted_codes)
        candidates: list[dict[str, object]] = []
        for candidate_index, program in enumerate(stage.programs):
            candidate_count += 1
            code = _class_code(compiled, stage_index, program.name)
            if code not in admitted_set:
                continue
            admitted_count += 1
            filename = f"stage_{stage_index:02d}_candidate_{candidate_index:02d}.py"
            artifacts[filename] = program.source
            digest = program.sha256
            candidates.append({
                "candidate_index": candidate_index,
                "class_code": code,
                "name": program.name,
                "sha256": digest,
                "source_sha256": digest,
                "file": filename,
            })
        admitted_classes = [
            {
                "class_code": code,
                "candidate_count": sum(
                    1 for candidate in candidates if candidate["class_code"] == code
                ),
                "candidates": [
                    candidate for candidate in candidates if candidate["class_code"] == code
                ],
            }
            for code in admitted_codes
        ]
        stage_rows.append({
            "stage_index": stage_index,
            "name": stage.name,
            "admitted_class_codes": list(admitted_codes),
            "candidates": candidates,
            "admitted_classes": admitted_classes,
            "admitted_candidate_count": len(candidates),
        })
    return stage_rows, candidate_count, admitted_count


def _prepare_artifacts(
    compiled: CompiledWorkbench, runtime: TauRuntime, output: Path | None,
) -> tuple[dict[str, object], dict[str, bytes]]:
    task = compiled.catalog.task
    encoded_task = encode_task(task)
    artifacts: dict[str, bytes] = {"task.json": _json_bytes(encoded_task)}
    stage_rows, candidate_count, admitted_count = _candidate_rows(compiled, artifacts)
    for stage_index, stage in enumerate(task.stages):
        filename = f"stage_{stage_index:02d}.tau"
        source = export_agent_gate(compiled.envelope, stage.name).encode("utf-8")
        artifacts[filename] = source
        stage_rows[stage_index]["gate_file"] = filename
        stage_rows[stage_index]["gate_sha256"] = hashlib.sha256(source).hexdigest()
    records = [asdict(record) for record in runtime.records]
    artifacts["native_queries.json"] = _json_bytes(records)
    report: dict[str, object] = {
        "schema": RESULT_SCHEMA,
        "status": "compiled_native_checked",
        "authority": "NONE",
        "runtime_mounted": False,
        "task_id": task.subject_id,
        "task_name": task.name,
        "bits": task.bits,
        "domain_size": 1 << task.bits,
        "expansion_order": list(compiled.envelope.expansion_order),
        "stages": stage_rows,
        "source_counts": {
            "candidate_sources": candidate_count,
            "admitted_candidate_sources": admitted_count,
            "source_input_evaluations": candidate_count * (1 << task.bits),
            "domain_values_per_source": 1 << task.bits,
        },
        "binary_sha256": compiled.envelope.binary_sha256,
        "native_queries": compiled.envelope.native_queries,
        "native_query_labels": _query_labels(runtime),
        "native_queries_artifact": "native_queries.json" if output is not None else None,
        "nonclaims": list(NONCLAIMS),
    }
    if output is not None:
        report["artifacts"] = sorted((*artifacts, "report.json"))
    else:
        report["artifacts"] = []
    artifacts["report.json"] = _json_bytes(report)
    return report, artifacts


def _write_artifacts(output: Path, artifacts: dict[str, bytes]) -> None:
    try:
        output.mkdir(parents=False, exist_ok=False)
    except FileExistsError as exc:
        raise ValueError("output_directory_exists") from exc
    for filename in sorted(artifacts, key=lambda name: (name == "report.json", name)):
        (output / filename).write_bytes(artifacts[filename])


def _compile(args: argparse.Namespace) -> dict[str, object]:
    task = _read_task(args.task)
    order = _parse_order(args.order, task)
    output = _validate_output_path(args.out)
    tau_path = _validate_tau_path(args.tau)
    runtime = TauRuntime(tau_path)
    compiled = compile_task(task, runtime, order)
    report, artifacts = _prepare_artifacts(compiled, runtime, output)
    if output is not None:
        _write_artifacts(output, artifacts)
    return report


def _error_payload(status: str, code: str) -> dict[str, object]:
    return {"status": status, "error_code": code, "authority": "NONE"}


def main(argv: list[str] | None = None) -> int:
    try:
        args = parser().parse_args(argv)
        if args.command == "describe":
            result: object = describe()
        elif args.command == "example":
            result = encode_task(message_task())
        else:
            result = _compile(args)
    except (TauQueryError, ExpressionBudgetError) as exc:
        print(json.dumps(_error_payload("UNKNOWN", str(exc)), sort_keys=True))
        return 3
    except (OSError, TypeError, ValueError, RecursionError) as exc:
        print(json.dumps(_error_payload("invalid_input", str(exc)), sort_keys=True))
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
