#!/usr/bin/env python3
"""Compile local choices for a human-directed swarm; stdout is structured JSON."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict
from pathlib import Path
from typing import NoReturn

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.tau_composition.codec import _unique_object, encode_contract  # noqa: E402
from src.tau_composition.resources import ExpressionBudgetError  # noqa: E402
from src.tau_composition.runtime import TauQueryError, TauRuntime  # noqa: E402
from src.tau_swarm.codec import (  # noqa: E402
    MAX_PROBLEM_BYTES,  # noqa: E402
    decode_problem,
    encode_problem,
)
from src.tau_swarm.codec import SCHEMA as PROBLEM_SCHEMA  # noqa: E402
from src.tau_swarm.compiler import AutonomyCompiler  # noqa: E402
from src.tau_swarm.examples import (  # noqa: E402
    asymmetric_choices,
    balanced_anchor,
    planning_swarm,
    triangle_choices,
)
from src.tau_swarm.exports import export_agent_gate  # noqa: E402
from src.tau_swarm.inspection import MAX_INSPECTION_BITS, inspect_envelope  # noqa: E402
from src.tau_swarm.models import SwarmProblem  # noqa: E402

EXAMPLES = ("planning", "asymmetric", "triangle")
MAX_ENVIRONMENT_BYTES = 16_000


class JsonArgumentParser(argparse.ArgumentParser):
    """Turn argparse failures into typed invalid-input values, never exits."""

    def error(self, message: str) -> NoReturn:
        raise ValueError("argument_error: " + message)


def parser() -> argparse.ArgumentParser:
    result = JsonArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    commands.add_parser("describe")
    sample = commands.add_parser("example")
    sample.add_argument("name", choices=EXAMPLES)
    sample.add_argument("--balanced-anchor", action="store_true")
    compile_command = commands.add_parser("compile")
    source = compile_command.add_mutually_exclusive_group(required=True)
    source.add_argument("--problem", type=Path)
    source.add_argument("--example", choices=EXAMPLES)
    compile_command.add_argument("--balanced-anchor", action="store_true")
    compile_command.add_argument(
        "--order", help="Comma-separated full permutation of agent names.")
    compile_command.add_argument("--tau", type=Path, required=True)
    compile_command.add_argument("--timeout-seconds", type=float, default=10.0)
    compile_command.add_argument(
        "--environment", help="Exact Boolean environment JSON for bounded inspection.")
    compile_command.add_argument(
        "--out", type=Path, help="New directory for generated research artifacts.")
    return result


def describe() -> dict[str, object]:
    """Derive the accepted commands and options from the real parser."""
    commands: dict[str, object] = {}
    for action in parser()._actions:
        if isinstance(action, argparse._SubParsersAction):
            for name, command in action.choices.items():
                commands[name] = [
                    {"name": item.dest, "flags": list(item.option_strings),
                     "required": bool(item.required),
                     "choices": None if item.choices is None else list(item.choices)}
                    for item in command._actions if item.dest != "help"
                ]
    return {
        "schema": "tau-swarm/cli-v1", "commands": commands,
        "problem_schema": PROBLEM_SCHEMA, "examples": list(EXAMPLES),
        "authority": "NONE", "runtime_mounted": False,
        "effects": {"describe": "stdout_only", "example": "stdout_only",
                    "compile": "temporary native Tau processes and files",
                    "out": "writes artifacts to a new directory"},
        "artifacts": ["problem.json", "report.json", "native_queries.json",
                      "agent_NN.tau", "agent_NN.contract.json",
                      "inspection.json (only with --environment)"],
        "exit_codes": {"0": "completed", "2": "invalid_input", "3": "UNKNOWN"},
        "limits": {"problem_bytes": MAX_PROBLEM_BYTES,
                   "environment_bytes": MAX_ENVIRONMENT_BYTES,
                   "inspection_control_bits": MAX_INSPECTION_BITS,
                   "agent_blocks": 16},
        "recovery": "Choose an explicit compatible Tau binary; revise unsupported "
                    "inputs; retry into a new directory.",
        "nonclaims": ["maximum product size", "agent execution",
                      "generated-code correctness", "Tau Net admission",
                      "settlement authority", "legal clearance"],
    }


def example(name: str, balanced: bool = False) -> SwarmProblem:
    factories = {"planning": planning_swarm, "asymmetric": asymmetric_choices,
                 "triangle": triangle_choices}
    if name not in factories:
        raise ValueError("unknown_example")
    problem = factories[name]()
    if balanced:
        if name != "triangle":
            raise ValueError("balanced_anchor_requires_triangle")
        return SwarmProblem(problem.contract, problem.blocks, balanced_anchor(problem))
    return problem


def _read_problem(args: argparse.Namespace) -> SwarmProblem:
    if args.problem is None:
        return example(args.example, args.balanced_anchor)
    if args.balanced_anchor:
        raise ValueError("balanced_anchor_requires_triangle_example")
    with args.problem.open("rb") as stream:
        payload = stream.read(MAX_PROBLEM_BYTES + 1)
    if len(payload) > MAX_PROBLEM_BYTES:
        raise ValueError("problem_byte_bound")
    return decode_problem(payload.decode("utf-8"))


def _order(text: str | None, problem: SwarmProblem) -> tuple[str, ...] | None:
    """Reject a non-permutation before any native process is started."""
    if text is None:
        return None
    order = tuple(text.split(","))
    names = tuple(block.name for block in problem.blocks)
    if len(order) != len(names) or set(order) != set(names):
        raise ValueError("expansion_order_permutation")
    return order


def _environment(text: str | None, problem: SwarmProblem) -> dict[str, bool] | None:
    if text is None:
        return None
    if len(text.encode("utf-8")) > MAX_ENVIRONMENT_BYTES:
        raise ValueError("environment_byte_bound")
    values = json.loads(text, object_pairs_hook=_unique_object)
    if type(values) is not dict or set(values) != set(problem.contract.environment):
        raise ValueError("inspection_environment_fields")
    if any(type(value) is not bool for value in values.values()):
        raise ValueError("exact_boolean_required")
    if len(problem.contract.controls) > MAX_INSPECTION_BITS:
        raise ValueError("inspection_bit_bound")
    return values


def _canonical(payload: object) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _write_artifacts(directory: Path, artifacts: dict[str, object]) -> None:
    directory.mkdir(parents=True, exist_ok=False)
    for name, value in artifacts.items():
        text = value if isinstance(value, str) else (
            json.dumps(value, indent=2, sort_keys=True) + "\n")
        (directory / name).write_bytes(text.encode("utf-8"))


def _records(runtime: TauRuntime) -> list[dict[str, object]]:
    return [asdict(record) for record in runtime.records]


def _record_labels(runtime: TauRuntime) -> list[dict[str, object]]:
    """Return fixed summary fields; full transcripts require --out."""
    return [{"index": index, "operation": record.operation,
             "binary_sha256": record.binary_sha256,
             "query_sha256": hashlib.sha256(record.query.encode("utf-8")).hexdigest()}
            for index, record in enumerate(runtime.records)]


def _compile(args: argparse.Namespace) -> dict[str, object]:
    problem = _read_problem(args)
    environment = _environment(args.environment, problem)
    order = _order(args.order, problem)
    if args.out is not None and args.out.exists():
        raise ValueError("output_directory_exists")
    runtime = TauRuntime(args.tau, timeout_seconds=args.timeout_seconds)
    envelope = AutonomyCompiler(runtime).compile(problem, order)
    encoded = encode_problem(problem)
    artifacts: dict[str, object] = {"problem.json": encoded}
    domains = []
    for index, domain in enumerate(envelope.domains):
        source = export_agent_gate(envelope, domain.block.name)
        prefix = f"agent_{index:02d}"
        artifacts[prefix + ".tau"] = source
        artifacts[prefix + ".contract.json"] = encode_contract(
            envelope.local_contract(domain.block.name))
        domains.append({
            "agent": domain.block.name, "controls": list(domain.block.controls),
            "input_order": list(problem.contract.environment + domain.block.controls),
            "output": "o1 = local domain compatibility",
            "residual": domain.residual.canonical_data(),
            "gate_file": prefix + ".tau", "contract_file": prefix + ".contract.json",
            "gate_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest()})
    report: dict[str, object] = {
        "schema": "tau-swarm/result-v1", "status": "compiled_native_checked",
        "authority": "NONE", "runtime_mounted": False,
        "envelope_id": envelope.subject_id,
        "problem_sha256": hashlib.sha256(_canonical(encoded).encode("utf-8")).hexdigest(),
        "binary_sha256": envelope.binary_sha256,
        "native_queries": envelope.native_queries,
        "native_records": _record_labels(runtime),
        "native_records_artifact": "native_queries.json" if args.out is not None else None,
        "expansion_order": list(envelope.expansion_order), "domains": domains,
        "checked_properties": ["product safety", "retained common anchor",
                               "exact final universal cofactors"],
        "scope": "fixed formal contract; factorwise inclusion-maximal product of "
                 "independent choices",
        "nonclaims": describe()["nonclaims"],
    }
    if environment is not None:
        inspection = inspect_envelope(envelope, environment)
        report["inspection"] = inspection
        artifacts["inspection.json"] = inspection
    artifacts["native_queries.json"] = _records(runtime)
    if args.out is not None:
        report["output_directory"] = str(args.out)
        report["artifacts"] = sorted([*artifacts, "report.json"])
    artifacts["report.json"] = report
    if args.out is not None:
        _write_artifacts(args.out, artifacts)
    return report


def main(argv: list[str] | None = None) -> int:
    try:
        args = parser().parse_args(argv)
        if args.command == "describe":
            result: object = describe()
        elif args.command == "example":
            result = encode_problem(example(args.name, args.balanced_anchor))
        else:
            result = _compile(args)
    except (TauQueryError, ExpressionBudgetError) as exc:
        print(json.dumps({"status": "UNKNOWN", "error_code": str(exc),
                          "authority": "NONE"}, sort_keys=True))
        return 3
    except (ValueError, OSError, TypeError, RecursionError) as exc:
        print(json.dumps({"status": "invalid_input", "error_code": str(exc),
                          "authority": "NONE"}, sort_keys=True))
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
