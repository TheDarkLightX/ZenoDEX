#!/usr/bin/env python3
"""Compile original Boolean proposal contracts using a separately installed Tau.

Stdout is JSON. Exit 0: requested research operation completed; 2: invalid input;
3: native result unavailable/unsupported. Outputs never authorize an effect.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.tau_composition.anchor import AnchorCompiler, zero_anchor  # noqa: E402
from src.tau_composition.anchor_export import export_anchor_tau  # noqa: E402
from src.tau_composition.codec import decode_contract, encode_contract, export_tau  # noqa: E402
from src.tau_composition.compiler import RepairCompiler  # noqa: E402
from src.tau_composition.examples import example  # noqa: E402
from src.tau_composition.models import Contract  # noqa: E402
from src.tau_composition.resources import ExpressionBudgetError  # noqa: E402
from src.tau_composition.runtime import TauQueryError, TauRuntime  # noqa: E402

EXAMPLES = ("coupled_recovery", "conditional_cycle", "action_permissions", "permission_chain", "exclusion_pairs")


def describe() -> dict[str, object]:
    return {
        "schema": "tau-composition/cli-v1",
        "commands": ["describe", "example", "compile"],
        "examples": list(EXAMPLES),
        "contract_schema": "tau-composition/contract-v1",
        "native_primitives": ["lgrs", "valid", "qelim"],
        "algorithms": ["native local retractions with preservation graph and SCC merge",
                       "bounded exact order covers", "shared residual with a native-checked common anchor"],
        "domain": "Boolean equations and exact Boolean application inputs",
        "effects": {"default": "stdout_only", "out": "writes generated research artifacts"},
        "authority": "NONE",
        "exit_codes": {"0": "completed", "2": "invalid_input", "3": "native_unknown_or_unsupported"},
        "recovery": "Supply an explicitly chosen compatible Tau binary; inspect unsupported results; retain native logs.",
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    commands.add_parser("describe")
    sample = commands.add_parser("example", help="Print a reusable contract JSON example.")
    sample.add_argument("name", choices=EXAMPLES)
    sample.add_argument("--size", type=int, default=8)
    compile_command = commands.add_parser("compile", help="Compile and check an advisory repair map.")
    inputs = compile_command.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--contract", type=Path)
    inputs.add_argument("--example", choices=EXAMPLES)
    compile_command.add_argument("--size", type=int, default=8)
    compile_command.add_argument("--tau", type=Path, required=True)
    compile_command.add_argument("--timeout-seconds", type=float, default=10.0)
    mode = compile_command.add_mutually_exclusive_group()
    mode.add_argument("--two-order-cover", action="store_true",
                      help="For two requirements, check both orders and glue their guarded maps.")
    mode.add_argument("--zero-anchor", action="store_true",
                      help="Check the all-zero fallback and export a shared residual; invalid proposals reset to it.")
    compile_command.add_argument("--out", type=Path, help="New directory for contract, controller and native-query evidence.")
    return result


def _read_contract(args: argparse.Namespace) -> Contract:
    if args.contract is not None:
        if args.contract.stat().st_size > 256_000:
            raise ValueError("contract_byte_bound")
        return decode_contract(args.contract.read_text(encoding="utf-8"))
    return example(args.example, args.size)


def _write_artifacts(directory: Path, artifacts: dict[str, object]) -> None:
    # Exclusive directory creation prevents overwriting a prior study or user work.
    directory.mkdir(parents=True, exist_ok=False)
    for name, content in artifacts.items():
        text = content if isinstance(content, str) else json.dumps(content, indent=2, sort_keys=True) + "\n"
        (directory / name).write_text(text, encoding="utf-8")


def _compile(args: argparse.Namespace) -> dict[str, object]:
    contract = _read_contract(args)
    runtime = TauRuntime(args.tau, timeout_seconds=args.timeout_seconds)
    if args.zero_anchor:
        anchored = AnchorCompiler(runtime).compile(contract, zero_anchor(contract))
        source = export_anchor_tau(anchored)
        details = {
            "representation": "shared_residual_and_anchor",
            "native_queries": anchored.native_queries, "cache_hits": anchored.cache_hits,
            "anchor": {name: term.canonical_data() for name, term in anchored.anchor.assignments},
        }
    else:
        compiler = RepairCompiler(runtime)
        compiled = (compiler.compile_guarded_cover(contract, ((0, 1), (1, 0)))
                    if args.two_order_cover else compiler.compile(contract))
        source = export_tau(compiled)
        details = {
            "representation": "composed_polynomial_map",
            "groups": compiled.groups, "dependency_edges": compiled.dependency_edges,
            "schedule": compiled.schedule, "merge_rounds": compiled.merge_rounds,
            "alternative_orders": compiled.alternative_orders,
            "order_guards": [term.canonical_data() for term in compiled.order_guards],
            "native_queries": compiled.native_queries, "cache_hits": compiled.cache_hits,
            "repair": {name: term.canonical_data() for name, term in compiled.repair.assignments},
        }
    report = {
        "schema": "tau-composition/result-v1", "status": "compiled_native_checked",
        "authority": "NONE", "runtime_mounted": False,
        "contract": encode_contract(contract),
        "binary_sha256": runtime.binary_sha256,
        "controller_sha256": hashlib.sha256(source.encode()).hexdigest(),
        **details,
        "nonclaims": ["settlement authority", "network rule acceptance", "production readiness",
                      "minimum edit distance", "novel theorem", "legal clearance"],
    }
    if args.out is not None:
        _write_artifacts(args.out, {
            "contract.json": encode_contract(contract), "controller.tau": source,
            "report.json": report, "native_queries.json": [asdict(item) for item in runtime.records],
        })
    return report


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        if args.command == "describe":
            result = describe()
        elif args.command == "example":
            result = encode_contract(example(args.name, args.size))
        else:
            result = _compile(args)
    except (TauQueryError, ExpressionBudgetError) as exc:
        print(json.dumps({"status": "UNKNOWN", "error_code": str(exc), "authority": "NONE"}, sort_keys=True))
        return 3
    except (ValueError, OSError, TypeError, RecursionError) as exc:
        print(json.dumps({"status": "invalid_input", "error_code": str(exc), "authority": "NONE"}, sort_keys=True))
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
