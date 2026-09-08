#!/usr/bin/env python3
"""Replay seven fixed Tau Swarm examples against independent finite relations."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from collections.abc import Callable
from dataclasses import asdict, dataclass
from itertools import product
from math import prod
from pathlib import Path
from typing import Any, cast

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.tau_composition.codec import encode_contract  # noqa: E402
from src.tau_composition.resources import ExpressionBudgetError  # noqa: E402
from src.tau_composition.runtime import TauQueryError, TauRuntime  # noqa: E402
from src.tau_swarm.codec import encode_problem  # noqa: E402
from src.tau_swarm.compiler import AutonomyCompiler  # noqa: E402
from src.tau_swarm.exports import export_agent_gate, replay_agent_gate  # noqa: E402
from src.tau_swarm.inspection import inspect_envelope  # noqa: E402
from src.tau_swarm.models import AgentBlock, AutonomyEnvelope, SwarmProblem  # noqa: E402
from tools.tau_swarm import JsonArgumentParser, _write_artifacts, example  # noqa: E402


class EvidenceMismatch(RuntimeError):
    """A deterministic oracle disagreed; this run has no passing evidence."""


def _require(condition: bool, code: str) -> None:
    if not condition:
        raise EvidenceMismatch(code)


def _rows(names: tuple[str, ...]) -> tuple[dict[str, bool], ...]:
    return tuple(dict(zip(names, bits, strict=True))
                 for bits in product((False, True), repeat=len(names)))


def _merge(environment: dict[str, bool],
           rows: tuple[dict[str, bool], ...]) -> dict[str, bool]:
    return environment | {name: value for row in rows for name, value in row.items()}


def _planning_legal(v: dict[str, bool]) -> bool:
    return (not (v["breaking"] and v["additive"])
            and not (v["upgrade"] and v["shim"])
            and (not v["breaking"] or (v["allow_breaking"] and v["upgrade"]
                                       and v["migration"] and not v["shim"]))
            and (not (v["additive"] or v["shim"] or v["upgrade"]) or v["regression"]))


def _asymmetric_legal(v: dict[str, bool]) -> bool:
    return not (v["a"] and (v["b"] or v["c"])) and not (v["b"] and v["c"])


def _triangle_legal(v: dict[str, bool]) -> bool:
    left = int(v["left_low"]) + 2 * int(v["left_high"])
    right = int(v["right_low"]) + 2 * int(v["right_high"])
    return (left, right) in {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)}


@dataclass(frozen=True)
class Case:
    name: str
    problem: SwarmProblem
    order: tuple[str, ...]
    legal: Callable[[dict[str, bool]], bool]
    expected_counts: tuple[int, ...]
    expected_global: tuple[int, ...]
    expected_maximum: tuple[int, ...]


def _cases() -> tuple[Case, ...]:
    # Environment rows are ordered False then True, as produced by _rows.
    plan = ("schema", "client", "verification")
    return (
        Case("planning_schema_first", example("planning"), plan, _planning_legal,
             (12, 3), (14, 15), (12, 12)),
        Case("planning_verification_first", example("planning"), plan[::-1],
             _planning_legal, (12, 12), (14, 15), (12, 12)),
        Case("asymmetric_A_first", example("asymmetric"), ("A", "B"),
             _asymmetric_legal, (2,), (4,), (3,)),
        Case("asymmetric_B_first", example("asymmetric"), ("B", "A"),
             _asymmetric_legal, (3,), (4,), (3,)),
        Case("triangle_left_first", example("triangle"), ("left", "right"),
             _triangle_legal, (3,), (6,), (4,)),
        Case("triangle_right_first", example("triangle"), ("right", "left"),
             _triangle_legal, (3,), (6,), (4,)),
        Case("triangle_balanced_anchor", example("triangle", True), ("left", "right"),
             _triangle_legal, (4,), (6,), (4,)),
    )


def _maximum_product(case: Case, environment: dict[str, bool]) -> int:
    """Exhaust all nonempty factor subsets in these tiny, fixed oracle cases."""
    universes = tuple(_rows(block.controls) for block in case.problem.blocks)
    _require(len(universes) <= 3 and all(len(rows) <= 4 for rows in universes),
             "oracle_subset_bound")
    legal = {
        keys: case.legal(_merge(environment,
                                tuple(universes[i][k] for i, k in enumerate(keys))))
        for keys in product(*(range(len(rows)) for rows in universes))
    }
    subsets = tuple(tuple(tuple(i for i in range(len(rows)) if mask & (1 << i))
                          for mask in range(1, 1 << len(rows))) for rows in universes)
    best = 0
    for rectangle in product(*subsets):
        count = prod(len(part) for part in rectangle)
        if count > best and all(legal[keys] for keys in product(*rectangle)):
            best = count
    return best


def _domains(case: Case, envelope: AutonomyEnvelope,
             environment: dict[str, bool]) -> tuple[tuple[dict[str, bool], ...], ...]:
    return tuple(tuple(row for row in _rows(block.controls)
                       if envelope.permits(block.name, environment | row))
                 for block in case.problem.blocks)


def _check_witnesses(case: Case, envelope: AutonomyEnvelope,
                     inspection: dict[str, object]) -> int:
    environment = cast(dict[str, bool], inspection["environment"])
    count = 0
    for agent in cast(list[dict[str, Any]], inspection["agents"]):
        block = case.problem.block(agent["agent"])
        expected = {tuple(row[name] for name in block.controls)
                    for row in _rows(block.controls)
                    if not envelope.permits(block.name, environment | row)}
        seen = set()
        for excluded in agent["excluded_choices"]:
            row = excluded["conflicting_joint_choice"]
            own = excluded["choice"]
            case.problem.contract.validate_values(row)
            _require(all(row[name] == bit for name, bit in environment.items()),
                     "witness_environment")
            _require(own == {name: row[name] for name in block.controls},
                     "witness_own_choice")
            _require(not case.legal(row), "witness_must_violate_independent_relation")
            for other in case.problem.blocks:
                if other != block:
                    values = {name: row[name] for name in
                              case.problem.contract.environment + other.controls}
                    _require(envelope.permits(other.name, values), "witness_other_domain")
            violations = [r.name for r in case.problem.contract.requirements
                          if r.residual.evaluate(row)]
            _require(excluded["violated_requirements"] == violations,
                     "witness_requirement_names")
            key = tuple(own[name] for name in block.controls)
            _require(key not in seen, "duplicate_exclusion_witness")
            seen.add(key)
            count += 1
        _require(seen == expected, "exclusion_witness_coverage")
    return count


def _check_slice(case: Case, envelope: AutonomyEnvelope, environment: dict[str, bool],
                 expected: int, expected_global: int,
                 expected_maximum: int) -> dict[str, object]:
    blocks = case.problem.blocks
    global_rows = _rows(case.problem.contract.controls)
    for row in global_rows:
        values = environment | row
        _require(case.problem.contract.satisfied(values) == case.legal(values),
                 "original_relation_oracle")
    domains = _domains(case, envelope, environment)
    _require(all(domains), "empty_agent_domain")
    subject = envelope.subject_id
    for choices in product(*domains):
        values = _merge(environment, choices)
        _require(case.legal(values), "independent_product_unsafe")
        issued = tuple(envelope.choose(block.name, environment | row)
                       for block, row in zip(blocks, choices, strict=True))
        _require(all(choice.envelope_id == subject for choice in issued),
                 "choice_subject_binding")
        _require(all(dict(choice.environment) == environment for choice in issued),
                 "choice_environment_binding")
        _require(envelope.combine_choices(issued) == values, "combined_choices_changed")
    for index, block in enumerate(blocks):
        others = tuple(rows for j, rows in enumerate(domains) if j != index)
        for own in _rows(block.controls):
            compatible = all(case.legal(_merge(environment | own, choices))
                             for choices in product(*others))
            _require(envelope.permits(block.name, environment | own) == compatible,
                     "final_cofactor_oracle")
    inspection = inspect_envelope(envelope, environment)
    count = prod(len(rows) for rows in domains)
    _require(count == expected == inspection["independent_combinations"],
             "expected_independent_count")
    feasible = sum(case.legal(environment | row) for row in global_rows)
    _require(feasible == expected_global == inspection[
        "all_globally_feasible_combinations"], "feasible_count_oracle")
    maximum = _maximum_product(case, environment)
    _require(maximum == expected_maximum, "expected_maximum_product")
    _require(envelope.subject_id == subject, "unstable_subject_id")
    return {"environment": environment, "independent_combinations": count,
            "globally_feasible": feasible,
            "maximum_product_in_this_finite_case": maximum,
            "boolean_oracle_rows": len(global_rows),
            "exclusion_witnesses_checked": _check_witnesses(case, envelope, inspection),
            "inspection": inspection}


def _expected_permit(case: Case, envelope: AutonomyEnvelope, block: AgentBlock,
                     row: dict[str, bool]) -> bool:
    environment = {name: row[name] for name in case.problem.contract.environment}
    own = {name: row[name] for name in block.controls}
    others = tuple(tuple(r for r in _rows(other.controls)
                         if envelope.permits(other.name, environment | r))
                   for other in case.problem.blocks if other != block)
    return all(case.legal(_merge(environment | own, choices))
               for choices in product(*others))


def _run_case(case: Case, runtime: TauRuntime,
              artifacts: dict[str, object]) -> dict[str, object]:
    before = len(runtime.records)
    started = time.perf_counter()
    envelope = AutonomyCompiler(runtime).compile(case.problem, case.order)
    compile_seconds = time.perf_counter() - started
    slices = [_check_slice(case, envelope, environment, count, feasible, maximum)
              for environment, count, feasible, maximum in zip(
                  _rows(case.problem.contract.environment), case.expected_counts,
                  case.expected_global, case.expected_maximum, strict=True)]
    artifacts[case.name + ".problem.json"] = encode_problem(case.problem)
    trace_rows = 0
    replay_seconds = 0.0
    for index, block in enumerate(case.problem.blocks):
        prefix = f"{case.name}.agent_{index:02d}"
        rows = _rows(case.problem.contract.environment + block.controls)
        clock = time.perf_counter()
        observed = replay_agent_gate(runtime, envelope, block.name, rows)
        replay_seconds += time.perf_counter() - clock
        _require(observed == tuple(_expected_permit(case, envelope, block, row)
                                   for row in rows), "native_trace_oracle")
        source = export_agent_gate(envelope, block.name)
        artifacts[prefix + ".tau"] = source
        artifacts[prefix + ".contract.json"] = encode_contract(
            envelope.local_contract(block.name))
        artifacts[prefix + ".trace.json"] = {
            "inputs": rows, "observed_permits": observed,
            "input_order": list(case.problem.contract.environment + block.controls),
            "source_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest()}
        trace_rows += len(rows)
    return {"name": case.name, "envelope_id": envelope.subject_id,
            "order": list(case.order), "compile_seconds": compile_seconds,
            "native_replay_seconds": replay_seconds,
            "compile_native_queries": envelope.native_queries,
            "query_interval": [before, len(runtime.records)],
            "native_trace_rows": trace_rows, "slices": slices}


def _source_hashes() -> dict[str, str]:
    paths = [p for folder in ("src/tau_composition", "src/tau_swarm")
             for p in (ROOT / folder).glob("*.py")]
    paths += list((ROOT / "tests").glob("test_tau_swarm*.py"))
    paths += [ROOT / name for name in (
        "tools/tau_swarm.py", "tools/benchmark_tau_swarm.py",
        "src/integration/tau_runner.py", "lean-mathlib/Proofs/TauSwarmAutonomy.lean")]
    result = {}
    for path in sorted(set(paths)):
        if not path.is_file():
            raise ValueError("source_file_missing")
        key = str(path.relative_to(ROOT))
        result[key] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def run(args: argparse.Namespace) -> dict[str, object]:
    if args.out.exists():
        raise ValueError("output_directory_exists")
    hashes = _source_hashes()
    runtime = TauRuntime(args.tau, timeout_seconds=args.timeout_seconds, max_queries=512)
    artifacts: dict[str, object] = {}
    started = time.perf_counter()
    try:
        cases = [_run_case(case, runtime, artifacts) for case in _cases()]
        _require(_source_hashes() == hashes, "source_changed_during_replay")
        runtime.check_subject()
    except EvidenceMismatch as exc:
        artifacts["native_queries.json"] = [asdict(r) for r in runtime.records]
        artifacts["report.json"] = {
            "schema": "tau-swarm/experiment-v1", "status": "FAIL",
            "error_code": str(exc), "authority": "NONE", "runtime_mounted": False,
            "binary_sha256": runtime.binary_sha256, "source_sha256": hashes}
        _write_artifacts(args.out, artifacts)
        raise
    report = {
        "schema": "tau-swarm/experiment-v1", "status": "PASS", "authority": "NONE",
        "runtime_mounted": False, "binary_sha256": runtime.binary_sha256,
        "python_version": sys.version.split()[0], "source_sha256": hashes,
        "cases": cases, "case_names": [case["name"] for case in cases],
        "wall_seconds": time.perf_counter() - started,
        "native_queries": len(runtime.records),
        "nonclaims": ["LLM productivity", "general speedup", "maximum-product compiler",
                      "new foundational theorem", "Python-to-Lean refinement proof",
                      "reproducible Tau build", "Tau Net integration",
                      "legal clearance"],
    }
    artifacts["native_queries.json"] = [asdict(record) for record in runtime.records]
    artifacts["report.json"] = report
    _write_artifacts(args.out, artifacts)
    return report


def main(argv: list[str] | None = None) -> int:
    try:
        command = JsonArgumentParser(description=__doc__)
        command.add_argument("--tau", type=Path, required=True)
        command.add_argument("--out", type=Path, required=True)
        command.add_argument("--timeout-seconds", type=float, default=10.0)
        report = run(command.parse_args(argv))
    except EvidenceMismatch as exc:
        print(json.dumps({"status": "FAIL", "error_code": str(exc), "authority": "NONE"}))
        return 1
    except (TauQueryError, ExpressionBudgetError) as exc:
        print(json.dumps({"status": "UNKNOWN", "error_code": str(exc),
                          "authority": "NONE"}))
        return 3
    except (ValueError, OSError, TypeError, RecursionError) as exc:
        print(json.dumps({"status": "invalid_input", "error_code": str(exc),
                          "authority": "NONE"}))
        return 2
    print(json.dumps({key: value for key, value in report.items()
                      if key not in {"source_sha256", "cases"}}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
