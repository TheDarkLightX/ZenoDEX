#!/usr/bin/env python3
"""Replay the composition frontier and compare native-certified compilation.

Run from the repository root:
python3 tools/benchmark_tau_composition.py --tau /path/to/tau --out /tmp/tau-study

Semantic checks are deterministic. Timings are local observations, never gates.
The output directory must be new. No network, installation or settlement effect.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import statistics
import sys
import time
from dataclasses import asdict
from pathlib import Path
from typing import TypedDict

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.tau_composition.anchor import AnchorCompiler, zero_anchor  # noqa: E402
from src.tau_composition.anchor_export import export_anchor_tau  # noqa: E402
from src.tau_composition.codec import encode_contract, export_tau  # noqa: E402
from src.tau_composition.compiler import RepairCompiler  # noqa: E402
from src.tau_composition.examples import (  # noqa: E402
    action_permissions,
    changed_chain,
    conditional_cycle,
    coupled_recovery,
    exclusion_pairs,
    permission_chain,
)
from src.tau_composition.models import Contract, Requirement, compose_maps  # noqa: E402
from src.tau_composition.replay import replay_controller  # noqa: E402
from src.tau_composition.resources import ExpressionBudgetError  # noqa: E402
from src.tau_composition.runtime import TauQueryError, TauRuntime  # noqa: E402
from src.tau_composition.terms import join, meet, negate, variable  # noqa: E402


class TimingSample(TypedDict):
    mode: str
    status: str
    error_code: str | None
    seconds: float
    native_queries: int
    native_output_bytes: int
    repair_tree_json_bytes: int | None


def _require(condition: bool, label: str) -> None:
    if not condition:
        raise RuntimeError(label)


def _rows(contract: Contract):
    names = contract.environment + contract.controls
    for values in itertools.product((False, True), repeat=len(names)):
        yield dict(zip(names, values, strict=True))


def _check_image(compiled, legal) -> int:
    contract = compiled.contract
    images: dict[tuple[bool, ...], set[tuple[bool, ...]]] = {}
    solutions: dict[tuple[bool, ...], set[tuple[bool, ...]]] = {}
    count = 0
    for row in _rows(contract):
        output = compiled.propose(row)
        _require(legal(output), "independent_soundness")
        if legal(row):
            _require(output == row, "independent_reproduction")
        _require(compiled.propose(output) == output, "independent_idempotence")
        environment = tuple(row[name] for name in contract.environment)
        images.setdefault(environment, set()).add(tuple(output[name] for name in contract.controls))
        solutions.setdefault(environment, set())
        if legal(row):
            solutions[environment].add(tuple(row[name] for name in contract.controls))
        count += 1
    _require(images == solutions, "independent_image_equality")
    return count


def _action_legal(row: dict[str, bool]) -> bool:
    flags = ("oracle_fresh", "maintenance_breach", "breaker_clear", "proof_valid",
             "binding_valid", "authorized", "position_open", "epoch_valid")
    return (
        (not row["liquidate"] or all(row[key] for key in flags))
        and (not row["recover"] or row["authorized"])
        and sum(row[key] for key in ("liquidate", "recover", "cancel")) <= 1
    )


def _triangular_contract(coordinate_count: int) -> Contract:
    """Create ``C_i = (x[i-2] | x[i-1]) & ~x[i]`` over explicit coordinates."""

    if type(coordinate_count) is not int or not 3 <= coordinate_count <= 256:
        raise ValueError("triangle_coordinate_count")
    clause_count = coordinate_count - 2
    names = tuple(f"x{index:03d}" for index in range(coordinate_count))
    terms = tuple(variable(name) for name in names)
    requirements = tuple(
        Requirement(
            f"triangle{index + 2:03d}",
            meet(join(terms[index], terms[index + 1]), negate(terms[index + 2])),
        )
        for index in range(clause_count)
    )
    return Contract(f"triangular_coordinates_{coordinate_count}", (), names, requirements)


def _triangular_legal(row: dict[str, bool], coordinate_count: int) -> bool:
    return all(
        not ((row[f"x{index:03d}"] or row[f"x{index + 1:03d}"])
             and not row[f"x{index + 2:03d}"])
        for index in range(coordinate_count - 2)
    )


def _triangular_trace_rows(contract: Contract) -> tuple[dict[str, bool], ...]:
    """Two legal and two deliberately invalid rows for the small anchor replay."""

    coordinate_count = len(contract.controls)
    all_zero = {name: False for name in contract.controls}
    all_one = {name: True for name in contract.controls}
    early_violation = dict(all_zero)
    early_violation[contract.controls[0]] = True
    late_violation = dict(all_zero)
    late_violation[contract.controls[2]] = True
    rows = (all_zero, all_one, early_violation, late_violation)
    for index, row in enumerate(rows):
        expected = index < 2
        _require(_triangular_legal(row, coordinate_count) is expected, "anchor_trace_vector")
    return rows


def _one_edit_triangle(contract: Contract) -> Contract:
    """Change one clause while retaining the all-zero anchor's validity."""

    original = contract.requirements[-1]
    replacement = Requirement(
        original.name,
        join(original.residual, meet(variable(contract.controls[0]), variable(contract.controls[-1]))),
    )
    return Contract(
        f"{contract.name}_one_edit",
        contract.environment,
        contract.controls,
        contract.requirements[:-1] + (replacement,),
    )


def semantic_replay(binary: Path, directory: Path) -> dict[str, object]:
    runtime = TauRuntime(binary, timeout_seconds=10, max_queries=256)
    compiler = RepairCompiler(runtime)
    recovery = coupled_recovery()
    maps = tuple(compiler.native_repair(Contract(
        "local", recovery.environment, recovery.controls, (item,),
    )) for item in recovery.requirements)
    naive = compose_maps(maps, recovery.controls)
    witness = {"paused": True, "debit": False, "credit": True}
    failed = naive.apply(witness)
    _require(failed["debit"] and failed["credit"], "negative_order_witness_changed")
    analysis = compiler.analyze_order(recovery, naive)
    _require(not analysis.covers_feasible_environment, "guard_confused_with_feasibility")

    recovered = compiler.compile(recovery)
    factor = compiler.compile_guarded_cover(conditional_cycle(), ((0, 1), (1, 0)))
    actions = compiler.compile(action_permissions())
    chain = compiler.compile(permission_chain(4))
    counts = {
        "recovery": _check_image(recovered, lambda v: not (v["paused"] and v["debit"]) and v["debit"] == v["credit"]),
        "factor": _check_image(factor, lambda v: not v["left"] and v["right"]),
        "actions": _check_image(actions, _action_legal),
        "chain": _check_image(chain, lambda v: all(not v[f"action{i:03d}"] or v[f"action{i + 1:03d}"] for i in range(4))),
    }
    traces = {}
    for compiled in (recovered, factor, actions, chain):
        rows = tuple(_rows(compiled.contract))
        selected = rows if len(rows) <= 32 else tuple(rows[i] for i in (0, 1, 7, 8, 1023, 2040, 2047))
        outputs = replay_controller(runtime, compiled, selected)
        traces[compiled.contract.name] = {"inputs": selected, "outputs": outputs}
        (directory / f"{compiled.contract.name}.tau").write_text(export_tau(compiled), encoding="utf-8")
        (directory / f"{compiled.contract.name}.contract.json").write_text(
            json.dumps(encode_contract(compiled.contract), indent=2, sort_keys=True) + "\n", encoding="utf-8",
        )
    _require(not runtime.valid("all p:sbf ((p=0:sbf) || (p=1:sbf))"), "ba_domain_trap")
    _require(runtime.valid("all p:sbf ((p | p')=1:sbf)"), "ba_complement_identity")
    (directory / "native_queries.json").write_text(json.dumps([asdict(q) for q in runtime.records], indent=2) + "\n")
    (directory / "native_traces.json").write_text(json.dumps(traces, indent=2, sort_keys=True) + "\n")
    return {
        "status": "PASS", "oracle_rows": counts, "total_oracle_rows": sum(counts.values()),
        "native_query_count": len(runtime.records),
        "native_trace_rows": sum(len(trace["inputs"]) for trace in traces.values()),
        "binary_sha256": runtime.binary_sha256,
        "naive_order_counterexample": {"input": witness, "output": failed},
        "safe_guard": analysis.safe_environment.canonical_data(),
        "feasible_guard": analysis.feasible_environment.canonical_data(),
        "guard_cover_orders": factor.alternative_orders,
        "factor_required_merged_synthesis": False,
    }


def _source_size_measurement(
    binary: Path, directory: Path, contract: Contract, representation: str
) -> dict[str, object]:
    """Generate one native-backed controller or record an explicit UNKNOWN."""

    runtime = TauRuntime(binary, timeout_seconds=10, max_queries=256)
    stem = f"{contract.name}_{representation}"
    source_path = directory / f"{stem}.tau"
    query_path = directory / f"{stem}_native_queries.json"
    try:
        if representation == "native_composed":
            composed = RepairCompiler(runtime).compile(contract)
            source = export_tau(composed)
            compile_queries, cache_hits = composed.native_queries, composed.cache_hits
        elif representation == "common_zero_anchor":
            anchored = AnchorCompiler(runtime).compile(contract, zero_anchor(contract))
            source = export_anchor_tau(anchored)
            compile_queries, cache_hits = anchored.native_queries, anchored.cache_hits
        else:
            raise ValueError("unknown_source_representation")
    except ExpressionBudgetError as exc:
        result: dict[str, object] = {
            "status": "UNKNOWN",
            "error_code": str(exc),
            "unknown_reason": "expression_budget",
            "source_bytes": None,
            "source_sha256": None,
            "source_file": None,
            "compile_native_queries": len(runtime.records),
            "cache_hits": None,
        }
    except TauQueryError as exc:
        result = {
            "status": "UNKNOWN",
            "error_code": str(exc),
            "unknown_reason": "native_unavailable_or_unsupported",
            "source_bytes": None,
            "source_sha256": None,
            "source_file": None,
            "compile_native_queries": len(runtime.records),
            "cache_hits": None,
        }
    else:
        encoded = source.encode("utf-8")
        source_path.write_text(source, encoding="utf-8")
        result = {
            "status": "PASS",
            "error_code": None,
            "source_bytes": len(encoded),
            "source_sha256": hashlib.sha256(encoded).hexdigest(),
            "source_file": source_path.name,
            "compile_native_queries": compile_queries,
            "cache_hits": cache_hits,
        }
    query_path.write_text(
        json.dumps([asdict(query) for query in runtime.records], indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    result["native_query_count"] = len(runtime.records)
    result["native_query_log"] = query_path.name
    return result


def _source_size_comparisons(binary: Path, directory: Path) -> list[dict[str, object]]:
    """Compare source footprints only; this does not make timing claims."""

    comparisons: list[dict[str, object]] = []
    for coordinate_count in (12, 16):
        contract = _triangular_contract(coordinate_count)
        composed = _source_size_measurement(binary, directory, contract, "native_composed")
        anchor = _source_size_measurement(binary, directory, contract, "common_zero_anchor")
        both_complete = composed["status"] == "PASS" and anchor["status"] == "PASS"
        source_ratio = None
        composed_bytes = composed["source_bytes"]
        anchor_bytes = anchor["source_bytes"]
        if both_complete and isinstance(composed_bytes, int) and isinstance(anchor_bytes, int):
            source_ratio = composed_bytes / anchor_bytes
        comparisons.append({
            "coordinate_count": coordinate_count,
            "clause_count": len(contract.requirements),
            "native_composed": composed,
            "common_zero_anchor": anchor,
            "source_size_ratio_when_both_complete": source_ratio,
            "speed_ratio": None,
            "speed_ratio_reason": "source_size_only" if both_complete else "native_composed_unknown",
        })
    return comparisons


def _repair_economy_example(runtime: TauRuntime, directory: Path) -> dict[str, object]:
    """Keep a witness where a valid shared anchor differs from native LGRS output."""

    contract = Contract("repair_economy", (), ("x", "y", "z"), (
        Requirement("x_must_be_zero", variable("x")),
    ))
    proposal = {"x": True, "y": True, "z": True}
    before = dict(proposal)
    anchored = AnchorCompiler(runtime).compile(contract, zero_anchor(contract))
    anchor_output = anchored.propose(proposal)
    native_start = len(runtime.records)
    native_output = RepairCompiler(runtime).native_repair(contract).apply(proposal)
    _require(proposal == before, "repair_economy_input_mutated")
    _require(anchor_output == {"x": False, "y": False, "z": False}, "anchor_economy_witness")
    _require(native_output == {"x": False, "y": True, "z": True}, "native_economy_witness")
    _require(anchor_output != native_output, "repair_economy_outputs_confused")
    source = export_anchor_tau(anchored)
    source_path = directory / "repair_economy_anchor.tau"
    source_path.write_text(source, encoding="utf-8")
    return {
        "proposal": proposal,
        "anchor_output": anchor_output,
        "native_output": native_output,
        "outputs_equal_on_witness": False,
        "anchor_native_queries": anchored.native_queries,
        "native_repair_queries": len(runtime.records) - native_start,
        "anchor_source_file": source_path.name,
        "anchor_source_bytes": len(source.encode("utf-8")),
        "anchor_source_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
    }


def shared_anchor_experiment(binary: Path, directory: Path) -> dict[str, object]:
    """Run bounded common-zero-anchor evidence without changing timing measurements."""

    contract = _triangular_contract(6)
    runtime = TauRuntime(binary, timeout_seconds=10, max_queries=256)
    compiler = AnchorCompiler(runtime)
    initial = compiler.compile(contract, zero_anchor(contract))
    warm = compiler.compile(contract, zero_anchor(contract))
    one_edit_contract = _one_edit_triangle(contract)
    one_edit = compiler.compile(one_edit_contract, zero_anchor(one_edit_contract))
    oracle_rows = _check_image(initial, lambda row: _triangular_legal(row, 6))
    trace_inputs = _triangular_trace_rows(contract)
    trace_outputs = replay_controller(runtime, initial, trace_inputs)
    for original, output in zip(trace_inputs, trace_outputs, strict=True):
        candidate = dict(original)
        candidate.update(output)
        _require(_triangular_legal(candidate, 6), "anchor_native_trace_soundness")
        if _triangular_legal(original, 6):
            _require(candidate == original, "anchor_native_trace_reproduction")
    source = export_anchor_tau(initial)
    source_path = directory / "shared_anchor_triangular_coordinates_6.tau"
    source_path.write_text(source, encoding="utf-8")
    traces = {
        "labels": ("valid_zero", "valid_one", "invalid_early", "invalid_late"),
        "inputs": trace_inputs,
        "outputs": trace_outputs,
    }
    trace_path = directory / "shared_anchor_native_traces.json"
    trace_path.write_text(json.dumps(traces, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    economy = _repair_economy_example(runtime, directory)
    query_path = directory / "shared_anchor_native_queries.json"
    query_path.write_text(
        json.dumps([asdict(query) for query in runtime.records], indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    encoded = source.encode("utf-8")
    return {
        "status": "PASS",
        "family": "triangular_common_zero_anchor",
        "definition": "C_i = (x[i-2] | x[i-1]) & ~x[i]",
        "coordinate_count": len(contract.controls),
        "clause_count": len(contract.requirements),
        "oracle_rows": oracle_rows,
        "native_trace_rows": len(trace_inputs),
        "trace_file": trace_path.name,
        "native_query_count": len(runtime.records),
        "native_query_log": query_path.name,
        "anchor_source_file": source_path.name,
        "anchor_source_bytes": len(encoded),
        "anchor_source_sha256": hashlib.sha256(encoded).hexdigest(),
        "anchor_native_queries": {
            "initial": initial.native_queries,
            "warm": warm.native_queries,
            "one_edit": one_edit.native_queries,
        },
        "anchor_cache_hits": {
            "initial": initial.cache_hits,
            "warm": warm.cache_hits,
            "one_edit": one_edit.cache_hits,
        },
        "repair_economy": economy,
        "source_size_comparisons": _source_size_comparisons(binary, directory),
        "limitations": [
            "The triangular truth oracle covers six coordinates, four clauses and exact host Boolean inputs.",
            "Source-size comparisons deliberately report no speed ratio.",
            "A resource-bound or native failure is UNKNOWN, not evidence about solver capability.",
            "The repair-economy witness shows different outputs on one proposal; it does not rank maps globally.",
        ],
    }


def _timed(binary: Path, contract: Contract, mode: str) -> TimingSample:
    runtime = TauRuntime(binary, timeout_seconds=5)
    compiler = RepairCompiler(runtime)
    started = time.perf_counter()
    try:
        if mode == "composed":
            repair = compiler.compile(contract).repair
        else:
            repair = compiler.native_repair(contract)
        status = "PASS"
        encoded_bytes = sum(len(term.canonical_json().encode()) for _, term in repair.assignments)
        error = None
    except (TauQueryError, ExpressionBudgetError) as exc:
        status, encoded_bytes, error = "UNKNOWN", None, str(exc)
    return {
        "mode": mode, "status": status, "error_code": error,
        "seconds": time.perf_counter() - started, "native_queries": len(runtime.records),
        "native_output_bytes": sum(len(q.stdout.encode()) for q in runtime.records),
        "repair_tree_json_bytes": encoded_bytes,
    }


def benchmarks(binary: Path, repeats: int) -> dict[str, object]:
    comparisons = []
    for factory, sizes in ((permission_chain, (2, 4, 8)), (exclusion_pairs, (2, 4))):
        for size in sizes:
            samples = {mode: [_timed(binary, factory(size), mode) for _ in range(repeats)]
                       for mode in ("composed", "monolithic")}
            complete = all(row["status"] == "PASS" for rows in samples.values() for row in rows)
            medians = {mode: statistics.median(row["seconds"] for row in rows) for mode, rows in samples.items()}
            comparisons.append({
                "family": factory.__name__, "requirements": size, "samples": samples,
                "median_seconds": medians,
                "speedup_when_both_complete": medians["monolithic"] / medians["composed"] if complete else None,
            })
    runtime = TauRuntime(binary, timeout_seconds=5)
    compiler = RepairCompiler(runtime)
    original = permission_chain(8)
    cold = compiler.compile(original)
    warm = compiler.compile(original)
    edited = compiler.compile(changed_chain(original))
    large = _timed(binary, permission_chain(64), "composed")
    boundary = [_timed(binary, permission_chain(12), "monolithic"),
                _timed(binary, exclusion_pairs(8), "monolithic")]
    return {
        "comparisons": comparisons,
        "incremental_native_queries": {"cold": cold.native_queries, "unchanged": warm.native_queries, "one_edit": edited.native_queries},
        "large_chain": {"requirements": 64, "input_bits": 65, "input_words": 2 ** 65, "result": large},
        "monolithic_profile_boundaries": boundary,
        "limitations": [
            "Local wall time includes native parsing/checking and process costs; initial runtime hashing is excluded equally.",
            "Native term-profile rejection is distinct from solver timeout and proves no native solver incapability.",
            "Only completed paired runs produce a ratio; selected maps may differ while both preserve the whole solution set.",
            "Families are synthetic algebra workloads; no production throughput or general asymptotic speedup is established.",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tau", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    if not 1 <= args.repeats <= 5:
        parser.error("repeats must be in [1,5]")
    args.out.mkdir(parents=True, exist_ok=False)
    semantics = semantic_replay(args.tau, args.out)
    shared_anchor = shared_anchor_experiment(args.tau, args.out)
    measurements = benchmarks(args.tau, args.repeats)
    report = {
        "schema": "tau-composition/experiment-v1", "authority": "NONE", "production_claim": False,
        "semantics": semantics,
        "shared_anchor": shared_anchor,
        "measurements": measurements,
    }
    source_paths = [
        *ROOT.glob("src/tau_composition/*.py"),
        *ROOT.glob("tests/test_tau_composition*.py"),
        ROOT / "tests/test_tau_common_anchor.py",
        ROOT / "tests/test_tau_anchor_export.py",
        ROOT / "tools/tau_composition.py",
        Path(__file__),
        ROOT / "docs/research/tau_composition_20260907.md",
        ROOT / "lean-mathlib/Proofs/TauReproductiveComposition.lean",
        ROOT / "lean-mathlib/Proofs/TauCommonAnchor.lean",
        ROOT / "lean-mathlib/Proofs/TauPolynomialRepair.lean",
    ]
    sources = sorted(dict.fromkeys(source_paths))
    report["source_sha256"] = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in sources}
    (args.out / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"semantic_status": semantics["status"], "report": str(args.out / "report.json")}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
