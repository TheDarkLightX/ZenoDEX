#!/usr/bin/env python3
"""Replay the finite message workbench, code revisions, and paired Tau representations.

Writes a fresh evidence directory. Executes only exact source bytes admitted by
the bounded workbench profile in a separate CPython process. No network, Tau Net
submission, repository mutation, or execution authority is provided.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from dataclasses import asdict, dataclass, replace
from itertools import product
from math import prod
from pathlib import Path
from statistics import median
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.tau_composition.codec import _unique_object  # noqa: E402
from src.tau_composition.models import Requirement  # noqa: E402
from src.tau_composition.resources import ExpressionBudgetError  # noqa: E402
from src.tau_composition.runtime import TauQueryError, TauRuntime  # noqa: E402
from src.tau_swarm.codec import encode_problem  # noqa: E402
from src.tau_swarm.compiler import AutonomyCompiler  # noqa: E402
from src.tau_swarm.exports import export_agent_gate, replay_agent_gate  # noqa: E402
from src.tau_swarm.models import AutonomyEnvelope, SwarmProblem  # noqa: E402
from src.tau_workbench.catalog import Catalog, build_catalog, outputs_of  # noqa: E402
from src.tau_workbench.codec import encode_task  # noqa: E402
from src.tau_workbench.compiler import CompiledWorkbench, compile_task, problem_for  # noqa: E402
from src.tau_workbench.examples import message_task  # noqa: E402
from src.tau_workbench.models import Stage, Task  # noqa: E402
from src.tau_workbench.native import replay_bundles  # noqa: E402
from src.tau_workbench.programs import Program, analyze  # noqa: E402
from src.tau_workbench.relation import residuals  # noqa: E402
from tools.benchmark_tau_swarm import _source_hashes as _swarm_hashes  # noqa: E402


class EvidenceMismatch(RuntimeError):
    """Deterministic disagreement; no passing result may be published."""


def _require(condition: bool, code: str) -> None:
    if not condition:
        raise EvidenceMismatch(code)


@dataclass(frozen=True)
class Proposal:
    stage: str
    program: Program
    intent: str
    negative_control: bool


def _proposals(text: str) -> tuple[Proposal, ...]:
    if len(text.encode()) > 128_000:
        raise ValueError("proposal_byte_bound")
    data = json.loads(text, object_pairs_hook=_unique_object)
    if type(data) is not dict or set(data) != {"candidates"}:
        raise ValueError("proposal_shape")
    rows = data["candidates"]
    if type(rows) is not list or not 1 <= len(rows) <= 16:
        raise ValueError("proposal_count")
    result = []
    names = set()
    for row in rows:
        if type(row) is not dict or set(row) != {"stage", "name", "source", "intent", "negative_control"}:
            raise ValueError("proposal_shape")
        if (type(row["stage"]) is not str or row["stage"] not in {"encoder", "adapter", "decoder"}
                or type(row["source"]) is not str or type(row["intent"]) is not str
                or type(row["negative_control"]) is not bool):
            raise ValueError("proposal_value")
        program = Program(row["name"], row["source"].encode())
        if program.name in names:
            raise ValueError("duplicate_proposal")
        names.add(program.name)
        result.append(Proposal(row["stage"], program, row["intent"], row["negative_control"]))
    return tuple(result)


def _source_hashes() -> dict[str, str]:
    hashes = _swarm_hashes()
    names = ("__init__", "models", "programs", "catalog", "compiler", "codec", "native", "examples", "relation")
    paths = [*(f"src/tau_workbench/{name}.py" for name in names),
             "tools/tau_workbench.py", "tools/benchmark_tau_workbench.py",
             "lean-mathlib/Proofs/TauArtifactQuotient.lean",
             "docs/research/tau_workbench_plan_20260908.md",
             "tests/test_tau_workbench.py", "tests/test_tau_workbench_programs.py",
             "tests/test_tau_workbench_relation.py", "tests/test_tau_workbench_codec.py",
             "tests/test_tau_workbench_cli.py", "tests/test_tau_workbench_benchmark.py"]
    for name in paths:
        path = ROOT / name
        if not path.is_file():
            raise ValueError("source_file_missing")
        hashes[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    return hashes


def _central_baselines(task: Task) -> tuple[dict[str, Any], tuple[bool, ...]]:
    start = time.perf_counter()
    tables = tuple(tuple(analyze(p, task.bits).outputs for p in s.programs) for s in task.stages)
    analysis_seconds = time.perf_counter() - start
    start = time.perf_counter()
    raw = tuple(outputs_of(rows, task.inputs) == task.expected for rows in product(*tables))
    cached_seconds = time.perf_counter() - start
    start = time.perf_counter()
    classes = tuple(tuple(dict.fromkeys(rows)) for rows in tables)
    quotient = tuple(outputs_of(rows, task.inputs) == task.expected for rows in product(*classes))
    quotient_seconds = time.perf_counter() - start
    return {"source_input_evaluations": sum(len(s.programs) for s in task.stages) * (1 << task.bits),
            "source_analysis_seconds": analysis_seconds,
            "cached_artifact_checks": len(raw), "cached_artifact_seconds": cached_seconds,
            "accepted_artifact_bundles": sum(raw), "quotient_class_checks": len(quotient),
            "quotient_seconds_including_grouping": quotient_seconds,
            "accepted_behavior_bundles": sum(quotient),
            "same_class_replacement_global_checks": 0,
            "same_class_replacement_reuse_also_available_without_tau": True}, raw


def _maximum_product(catalog: Catalog) -> tuple[tuple[int, ...], ...]:
    _require(len(catalog.stages) == 3 and all(len(s) == 4 for s in catalog.stages), "pilot_oracle_bound")
    subsets = tuple(tuple(i for i in range(4) if mask & (1 << i)) for mask in range(1, 16))
    best: tuple[tuple[int, ...], ...] = ()
    volume = 0
    for domains in product(subsets, repeat=3):
        if prod(map(len, domains)) > volume and all(row in catalog.legal for row in product(*domains)):
            best = domains
            volume = prod(map(len, domains))
    _require(bool(best), "pilot_oracle_empty")
    return best


def _domain_codes(envelope: AutonomyEnvelope) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(code for code in range(1 << len(block.controls))
                       if envelope.permits(block.name, {name: bool(code & (1 << i))
                                                        for i, name in enumerate(block.controls)}))
                 for block in envelope.problem.blocks)


def _representations(task: Task) -> tuple[SwarmProblem, SwarmProblem]:
    selected = problem_for(task)
    controls = selected.contract.controls
    allowed = frozenset(row for row in product((False, True), repeat=len(controls))
                        if selected.contract.satisfied(dict(zip(controls, row, strict=True))))
    enumerated, compact = residuals(controls, allowed)
    _require(compact == selected.contract.residual, "residual_regeneration")
    reference = replace(selected, contract=replace(selected.contract, requirements=(
        Requirement("exact_pipeline_behavior", enumerated),)))
    return reference, selected


def _paired_compiles(task: Task, runtime: TauRuntime, pairs: int,
                     artifacts: dict[str, Any]) -> dict[str, Any]:
    problems = dict(zip(("enumerated", "factored"), _representations(task), strict=True))
    for name, problem in problems.items():
        artifacts[name + ".problem.json"] = encode_problem(problem)
    rows: list[dict[str, Any]] = []
    domains = None
    for pair in range(pairs):
        for name in (("enumerated", "factored") if pair % 2 == 0 else ("factored", "enumerated")):
            before = len(runtime.records)
            start = time.perf_counter()
            envelope = AutonomyCompiler(runtime).compile(problems[name])
            seconds = time.perf_counter() - start
            observed = _domain_codes(envelope)
            if domains is None:
                domains = observed
            _require(observed == domains, "representation_domain_disagreement")
            rows.append({"pair": pair, "representation": name, "seconds": seconds,
                         "native_queries": len(runtime.records) - before, "domains": observed})
    medians = {name: median(row["seconds"] for row in rows if row["representation"] == name)
               for name in problems}
    return {"residual_bytes": {name: len(p.contract.residual.to_tau().encode()) for name, p in problems.items()},
            "boolean_rows_checked": 1 << len(problems["factored"].contract.controls),
            "pairs": pairs, "runs": rows, "median_seconds": medians,
            "observed_median_ratio": medians["enumerated"] / medians["factored"],
            "timing_scope": "native compiler only; source analysis and relation construction excluded"}


def _case(task: Task, order: tuple[str, ...], runtime: TauRuntime, label: str,
          artifacts: dict[str, Any]) -> tuple[CompiledWorkbench, dict[str, Any]]:
    before = len(runtime.records)
    start = time.perf_counter()
    compiled = compile_task(task, runtime, order)
    seconds = time.perf_counter() - start
    indices = tuple(tuple(i for i, p in enumerate(stage.programs) if p in compiled.members(j))
                    for j, stage in enumerate(task.stages))
    bundles = tuple(product(*indices))
    replay = replay_bundles(task, bundles)
    _require(all(failure is None for failure in replay.outcomes), "admitted_native_bundle_failed")
    artifacts[label + ".task.json"] = encode_task(task)
    artifacts[label + ".cpython.json"] = {"bundles": bundles, "replay": asdict(replay)}
    trace_rows = 0
    for i, block in enumerate(compiled.envelope.problem.blocks):
        rows = tuple(dict(zip(block.controls, row, strict=True))
                     for row in product((False, True), repeat=len(block.controls)))
        observed = replay_agent_gate(runtime, compiled.envelope, block.name, rows)
        _require(sum(observed) == len(compiled.domains[i]), "native_local_gate_disagreement")
        artifacts[f"{label}.stage_{i}.tau"] = export_agent_gate(compiled.envelope, block.name)
        trace_rows += len(rows)
    return compiled, {"task_id": task.subject_id, "anchor": task.anchor, "order": order,
                      "domains": compiled.domains, "admitted_artifacts_per_stage": tuple(map(len, indices)),
                      "independent_artifact_bundles": len(bundles),
                      "independent_behavior_bundles": prod(map(len, compiled.domains)),
                      "end_to_end_compile_seconds": seconds,
                      "native_records_including_gate_replay": len(runtime.records) - before,
                      "native_gate_rows": trace_rows, "cpython_pipeline_inputs_checked": replay.pipeline_inputs_checked}


def _proposal_events(compiled: CompiledWorkbench, proposals: tuple[Proposal, ...],
                     runtime: TauRuntime, artifacts: dict[str, Any]) -> list[dict[str, Any]]:
    task = compiled.catalog.task
    events = []
    accepted: list[list[Program]] = [[] for _ in task.stages]
    for index, proposal in enumerate(proposals):
        start = time.perf_counter()
        before = len(runtime.records)
        result = compiled.assess_replacement(proposal.stage, proposal.program)
        local_seconds = time.perf_counter() - start
        _require(len(runtime.records) == before, "replacement_issued_native_query")
        stage_index = tuple(s.name for s in task.stages).index(proposal.stage)
        stages = tuple(Stage(s.name, (proposal.program,) if i == stage_index else compiled.members(i))
                       for i, s in enumerate(task.stages))
        revision_task = replace(task, stages=stages, anchor=tuple(s.programs[0].name for s in stages))
        bundles = tuple(product(*(range(len(s.programs)) for s in stages)))
        native = replay_bundles(revision_task, bundles)
        local = result["status"] == "local_equivalent"
        if local:
            _require(all(f is None for f in native.outcomes), "local_replacement_context_failed")
            accepted[stage_index].append(proposal.program)
        failures = [(bundle, failure) for bundle, failure in zip(bundles, native.outcomes, strict=True)
                    if failure is not None]
        artifacts[f"proposal_{index:02d}.task.json"] = encode_task(revision_task)
        artifacts[f"proposal_{index:02d}.cpython.json"] = {"bundles": bundles, "replay": asdict(native)}
        events.append({**result, "name": proposal.program.name, "negative_control": proposal.negative_control,
                       "intent_is_unverified_author_metadata": proposal.intent,
                       "local_check_seconds": local_seconds, "full_domain_values_checked": 1 << task.bits,
                       "central_context_bundles_checked": len(bundles),
                       "central_context_bundles_passed": len(bundles) - len(failures),
                       "first_failure": None if not failures else {"bundle": failures[0][0], **asdict(failures[0][1])}})
    _require(all(accepted), "pilot_requires_an_admitted_revision_per_stage")
    revised_stages = tuple(Stage(s.name, tuple(ps)) for s, ps in zip(task.stages, accepted, strict=True))
    revised = replace(task, stages=revised_stages, anchor=tuple(s.programs[0].name for s in revised_stages))
    for programs in product(*(s.programs for s in revised.stages)):
        compiled.check_revision(programs)
    bundles = tuple(product(*(range(len(s.programs)) for s in revised.stages)))
    native = replay_bundles(revised, bundles)
    _require(all(f is None for f in native.outcomes), "assembled_revision_failed")
    artifacts["assembled_revision.task.json"] = encode_task(revised)
    artifacts["assembled_revision.cpython.json"] = {"bundles": bundles, "replay": asdict(native)}
    return events


def _run(runtime: TauRuntime, proposals: tuple[Proposal, ...], pairs: int,
         artifacts: dict[str, Any]) -> dict[str, Any]:
    task = message_task()
    catalog = build_catalog(task)
    baseline, raw = _central_baselines(task)
    bundles = tuple(product(*(range(len(s.programs)) for s in task.stages)))
    replay = replay_bundles(task, bundles)
    _require(tuple(f is None for f in replay.outcomes) == raw, "baseline_cpython_disagreement")
    artifacts["baseline.task.json"] = encode_task(task)
    artifacts["baseline.cpython.json"] = {"bundles": bundles, "replay": asdict(replay)}
    best = _maximum_product(catalog)
    best_anchor = tuple(classes[domain[0]].members[0].name for classes, domain in zip(catalog.stages, best, strict=True))
    cases = {}
    order = tuple(s.name for s in task.stages)
    compiled, cases["encoder_first"] = _case(task, order, runtime, "encoder_first", artifacts)
    _, cases["decoder_first"] = _case(task, order[::-1], runtime, "decoder_first", artifacts)
    _, cases["oracle_anchor"] = _case(replace(task, anchor=best_anchor), order, runtime, "oracle_anchor", artifacts)
    _require(cases["oracle_anchor"]["independent_behavior_bundles"] == prod(map(len, best)), "oracle_anchor_not_maximum")
    events = _proposal_events(compiled, proposals, runtime, artifacts)
    return {"task_id": task.subject_id, "baseline": baseline, "cases": cases, "proposal_events": events,
            "pilot_maximum_product": {"domains": best, "behavior_bundles": prod(map(len, best)),
                                      "oracle_subset_products": 15 ** 3},
            "representations": _paired_compiles(task, runtime, pairs, artifacts),
            "accepted_revision_bundles": len(artifacts["assembled_revision.cpython.json"]["bundles"]),
            "nonclaims": ["Finite original message-code pilot; no real ZenoDEX runtime change.",
                          "No general Python sandbox, program merge, or interpreter refinement proof.",
                          "No new Boolean decision procedure or established patent freedom to operate.",
                          "No human-time or general agent productivity measurement.",
                          "Explicit negative controls are not a natural model error-rate sample.",
                          "Equivalence caching also benefits the centralized quotient baseline.",
                          "Tau domains need not maximize volume; maximum is checked only in this pilot.",
                          "No Tau source-to-binary build correspondence, Tau Net submission or production authority."]}


def _write(output: Path, artifacts: dict[str, Any]) -> None:
    for name, value in artifacts.items():
        if type(value) is bytes:
            payload = value
        else:
            text = value if type(value) is str else json.dumps(value, indent=2, sort_keys=True) + "\n"
            payload = text.encode("utf-8")
        (output / name).write_bytes(payload)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tau", type=Path, required=True)
    parser.add_argument("--candidates", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--pairs", type=int, choices=(1, 2, 3), default=2)
    args = parser.parse_args(argv)
    if args.out.exists():
        print(json.dumps({"status": "invalid_input", "error_code": "output_directory_exists", "authority": "NONE"}))
        return 2
    artifacts: dict[str, Any] = {}
    report: dict[str, Any] = {"schema": "tau-workbench/replay-v1", "status": "FAIL", "authority": "NONE",
                              "runtime_mounted": False, "python_version": sys.version.split()[0]}
    runtime = None
    owns_output = False
    try:
        args.out.mkdir(parents=False, exist_ok=False)
        owns_output = True
        with args.candidates.open("rb") as stream:
            payload = stream.read(128_001)
        proposals = _proposals(payload.decode("utf-8"))
        artifacts["candidates.json"] = payload
        hashes = _source_hashes()
        report["source_sha256"] = hashes
        report["candidate_input_sha256"] = hashlib.sha256(payload).hexdigest()
        runtime = TauRuntime(args.tau, max_queries=512)
        report["binary_sha256"] = runtime.binary_sha256
        report.update(_run(runtime, proposals, args.pairs, artifacts))
        _require(_source_hashes() == hashes, "source_changed_during_replay")
        runtime.check_subject()
        report["status"] = "PASS"
    except (TauQueryError, ExpressionBudgetError) as exc:
        report.update(status="UNKNOWN", error_code=str(exc))
    except (OSError, ValueError, TypeError, RecursionError, EvidenceMismatch) as exc:
        report.update(status="FAIL", error_code=str(exc))
    if runtime is not None:
        artifacts["native_queries.json"] = [asdict(r) for r in runtime.records]
        report["native_records"] = len(runtime.records)
    artifacts["report.json"] = report
    if owns_output:
        _write(args.out, artifacts)
    print(json.dumps({k: v for k, v in report.items() if k not in {"source_sha256", "proposal_events"}}, indent=2))
    return 0 if report["status"] == "PASS" else 3


if __name__ == "__main__":
    raise SystemExit(main())
