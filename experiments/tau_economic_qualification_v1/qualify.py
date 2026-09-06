"""Replay pinned Tau economic predicates and measure one equivalent candidate.

Run with ``python3 -B -m experiments.tau_economic_qualification_v1.qualify
--tau-binary PATH --output REPORT``. A PASS records complete bounded traces;
it grants no ownership, publication, finality or production authority.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import asdict
from pathlib import Path

from experiments.tau_adt_rows_v1.execution import frozen_executable
from experiments.tau_adt_rows_v1.qualify import MEASURED_TAU_SHA256
from experiments.tau_economic_qualification_v1.conservation_equivalence import (
    check_conservation_equivalence,
)
from experiments.tau_economic_qualification_v1.reference import (
    SPEC_IDS,
    QualificationCase,
    corpus,
    evaluate,
    stateful_histories,
)
from experiments.tau_economic_qualification_v1.runner import (
    ENGINE_OPTIONS,
    NORMALIZER_SHA256,
    PreparedSpec,
    Variant,
    prepare,
    run_trace,
    sha256,
)
from tools.current_tau_replay_io_v1 import _read_bounded_regular_file_v1

ROOT = Path(__file__).resolve().parents[2]
SPEC_DIRECTORY = ROOT / "src/tau_specs/recommended"


def source_subject() -> dict[str, str]:
    paths = {SPEC_DIRECTORY / f"{name}.tau" for name in SPEC_IDS}
    for module in tuple(sys.modules.values()):
        filename = getattr(module, "__file__", None)
        if type(filename) is str:
            path = Path(filename).resolve()
            if path.is_relative_to(ROOT) and path.suffix == ".py":
                paths.add(path)
    return {str(path.relative_to(ROOT)): sha256(_read_bounded_regular_file_v1(path, 2 * 1024 * 1024, "source"))
            for path in sorted(paths)}


def _checked_run(fd: int, prepared: PreparedSpec, cases: tuple[QualificationCase, ...]) -> dict[str, object]:
    if not cases or any(case.spec_id != prepared.spec_id for case in cases):
        raise ValueError("mixed or empty qualification cases")
    for case in cases:
        if evaluate(case.spec_id, case.inputs) != case.expected_outputs:
            raise ValueError(f"independent reference disagrees with fixed vector: {case.name}")
    observation = run_trace(fd, prepared, tuple(case.inputs for case in cases))
    expected = tuple(case.expected_outputs for case in cases)
    if observation.outputs != expected:
        raise ValueError(f"Tau output disagreement: {prepared.spec_id}/{prepared.variant.value}/{cases[0].name}")
    return {
        "spec_id": prepared.spec_id, "variant": prepared.variant.value,
        "selected_source_sha256": prepared.selected_source_sha256,
        "expression_sha256": sha256(prepared.expression.encode("ascii")),
        "cases": [asdict(case) for case in cases], "observation": asdict(observation),
    }


def _qualify_corpus(fd: int, specs: dict[str, PreparedSpec], candidate: PreparedSpec) -> list[dict[str, object]]:
    observations = []
    vectors = corpus()
    for spec_id in SPEC_IDS:
        cases = tuple(case for case in vectors if case.spec_id == spec_id)
        if not cases:
            raise ValueError(f"missing qualification corpus: {spec_id}")
        for offset in range(0, len(cases), 8):
            batch = cases[offset:offset + 8]
            observations.append(_checked_run(fd, specs[spec_id], batch))
            if spec_id == candidate.spec_id:
                observations.append(_checked_run(fd, candidate, batch))
    return observations


def _qualify_histories(fd: int, spec: PreparedSpec) -> list[dict[str, object]]:
    observations = []
    for history in stateful_histories():
        observed = _checked_run(fd, spec, history.cases)
        state = history.initial_last_nonce
        outputs = observed["observation"]
        if not isinstance(outputs, dict):
            raise ValueError("missing trace observation")
        for case, output in zip(history.cases, outputs["outputs"], strict=True):
            if case.inputs[1] != state:
                raise ValueError("history predecessor does not match previously observed outcome")
            if output == (1,):
                state = case.inputs[0]
        if state != history.final_last_nonce:
            raise ValueError("observed history final nonce differs from fixed witness")
        observations.append({"name": history.name, "initial_last_nonce": history.initial_last_nonce,
                             "final_last_nonce": state, "trace": observed})
    if not observations:
        raise ValueError("missing history corpus")
    return observations


def _benchmark(fd: int, original: PreparedSpec, candidate: PreparedSpec, repeats: int) -> dict[str, object]:
    cases = tuple(case for case in corpus() if case.spec_id == original.spec_id)[:8]
    # Warmups execute and validate the same cases; only their timings are omitted.
    warmups = [_checked_run(fd, spec, cases) for spec in (original, candidate)]
    observations = []
    durations: dict[str, list[int]] = {variant.value: [] for variant in Variant}
    for repeat in range(repeats):
        pair = (original, candidate) if repeat % 2 == 0 else (candidate, original)
        for spec in pair:
            result = _checked_run(fd, spec, cases)
            result["repeat"] = repeat
            observation = result["observation"]
            if not isinstance(observation, dict) or type(observation["elapsed_ns"]) is not int:
                raise ValueError("missing benchmark observation")
            durations[spec.variant.value].append(observation["elapsed_ns"])
            observations.append(result)
    original_ns = sorted(durations[Variant.ORIGINAL.value])[repeats // 2]
    candidate_ns = sorted(durations[Variant.CONSERVATION_ELISION.value])[repeats // 2]
    threshold_met = candidate_ns * 100 <= original_ns * 80
    return {
        "repeats": repeats, "order": "alternating; fresh process each invocation",
        "warmups": warmups, "runs": observations,
        "original_median_ns": original_ns, "candidate_median_ns": candidate_ns,
        "at_least_twenty_percent_faster": threshold_met,
        "decision": "RESEARCH_CANDIDATE_FOR_BROADER_BENCHMARK" if threshold_met else "SPEEDUP_NOT_ESTABLISHED",
        "production_adopted": False,
    }


def run_qualification(binary: Path, *, repeats: int = 3) -> dict[str, object]:
    if type(repeats) is not int or repeats not in (3, 5):
        raise ValueError("benchmark repeats must be three or five")
    before = source_subject()
    if before.get("src/integration/tau_runner.py") != NORMALIZER_SHA256:
        raise ValueError("Tau normalizer source drift")
    sources = {spec_id: _read_bounded_regular_file_v1(SPEC_DIRECTORY / f"{spec_id}.tau", 16384, "spec")
               for spec_id in SPEC_IDS}
    specs: dict[str, PreparedSpec] = {
        spec_id: prepare(spec_id, source, Variant.ORIGINAL) for spec_id, source in sources.items()
    }
    transfer_source = sources["transfer_hook_guard_v1"]
    proof = check_conservation_equivalence(transfer_source.decode("ascii"))
    candidate = prepare("transfer_hook_guard_v1", transfer_source, Variant.CONSERVATION_ELISION)
    if proof.candidate_sha256 != candidate.selected_source_sha256:
        raise ValueError("proved candidate differs from executed candidate")
    with frozen_executable(binary, MEASURED_TAU_SHA256) as fd:
        observations = _qualify_corpus(fd, specs, candidate)
        histories = _qualify_histories(fd, specs["nonce_manager_v1"])
        benchmark = _benchmark(fd, specs[candidate.spec_id], candidate, repeats)
    if source_subject() != before:
        raise ValueError("repository source changed during qualification")
    return {
        "schema": "tau-economic-qualification-v1", "status": "PASS", "authority": "NONE",
        "production_security_claim": False, "binary_sha256": MEASURED_TAU_SHA256,
        "sources_sha256": before, "engine_options": ENGINE_OPTIONS,
        "execution": "sealed measured ELF and per-stream sealed inputs; bounded raw ASCII IO",
        "solver_equivalence": asdict(proof), "corpus": observations,
        "caller_state_histories": histories, "benchmark": benchmark,
        "nonclaims": ["authenticated ownership, balances, signatures or host witnesses",
                      "runtime publication, replay consumption or persistent nonce updates",
                      "full-domain Tau implementation refinement", "non-Boolean sbf execution coverage",
                      "reproducible Tau source build", "cross-machine performance or peak memory",
                      "Tau-internal stateful policy qualification", "production readiness"],
        "trusted_host": "loaded Python/solver code, OS, dynamic loader and system libraries; source hashes are not attestation",
    }


def atomic_report(path: Path, report: dict[str, object]) -> None:
    """Atomically replace one caller-owned report; no durability claim is made."""
    rendered = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8")
    if len(rendered) > 2 * 1024 * 1024:
        raise ValueError("qualification report exceeds resource bound")
    descriptor, temporary_name = tempfile.mkstemp(prefix=".tau-report-", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(rendered)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        # A failed cleanup never turns a successfully installed report into a
        # claimed publication failure. At most one bounded temp file remains.
        try:
            temporary.unlink(missing_ok=True)
        except OSError:
            pass


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tau-binary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repeats", type=int, default=3)
    arguments = parser.parse_args()
    try:
        atomic_report(arguments.output, {"status": "INCOMPLETE", "authority": "NONE"})
    except (ValueError, OSError) as exc:
        print(json.dumps({"status": "FAIL", "authority": "NONE", "error": str(exc),
                          "output_state": "UNVERIFIED_PREEXISTING", "stale_output_possible": True}, sort_keys=True))
        return 1
    try:
        report = run_qualification(arguments.tau_binary, repeats=arguments.repeats)
    except (ValueError, TypeError, OSError, subprocess.TimeoutExpired) as exc:
        report = {"status": "FAIL", "authority": "NONE", "error": str(exc)}
    try:
        atomic_report(arguments.output, report)
    except (ValueError, OSError) as exc:
        report = {"status": "FAIL", "authority": "NONE", "error": str(exc), "output_state": "INCOMPLETE"}
    print(json.dumps({key: value for key, value in report.items()
                      if key in ("status", "authority", "error", "output_state")}, sort_keys=True))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
