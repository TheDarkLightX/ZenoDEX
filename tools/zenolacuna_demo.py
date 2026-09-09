#!/usr/bin/env python3
"""Generate fresh, reproducible ZenoLacuna tasks, omission witnesses and queue models."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict
from pathlib import Path
from time import perf_counter_ns

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.zenolacuna.codec import encode  # noqa: E402
from src.zenolacuna.engine import analyze  # noqa: E402
from src.zenolacuna.migration import (  # noqa: E402
    byte_roundtrip_scope,
    codec_scope,
    migration_report,
)
from src.zenolacuna.model import Candidate, LacunaError, Relation, Scope  # noqa: E402
from src.zenolacuna.proposals import proposal_packet  # noqa: E402
from src.zenolacuna.queue_model import Admission, audit_queue, esso_model, guard_table  # noqa: E402


def _python_relation_equal(scope: Scope, left: Relation, right: Relation) -> bool:
    """Ordinary set comparison baseline on the same owned finite observations."""
    return all(
        {(scope.outcomes[o].kind, scope.outcomes[o].observation) for o in left[c]}
        == {(scope.outcomes[o].kind, scope.outcomes[o].observation) for o in right[c]}
        for c in scope.assumptions
    )


def generate(output: Path, tau_binary: Path | None = None, *, run_esso: bool = False) -> dict[str, object]:
    output.mkdir(parents=True, exist_ok=False)
    started = perf_counter_ns()
    scope, _ = codec_scope(ROOT)
    discovery_ns = perf_counter_ns() - started
    (output / "task.json").write_bytes(encode(scope))
    candidate = Candidate("preserve-wire-compatibility", scope.hypotheses[0].allowed, scope.assumptions)
    (output / "candidate.json").write_bytes(encode(candidate))
    (output / "swarm_packet.json").write_bytes(encode(proposal_packet(scope)))
    (output / "codec_report.json").write_bytes(encode(migration_report(ROOT)))
    program_scope, program_candidate = byte_roundtrip_scope(ROOT)
    (output / "program_task.json").write_bytes(encode(program_scope))
    (output / "program_candidate.json").write_bytes(encode(program_candidate))
    for mode in Admission:
        # JSON is also valid YAML; using canonical JSON avoids a new YAML writer.
        (output / (mode.value.lower() + ".yaml")).write_bytes(encode(esso_model(mode)))
    queue = {
        "unguarded": {**asdict(audit_queue(Admission.UNGUARDED)), "admission": Admission.UNGUARDED.value},
        "guarded": {**asdict(audit_queue(Admission.PRESERVE_DECODING)), "admission": Admission.PRESERVE_DECODING.value},
        "permitted_actions": [{"state": asdict(state), "actions": tuple(a.value for a in actions)}
                              for state, actions in guard_table()],
        "claim": "Complete single-message version graph under the separately checked paired-XOR codec premise",
        "authority": "NONE",
    }
    (output / "queue_report.json").write_bytes(encode(queue))
    timings = []
    for _ in range(11):
        started = perf_counter_ns()
        report = analyze(scope)
        timings.append(perf_counter_ns() - started)
    summary: dict[str, object] = {
        "schema": "zenolacuna/demo-v1", "authority": "NONE", "profile": "SIMULATED",
        "scope_root": scope.root, "discovery_ns": discovery_ns,
        "finite_analysis_median_ns": sorted(timings)[len(timings) // 2],
        "interpretations": len(scope.hypotheses), "semantic_classes": len(report.classes),
        "worst_case_question_cost": report.policy.worst_cost,
        "tau": "NOT_RUN", "esso": "MODELS_GENERATED_NOT_VERIFIED",
    }
    if tau_binary is not None:
        from src.tau_composition.runtime import TauQueryError, TauRuntime
        from src.zenolacuna.ports.tau import compare, project_queue_guard
        try:
            runtime = TauRuntime(tau_binary, timeout_seconds=15, max_queries=8)
        except TauQueryError as error:
            raise LacunaError(error.code) from error
        comparisons = []
        for left, right in ((0, 0), (0, 1), (1, 2)):
            python_times = []
            for _ in range(11):
                started = perf_counter_ns()
                expected = _python_relation_equal(scope, scope.hypotheses[left].allowed,
                                                  scope.hypotheses[right].allowed)
                python_times.append(perf_counter_ns() - started)
            started = perf_counter_ns()
            result = compare(runtime, scope, scope.hypotheses[left].allowed, scope.hypotheses[right].allowed)
            comparisons.append({"left": left, "right": right, "result": asdict(result),
                                "elapsed_ns": perf_counter_ns() - started,
                                "python_relation_median_ns": sorted(python_times)[5]})
            if result.equivalent is None:
                raise LacunaError(result.code)
            if result.equivalent is not expected:
                raise LacunaError("BENCHMARK_BASELINE_DISAGREEMENT")
        (output / "tau_report.json").write_bytes(encode(comparisons))
        guard = project_queue_guard(runtime)
        (output / "tau_queue_guard.json").write_bytes(encode(asdict(guard)))
        if guard.guard is None:
            raise LacunaError(guard.code)
        summary["tau"] = "THREE_NATIVE_FINITE_RELATION_COMPARISONS_REPLAYED"
        summary["tau_guard"] = guard.code
    if run_esso:
        from src.zenolacuna.ports.esso import verify_queue
        results = [verify_queue(ROOT, mode) for mode in Admission]
        (output / "esso_report.json").write_bytes(encode([asdict(result) for result in results]))
        if results[0].verified is not False or results[1].verified is not True:
            raise LacunaError("ESSO_REPLAY_INCONCLUSIVE")
        summary["esso"] = "TWO_SOLVER_NEGATIVE_AND_POSITIVE_MODELS_CHECKED"
    sources = sorted((ROOT / "src/zenolacuna").rglob("*.py")) + [Path(__file__)]
    summary["source_sha256"] = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in sources}
    (output / "summary.json").write_bytes(encode(summary))
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="fresh output directory")
    parser.add_argument("--tau-bin", type=Path)
    parser.add_argument("--esso", action="store_true", help="run installed ESSO with Z3 and CVC5")
    args = parser.parse_args()
    try:
        summary = generate(args.out, args.tau_bin, run_esso=args.esso)
    except (LacunaError, OSError, ValueError) as error:
        print(json.dumps({"status": "REJECTED", "code": str(error), "authority": "NONE"}, sort_keys=True))
        return 1
    print(encode(summary).decode(), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
