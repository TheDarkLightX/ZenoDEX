#!/usr/bin/env python3
"""Replay the mounted signal codec, its finite Tau contract and transport costs.

Usage: python3 tools/benchmark_tau_signal_migration.py --tau PATH --out FRESH_DIR
The result is bounded advisory evidence. No candidate is installed by this tool.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import platform
import sys
import time
import zlib
from dataclasses import asdict
from itertools import product
from pathlib import Path
from statistics import median
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.autotrader_signal_profile import decode_profile  # noqa: E402
from src.integration.autotrader_signals import external_signal_observation_from_dict  # noqa: E402
from src.kernels.python.external_signal_profile_decode_v2 import (  # noqa: E402
    transform as decode_word,
)
from src.kernels.python.external_signal_profile_encode_v2 import (  # noqa: E402
    transform as encode_word,
)
from src.tau_composition.runtime import TauRuntime  # noqa: E402
from src.tau_swarm.exports import export_agent_gate, replay_agent_gate  # noqa: E402
from src.tau_workbench.catalog import outputs_of  # noqa: E402
from src.tau_workbench.codec import encode_task  # noqa: E402
from src.tau_workbench.compiler import compile_task  # noqa: E402
from src.tau_workbench.examples import program  # noqa: E402
from src.tau_workbench.models import Stage, Task  # noqa: E402
from src.tau_workbench.native import replay_bundles  # noqa: E402
from src.tau_workbench.programs import Program, analyze  # noqa: E402
from tools.benchmark_tau_workbench import _source_hashes as workbench_hashes  # noqa: E402
from tools.tau_signal_migration_case import (  # noqa: E402
    BASELINE,
    BASELINE_SOURCES,
    canonical,
    legacy_payload,
    observe,
)

ENCODER = "src/kernels/python/external_signal_profile_encode_v2.py"
DECODER = "src/kernels/python/external_signal_profile_decode_v2.py"
# Captured before editing; independently replayed from public base e1838293.
# These anchors prevent relabeling an edited fixture as the historical baseline.
BASELINE_SHA256 = "bde8c09ecd0c3f67b596e7ff93d758d48e6c7a7270edc9d9fea024f67ed0cd94"
LEGACY_REPLAY = "docs/research/tau_signal_migration_20260908/legacy_replay.json"
LEGACY_REPLAY_SHA256 = "2c1d9ecf1f9e48bf1f270b8106cc13a1804e3862593be4ebbcc365104a262200"
NEW_SOURCES = (
    ENCODER, DECODER, "src/integration/autotrader_signal_profile.py",
    "src/agents/tau_policy_adapter.py", "tools/tau_signal_migration_case.py",
    "tools/benchmark_tau_signal_migration.py", "tests/integration/test_tau_signal_migration.py",
    "tests/integration/test_autotrader_signal_profile.py", "tests/test_tau_signal_migration_benchmark.py",
    "docs/research/tau_signal_migration_spec_20260908.md", BASELINE, LEGACY_REPLAY,
)


def require(condition: bool, error: str) -> None:
    if not condition:
        raise ValueError(error)


def source_hashes() -> dict[str, str]:
    result = workbench_hashes()
    for name in (*BASELINE_SOURCES, *NEW_SOURCES):
        result[name] = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    return result


def signal_task() -> Task:
    """Real mounted sources plus independently coordinated alternative formats."""
    encode = Program("mounted_encoder", (ROOT / ENCODER).read_bytes())
    decode = Program("mounted_decoder", (ROOT / DECODER).read_bytes())
    def equivalent(p: Program, name: str) -> Program:
        return Program(name, p.source.replace(b"x < 128", b"(x & 128) == 0"))
    # Synthetic future-format alternatives and named negative controls.
    encoder = Stage("encoder", (
        encode, equivalent(encode, "equivalent_encoder"),
        program("semantic_order_encoder", "x if x < 128 else 255"),
        program("rotated_encoder", "((x << 1) & 127) | (x >> 6) if x < 128 else 255"),
        program("reserved_bit_lost_encoder", "x & 127"),
    ))
    decoder = Stage("decoder", (
        decode, equivalent(decode, "equivalent_decoder"),
        program("semantic_order_decoder", "x if x < 128 else 255"),
        program("rotated_decoder", "(x >> 1) | ((x & 1) << 6) if x < 128 else 255"),
        program("reserved_bit_lost_decoder", "x & 127"),
    ))
    return Task("external_signal_profile_v2", 8, (encoder, decoder), tuple(range(256)),
                tuple(x if x < 128 else 255 for x in range(256)),
                (encode.name, decode.name))


def baseline_parity() -> dict[str, object]:
    baseline_bytes = (ROOT / BASELINE).read_bytes()
    require(hashlib.sha256(baseline_bytes).hexdigest() == BASELINE_SHA256, "baseline_digest_mismatch")
    baseline = json.loads(baseline_bytes)
    legacy_bytes = (ROOT / LEGACY_REPLAY).read_bytes()
    require(hashlib.sha256(legacy_bytes).hexdigest() == LEGACY_REPLAY_SHA256, "legacy_replay_digest_mismatch")
    rows = baseline["rows"]
    require([r["semantic_word"] for r in rows] == list(range(128)), "baseline_domain")
    accepted = 0
    for row in rows:
        word = row["semantic_word"]
        require(row["input"] == legacy_payload(word), "baseline_input_drift")
        require(observe(row["input"]) == row["outcome"], "legacy_behavior_drift")
        compact = {key: row["input"][key] for key in ("signal_id", "source_id", "tags")}
        compact.update(schema="zenodex/autotrader-external-signal/v2", profile_code=encode_word(word))
        require(observe(compact) == row["outcome"], "compact_behavior_drift")
        accepted += row["outcome"]["status"] == "ACCEPT"
    for code in range(128, 256):
        try:
            decode_profile(code)
        except ValueError as exc:
            require(str(exc) == "code_reserved", "reserved_error_drift")
        else:
            raise ValueError("reserved_code_accepted")
    require(accepted == 14, "legacy_accept_count")
    return {"metadata_rows": 128, "accepted": accepted, "rejected": 128 - accepted,
            "reserved_bytes_rejected": 128, "baseline_sources": baseline["sources"],
            "baseline_sha256": BASELINE_SHA256, "historical_replay": json.loads(legacy_bytes),
            "historical_replay_sha256": LEGACY_REPLAY_SHA256,
            "normalized_fields_hashes_and_exact_errors_equal": True}


def cached_baselines(task: Task) -> tuple[dict[str, object], tuple[bool, ...]]:
    started = time.perf_counter()
    tables = tuple(tuple(analyze(p, 8).outputs for p in stage.programs) for stage in task.stages)
    analysis_seconds = time.perf_counter() - started
    require(tables[0][0] == tuple(encode_word(x) for x in range(256)), "mounted_encoder_drift")
    require(tables[1][0] == tuple(decode_word(x) for x in range(256)), "mounted_decoder_drift")
    started = time.perf_counter()
    raw = tuple(outputs_of(rows, task.inputs) == task.expected for rows in product(*tables))
    cached_seconds = time.perf_counter() - started
    started = time.perf_counter()
    classes = tuple(tuple(dict.fromkeys(rows)) for rows in tables)
    quotient = tuple(outputs_of(rows, task.inputs) == task.expected for rows in product(*classes))
    quotient_seconds = time.perf_counter() - started
    return {"source_analysis_seconds": analysis_seconds,
            "cached_artifact_checks": len(raw), "cached_artifact_seconds": cached_seconds,
            "quotient_class_checks": len(quotient), "quotient_seconds": quotient_seconds,
            "accepted_artifact_bundles": sum(raw), "accepted_class_bundles": sum(quotient)}, raw


def transport_benchmark(repetitions: int, trials: int) -> dict[str, object]:
    signals = tuple(external_signal_observation_from_dict(legacy_payload(x)) for x in range(128)
                    if observe(legacy_payload(x))["status"] == "ACCEPT")
    v1 = tuple(canonical(signal.to_dict()) for signal in signals)
    v2 = tuple(canonical(signal.to_compact_dict()) for signal in signals)
    actions: dict[str, Callable[[], object]] = {
        "encode_v1": lambda: tuple(canonical(s.to_dict()) for s in signals),
        "encode_v2": lambda: tuple(canonical(s.to_compact_dict()) for s in signals),
        "decode_guard_v1": lambda: tuple(external_signal_observation_from_dict(json.loads(x)) for x in v1),
        "decode_guard_v2": lambda: tuple(external_signal_observation_from_dict(json.loads(x)) for x in v2),
    }
    samples: dict[str, list[float]] = {name: [] for name in actions}
    for action in actions.values():
        for _ in range(20):
            action()
    for trial in range(trials):
        names = tuple(actions) if trial % 2 == 0 else tuple(reversed(actions))
        for name in names:
            started = time.perf_counter()
            for _ in range(repetitions):
                actions[name]()
            samples[name].append((time.perf_counter() - started) / (repetitions * len(signals)))
    sizes1, sizes2 = tuple(map(len, v1)), tuple(map(len, v2))
    batch1, batch2 = b"[" + b",".join(v1) + b"]", b"[" + b",".join(v2) + b"]"
    return {"observations_per_batch": len(signals), "repetitions": repetitions, "trials": trials,
            "clock": "perf_counter", "warmup_batches_per_action": 20,
            "order": "alternating_forward_reverse", "samples_seconds_per_signal": samples,
            "median_seconds_per_signal": {name: median(values) for name, values in samples.items()},
            "v1_bytes": sizes1, "v2_bytes": sizes2, "v1_total_bytes": sum(sizes1),
            "v2_total_bytes": sum(sizes2), "saved_bytes": sum(sizes1) - sum(sizes2),
            "saved_fraction": 1 - sum(sizes2) / sum(sizes1),
            "batch_v1_bytes": len(batch1), "batch_v2_bytes": len(batch2),
            "gzip6_batch_v1_bytes": len(gzip.compress(batch1, compresslevel=6, mtime=0)),
            "gzip6_batch_v2_bytes": len(gzip.compress(batch2, compresslevel=6, mtime=0)),
            "scope": "canonical JSON, fixed short identifiers and one tag; gzip is size-only, no network"}


def rolling_obstruction(legal: frozenset[tuple[int, ...]]) -> dict[str, object]:
    edges = tuple((a, b) for a in sorted(legal) for b in sorted(legal)
                  if sum(x != y for x, y in zip(a, b, strict=True)) == 1)
    # In this finite task each reversible format is an isolated legal class pair.
    require(len(legal) == 3 and not edges, "rolling_obstruction_changed")
    return {"legal_class_pairs": sorted(legal), "one_owner_change_edges": edges,
            "safe_rolling_path_between_distinct_formats": False,
            "scope": "candidate class graph; actual V1/V2 JSON schemas distinguish formats",
            "next_candidate": "source-bound mixed-version rollout planning with version tags"}


def run(runtime: TauRuntime, repetitions: int, trials: int) -> dict[str, Any]:
    before = source_hashes()
    parity = baseline_parity()
    task = signal_task()
    central, expected = cached_baselines(task)
    bundles = tuple(product(*(range(len(s.programs)) for s in task.stages)))
    native = replay_bundles(task, bundles)
    require(tuple(outcome is None for outcome in native.outcomes) == expected, "native_outcome_drift")
    started = time.perf_counter()
    compiled = compile_task(task, runtime)
    compile_seconds = time.perf_counter() - started
    compile_queries = len(runtime.records)
    gates = {}
    gate_outcomes = {}
    for block in compiled.envelope.problem.blocks:
        gates[block.name] = export_agent_gate(compiled.envelope, block.name)
        steps = tuple(dict(zip(block.controls, bits, strict=True))
                      for bits in product((False, True), repeat=len(block.controls)))
        gate_outcomes[block.name] = replay_agent_gate(runtime, compiled.envelope, block.name, steps)
    selected = compiled.check_selection(task.anchor)
    compiled.check_revision(selected)
    replacements = tuple(compiled.assess_replacement(s.name, s.programs[1]) for s in task.stages)
    require(all(r["status"] == "local_equivalent" for r in replacements), "replacement_drift")
    compiled.check_revision(tuple(s.programs[1] for s in task.stages))
    transport = transport_benchmark(repetitions, trials)
    runtime.check_subject()
    require(source_hashes() == before, "source_changed_during_run")
    return {
        "schema": "zenodex/tau-signal-migration/v1", "status": "PASS", "authority": "NONE",
        "python_version": platform.python_version(), "python_implementation": platform.python_implementation(),
        "zlib_version": zlib.ZLIB_RUNTIME_VERSION,
        "source_hashes": before, "binary_sha256": runtime.binary_sha256, "task_id": task.subject_id,
        "parity": parity, "central": central, "transport": transport,
        "tau": {"compile_seconds": compile_seconds, "compile_queries": compile_queries,
                "domains": compiled.domains,
                "members": [[p.name for p in compiled.members(i)] for i in range(2)],
                "gate_outcomes": gate_outcomes, "equivalent_replacements": replacements},
        "next_opportunity": rolling_obstruction(compiled.catalog.legal),
        "task": encode_task(task), "native_replay": asdict(native), "gates": gates,
        "native_queries": [asdict(record) for record in runtime.records],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tau", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--repetitions", type=int, default=1000)
    parser.add_argument("--trials", type=int, default=5)
    args = parser.parse_args(argv)
    try:
        require(1 <= args.repetitions <= 10000 and 1 <= args.trials <= 15, "benchmark_budget")
        require(not args.out.exists(), "output_exists")
        report = run(TauRuntime(args.tau, timeout_seconds=20), args.repetitions, args.trials)
        args.out.mkdir(parents=True, exist_ok=False)
        for name, source in report["gates"].items():
            (args.out / f"{name}.tau").write_text(source)
        (args.out / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    except (OSError, ValueError, RuntimeError) as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc), "authority": "NONE"}))
        return 1
    print(json.dumps({"status": "PASS", "task_id": report["task_id"], "authority": "NONE"}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
