#!/usr/bin/env python3
"""Bounded Tau feature and nonce-factorization probe; emits JSON, never edits specs.

Exit 0 means the requested probes completed, including explicit unsupported/error
results. Each result has its own acceptance status. Timings are observational.
This tool grants no runtime, publication, settlement, or release authority.
The timeout is the existing runner's initial attempt budget: its spec-mode
fallback can retry once with 25 seconds. Reported timings include this behavior.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from src.integration.tau_runner import (  # noqa: E402
    extract_always_exprs,
    inline_definitions,
    normalize_spec_text,
    parse_definitions,
    run_tau_spec_steps,
)


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def expanded_bytes(source: str) -> int:
    normalized = normalize_spec_text(source)
    definitions = parse_definitions(normalized)
    expanded = [
        inline_definitions(expr, definitions)
        for expr in extract_always_exprs(normalized)
    ]
    return len("\n".join(expanded).encode())


def nonce_cases() -> tuple[list[dict[str, int]], dict[int, dict[str, int]]]:
    maximum = (1 << 32) - 1
    rows = [(1, 0, 1), (2, 1, 2), (0, 0, 1), (2, 0, 1),
            (1, 0, 2), (maximum, maximum - 1, maximum),
            (0, maximum, 0), (maximum, maximum, 0)]
    steps = [dict(zip(("i1", "i2", "i3"), row, strict=True)) for row in rows]
    expected = {}
    for index, (intent, last, supplied_next) in enumerate(rows):
        params = supplied_next == (last + 1) % (1 << 32)
        fresh = intent > last
        sequential = intent == supplied_next
        expected[index] = {"o1": int(params), "o2": int(fresh),
                           "o3": int(sequential),
                           "o4": int(params and fresh and sequential)}
    return steps, expected


def factorization_miter() -> dict[str, object]:
    """Check exact equivalence of equality-to-top propositions, including rejects."""
    for p, q, r, a, b, c, d in itertools.product((False, True), repeat=7):
        components = (a == p) and (b == q) and (c == r)
        baseline = components and (d == (p and q and r))
        candidate = components and (d == (a and b and c))
        if baseline != candidate:
            return {"status": "MISMATCH", "assignment": [p, q, r, a, b, c, d]}
    return {"status": "PASS_EXHAUSTIVE_PROPOSITIONAL", "assignments": 128}


def run_case(binary: Path, source: str, steps: list[dict[str, int]],
             expected: dict[int, dict[str, int]], repeats: int,
             timeout_s: float) -> dict[str, object]:
    elapsed: list[int] = []
    with tempfile.TemporaryDirectory(prefix="zenodex-tau-adt-probe-") as scratch:
        spec = Path(scratch) / "probe.tau"
        spec.write_text(source, encoding="utf-8")
        for _ in range(repeats):
            start = time.perf_counter_ns()
            try:
                actual = run_tau_spec_steps(str(binary), spec, steps,
                                            timeout_s=timeout_s)
            except (OSError, RuntimeError, ValueError) as exc:
                return {"status": "ERROR_OR_UNSUPPORTED", "error": str(exc)[:400],
                        "completed_repetitions": len(elapsed)}
            elapsed.append(time.perf_counter_ns() - start)
            if actual != expected:
                return {"status": "MISMATCH", "actual": actual, "expected": expected}
    return {"status": "PASS_BOUNDED_TRACE", "steps": len(steps),
            "repeats": repeats, "elapsed_ns": elapsed,
            "median_elapsed_ns": int(statistics.median(elapsed)),
            "expanded_formula_bytes": expanded_bytes(source),
            "source_sha256": digest(source.encode())}


def cli_probe(binary: Path, command: str) -> dict[str, object]:
    try:
        result = subprocess.run(
            [str(binary), "--severity", "error", "--charvar", "false",
             "--evaluate", command], cwd="/tmp", capture_output=True,
            text=True, timeout=3, check=False,
        )
    except subprocess.TimeoutExpired:
        return {"status": "TIMEOUT"}
    return {"status": "OBSERVATION_ONLY", "returncode": result.returncode,
            "stdout": result.stdout[:600], "stderr": result.stderr[:600]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tau-bin", type=Path, required=True)
    parser.add_argument("--repeats", type=int, choices=range(1, 4), default=3)
    parser.add_argument("--timeout-s", type=float, default=3,
                        help="initial runner budget; inherited fallback may retry for 25 seconds")
    args = parser.parse_args()
    if not 0 < args.timeout_s <= 5:
        parser.error("--timeout-s must be greater than 0 and at most 5")
    binary = args.tau_bin.resolve(strict=True)
    spec_path = ROOT / "src/tau_specs/recommended/nonce_replay_guard_v1.tau"
    baseline = spec_path.read_text(encoding="utf-8")
    original = "(o4[t]:sbf = 1:sbf <-> nonce_replay_valid(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32]))"
    replacement = (
        "(o4[t]:sbf = 1:sbf <-> ((o1[t]:sbf = 1:sbf) && "
        "(o2[t]:sbf = 1:sbf) && (o3[t]:sbf = 1:sbf)))"
    )
    if baseline.count(original) != 1:
        parser.error("nonce source changed: exact candidate replacement is unavailable")
    candidate = baseline.replace(original, replacement)
    steps, expected = nonce_cases()
    results = {
        "nonce_factorization_miter": factorization_miter(),
        "nonce_baseline": run_case(binary, baseline, steps, expected,
                                   args.repeats, args.timeout_s),
        "nonce_reuse_current_outputs": run_case(binary, candidate, steps, expected,
                                                args.repeats, args.timeout_s),
    }
    for width in (32, 64, 256):
        source = f"always (o1[t]:bv[{width}] = i1[t]:bv[{width}]).\n"
        values = [0, 1, (1 << width) - 1]
        results[f"copy_bv{width}"] = run_case(
            binary, source, [{"i1": value} for value in values],
            {index: {"o1": value} for index, value in enumerate(values)},
            1, args.timeout_s,
        )
    parity_rows = list(itertools.product((0, 1), repeat=4))
    parity = "always (o1[t]:sbf = " + " ^ ".join(
        f"i{index}[t]:sbf" for index in range(1, 5)) + ").\n"
    results["xor4"] = run_case(
        binary, parity,
        [{f"i{index + 1}": value for index, value in enumerate(row)} for row in parity_rows],
        {index: {"o1": sum(row) % 2} for index, row in enumerate(parity_rows)},
        1, args.timeout_s,
    )
    results["adt_alias_registration"] = cli_probe(binary, "type byte = bv[8]. defs.")
    version = subprocess.run([str(binary), "--version"], capture_output=True,
                             text=True, timeout=3, check=True).stdout.strip()
    report = {"schema": "zenodex/tau-adt-optimization-probe/v1",
              "binary_sha256": digest(binary.read_bytes()), "version": version,
              "runner_sha256": digest((ROOT / "src/integration/tau_runner.py").read_bytes()),
              "nonce_source_sha256": digest(baseline.encode()), "results": results,
              "authority": "NONE", "timings": "OBSERVATIONAL_SHARED_HOST",
              "initial_attempt_timeout_s": args.timeout_s,
              "inherited_spec_fallback_retry_timeout_s": 25}
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
