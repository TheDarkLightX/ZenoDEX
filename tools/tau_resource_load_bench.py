#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]

import sys

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


StepGen = Callable[[int], dict[str, int]]


def _gen_resource_budget(i: int) -> dict[str, int]:
    hot = 1 if (i % 13 == 0) else 0
    degraded = 1 if (i % 17 == 0) else 0
    backpressure_bad = 1 if (i % 37 == 0) else 0
    return {
        "i1": 0 if hot else 1,                 # core_limits_ok
        "i2": 1 if (hot == 0 or degraded == 1) else 0,  # cache_path_ok
        "i3": 0 if backpressure_bad else 1,    # backpressure_clear_ok
        "i4": 1 if (i % 23) != 0 else 0,       # retry_budget_ok
        "i5": 1 if (i % 19) != 0 else 0,       # io_backlog_ok
        "i6": 1 if (i % 43) != 0 else 0,       # witness_complete_ok
        "i7": 1,                               # policy_epoch_ok
        "i8": 1 if (i % 47) != 0 else 0,       # telemetry_fresh_ok
        "i9": 1 if (i % 5) != 0 else 0,        # require_telemetry_fresh
        "i10": 1 if (i % 7) != 0 else 0,       # require_cache_path
        "i11": 1,                              # proof_ok
        "i12": 1,                              # binding_ok
    }


def _gen_artifact_binding(i: int) -> dict[str, int]:
    replay_required = 1 if (i % 8) != 0 else 0
    signer_required = 1 if (i % 6) != 0 else 0
    optional_artifacts_required = 1 if (i % 10) != 0 else 0
    return {
        "i1": 1 if (i % 9) != 0 else 0,        # hash_binding_ok
        "i2": 1 if (replay_required == 0 or (i % 21) != 0) else 0,   # anti_replay_ok
        "i3": 1 if (signer_required == 0 or (i % 16) != 0) else 0,   # signer_attestation_ok
        "i4": 1 if (optional_artifacts_required == 0 or (i % 14) != 0) else 0,  # optional_artifacts_ok
        "i5": 1 if (i % 25) != 0 else 0,       # epoch_match_ok
        "i6": signer_required,                 # require_signer_attestation
        "i7": optional_artifacts_required,     # require_optional_artifacts
        "i8": replay_required,                 # require_replay_guard
        "i9": 1,                               # proof_ok
        "i10": 1,                              # binding_ok
        "i11": 1 if (i % 18) != 0 else 0,      # quorum_hysteresis_ok
        "i12": 1 if (i % 13) != 0 else 0,      # policy_hash_fresh_ok
    }


def _gen_load_shedding(i: int) -> dict[str, int]:
    load_shed = 1 if (i % 8 == 0) else 0
    strict = 1 if (i % 4 == 0) else 0
    user_ok = 1 if (i % 5 != 0) else 0
    return {
        "i1": 1 if load_shed == 0 else 0,
        "i2": 1,
        "i3": user_ok,
        "i4": user_ok,
        "i5": user_ok,
        "i6": 1,
        "i7": 1,
        "i8": load_shed,
        "i9": 1 if load_shed == 1 else 0,
        "i10": strict,
        "i11": 1,
        "i12": 1,
    }


def _gen_perp_risk_envelope(i: int) -> dict[str, int]:
    shock = 1 if (i % 17 == 0) else 0
    mark = 100_000 + (i % 200)
    oracle = mark - (300 if shock else 20)
    prev_mark = mark - 10
    prev_oracle = oracle - 10
    return {
        "i1": mark,
        "i2": oracle,
        "i3": prev_mark,
        "i4": prev_oracle,
        "i5": 1_000_000 + (i % 10_000),
        "i6": 2_000_000,
        "i7": 40 + (i % 20),
        "i8": 100,
        "i9": 50,
        "i10": 100,
        "i11": 1_000_000,
        "i12": 200_000,
        "i13": 1 if shock else 0,
        "i14": 0,
        "i15": 1,
        "i16": 1,
        "i17": 1,
        "i18": 900,
        "i19": 500,
        "i20": 400,
        "i21": 120,
        "i22": 120,
    }


def _gen_swap_exec_regret(i: int) -> dict[str, int]:
    bad = 1 if (i % 10 == 0) else 0
    return {
        "i1": 0 if bad else 1,
        "i2": 1,
        "i3": 1,
        "i4": 1,
        "i5": 1,
        "i6": 1,
        "i7": 1,
        "i8": 1,
        "i9": 1,
        "i10": 1,
        "i11": 1,
        "i12": 1,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Benchmark Tau resource/regret specs under step load.")
    ap.add_argument("--steps", type=int, default=512)
    ap.add_argument("--max-seconds", type=float, default=60.0)
    ap.add_argument("--out", type=Path, default=Path("runs/tau_resource_load_bench/latest.json"))
    ap.add_argument(
        "--tau-bin",
        type=Path,
        help="Override Tau binary path (default: auto-detect; or set TAU_BIN=/path/to/tau).",
    )
    ap.add_argument(
        "--include-perp-risk",
        action="store_true",
        help="Include perp_risk_envelope_proof_gate_v1 in the benchmark set.",
    )
    args = ap.parse_args()

    tau_bin = str(args.tau_bin) if getattr(args, "tau_bin", None) else find_tau_bin(ROOT)
    if not tau_bin:
        raise SystemExit("tau binary not found (set TAU_BIN=/path/to/tau or build external/tau-lang/build-Release/tau)")

    bench_specs: list[tuple[str, Path, str, StepGen]] = [
        ("resource_budget_guard_v1", ROOT / "src/tau_specs/recommended/resource_budget_guard_v1.tau", "o3", _gen_resource_budget),
        ("resource_artifact_binding_guard_v1", ROOT / "src/tau_specs/recommended/resource_artifact_binding_guard_v1.tau", "o5", _gen_artifact_binding),
        ("resource_load_shedding_regret_guard_v1", ROOT / "src/tau_specs/recommended/resource_load_shedding_regret_guard_v1.tau", "o6", _gen_load_shedding),
        ("swap_execution_regret_guard_v1", ROOT / "src/tau_specs/recommended/swap_execution_regret_guard_v1.tau", "o4", _gen_swap_exec_regret),
    ]
    if args.include_perp_risk:
        bench_specs.append(
            ("perp_risk_envelope_proof_gate_v1", ROOT / "src/tau_specs/recommended/perp_risk_envelope_proof_gate_v1.tau", "o11", _gen_perp_risk_envelope)
        )

    steps_n = max(1, int(args.steps))
    max_seconds = float(args.max_seconds)
    results: list[dict[str, object]] = []

    for sid, spec_path, gate_out, gen in bench_specs:
        steps = [gen(i) for i in range(steps_n)]
        t0 = time.time()
        try:
            outputs = run_tau_spec_steps(
                tau_bin=tau_bin,
                spec_path=spec_path,
                steps=steps,
                timeout_s=max_seconds,
            )
            elapsed = float(time.time() - t0)
            accepts = sum(1 for i in range(steps_n) if int(outputs.get(i, {}).get(gate_out, 0)) == 1)
            results.append(
                {
                    "spec_id": sid,
                    "spec_path": str(spec_path),
                    "gate_output": gate_out,
                    "steps": steps_n,
                    "elapsed_s": elapsed,
                    "per_step_ms": (elapsed * 1000.0) / float(steps_n),
                    "accept_count": int(accepts),
                    "accept_rate": float(accepts) / float(steps_n),
                    "within_budget": bool(elapsed <= max_seconds),
                }
            )
        except Exception as exc:
            elapsed = float(time.time() - t0)
            results.append(
                {
                    "spec_id": sid,
                    "spec_path": str(spec_path),
                    "gate_output": gate_out,
                    "steps": steps_n,
                    "elapsed_s": elapsed,
                    "error": f"{type(exc).__name__}: {exc}",
                    "within_budget": False,
                }
            )

    ok = all(bool(r.get("within_budget")) for r in results)
    payload = {
        "ok": ok,
        "tau_bin": str(tau_bin),
        "steps": steps_n,
        "max_seconds": max_seconds,
        "results": results,
    }

    out_path = args.out if args.out.is_absolute() else (ROOT / args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(json.dumps({"ok": ok, "out": str(out_path)}, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
