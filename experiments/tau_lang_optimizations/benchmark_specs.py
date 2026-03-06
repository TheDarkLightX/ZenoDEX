from __future__ import annotations

import statistics
import sys
import time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


@dataclass(frozen=True)
class Case:
    label: str
    path: Path
    step: dict[str, int]
    runs: int = 1
    timeout_s: float = 10.0


CASES: list[Case] = [
    Case(
        label="baseline_batching_v1_4",
        path=ROOT / "src/tau_specs/batching_v1_4.tau",
        step={f"i{i}": i for i in range(1, 9)},
        runs=3,
        timeout_s=30.0,
    ),
    Case(
        label="experiment_batching_v1_5_compact",
        path=ROOT / "experiments/tau_lang_optimizations/batching_v1_5_compact_single_gate.tau",
        step={f"i{i}": i for i in range(1, 9)},
        runs=3,
        timeout_s=30.0,
    ),
    Case(
        label="experiment_batching_v1_5_explained",
        path=ROOT / "experiments/tau_lang_optimizations/batching_v1_5_explained.tau",
        step={f"i{i}": i for i in range(1, 9)},
        runs=3,
        timeout_s=30.0,
    ),
    Case(
        label="baseline_swap_exact_in_v4",
        path=ROOT / "src/tau_specs/swap_exact_in_v4.tau",
        step={"i1": 100, "i2": 100, "i3": 10, "i4": 29, "i5": 1, "i6": 9, "i7": 110, "i8": 91},
    ),
    Case(
        label="experiment_swap_exact_in_v5_hybrid",
        path=ROOT / "experiments/tau_lang_optimizations/swap_exact_in_v5_hybrid_flags.tau",
        step={"i1": 100, "i2": 100, "i3": 10, "i4": 29, "i5": 1, "i6": 9, "i7": 110, "i8": 91, "i9": 1, "i10": 1},
    ),
    Case(
        label="experiment_swap_exact_in_v5_compact",
        path=ROOT / "experiments/tau_lang_optimizations/swap_exact_in_v5_compact_single_gate.tau",
        step={"i1": 100, "i2": 100, "i3": 10, "i4": 29, "i5": 1, "i6": 9, "i7": 110, "i8": 91, "i9": 1, "i10": 1},
    ),
    Case(
        label="baseline_swap_exact_out_v4",
        path=ROOT / "src/tau_specs/swap_exact_out_v4.tau",
        step={"i1": 100, "i2": 100, "i3": 9, "i4": 29, "i5": 20, "i6": 10, "i7": 110, "i8": 91},
    ),
    Case(
        label="experiment_swap_exact_out_v5_hybrid",
        path=ROOT / "experiments/tau_lang_optimizations/swap_exact_out_v5_hybrid_flags.tau",
        step={"i1": 100, "i2": 100, "i3": 9, "i4": 29, "i5": 20, "i6": 10, "i7": 110, "i8": 91, "i9": 1, "i10": 1},
    ),
    Case(
        label="experiment_swap_exact_out_v5_compact",
        path=ROOT / "experiments/tau_lang_optimizations/swap_exact_out_v5_compact_single_gate.tau",
        step={"i1": 100, "i2": 100, "i3": 9, "i4": 29, "i5": 20, "i6": 10, "i7": 110, "i8": 91, "i9": 1, "i10": 1},
    ),
    Case(
        label="baseline_settlement_v4",
        path=ROOT / "src/tau_specs/settlement_v4_buyback_floor_rebate_lock.tau",
        step={f"i{i}": 1 for i in range(1, 54)},
    ),
    Case(
        label="experiment_settlement_v5_aligned",
        path=ROOT / "experiments/tau_lang_optimizations/settlement_v5_aligned_inputs.tau",
        step={f"i{i}": 1 for i in range(1, 54)},
    ),
    Case(
        label="experiment_settlement_v5_module_flags",
        path=ROOT / "experiments/tau_lang_optimizations/settlement_v5_module_flags.tau",
        step={"i1": 1, "i2": 2, "i3": 3, "i4": 4, "i5": 10, "i6": 11, "i7": 12, "i8": 1, "i9": 1, "i10": 1, "i11": 1, "i12": 1, "i13": 1},
    ),
]


def _run_case(tau_bin: str, case: Case) -> tuple[str, list[float], str]:
    samples: list[float] = []
    last_outputs = ""
    for _ in range(case.runs):
        started = time.perf_counter()
        try:
            outputs = run_tau_spec_steps(tau_bin, case.path, [case.step], timeout_s=case.timeout_s)
        except Exception as exc:
            elapsed_ms = (time.perf_counter() - started) * 1000.0
            detail = str(exc)
            if "timed out" in detail:
                return "timeout", samples + [elapsed_ms], detail
            return "error", samples + [elapsed_ms], detail
        samples.append((time.perf_counter() - started) * 1000.0)
        last_outputs = str(outputs)
    return "ok", samples, last_outputs


def main() -> int:
    tau_bin = find_tau_bin(ROOT)
    if not tau_bin:
        raise SystemExit("Tau binary not found")

    print(f"tau_bin={tau_bin}")
    print("label,status,run_ms")

    summaries: list[tuple[str, str, str]] = []
    for case in CASES:
        status, samples, detail = _run_case(tau_bin, case)
        for sample in samples:
            print(f"{case.label},{status},{sample:.2f}")
        if status == "ok":
            mean_ms = statistics.mean(samples)
            stdev_ms = statistics.pstdev(samples) if len(samples) > 1 else 0.0
            summaries.append((case.label, status, f"mean={mean_ms:.2f}ms stdev={stdev_ms:.2f}ms outputs={detail}"))
        else:
            summaries.append((case.label, status, detail))

    print("\nsummary")
    for label, status, detail in summaries:
        print(f"{label}: {status} {detail}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
