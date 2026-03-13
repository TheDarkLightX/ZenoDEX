#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
import time
from pathlib import Path
from typing import Dict


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.tau_lang_optimizations.trace_cases import TauOptimizationTraceCase, optimization_tau_trace_cases  # noqa: E402
from src.integration.tau_runner import TauRunError, find_tau_bin, run_tau_spec_steps_spec_mode_with_trace  # noqa: E402
from src.integration.tau_runner import run_tau_spec_steps_with_trace  # noqa: E402


def _compare_expected(outputs_by_step: Dict[int, Dict[str, int]], expected: list[dict[str, int]], *, label: str) -> None:
    for idx, exp_step in enumerate(expected):
        got = outputs_by_step.get(idx, {})
        for name, exp_val in exp_step.items():
            if got.get(name) != exp_val:
                raise RuntimeError(f"{label}: {name}[{idx}] expected {exp_val} got {got.get(name)}")


def _run_case(tau_bin: str, case: TauOptimizationTraceCase):
    if case.mode == "spec":
        return run_tau_spec_steps_spec_mode_with_trace(
            tau_bin=tau_bin,
            spec_path=case.spec_path,
            steps=case.steps,
            timeout_s=float(case.timeout_s),
            severity="error",
        )
    return run_tau_spec_steps_with_trace(
        tau_bin=tau_bin,
        spec_path=case.spec_path,
        steps=case.steps,
        timeout_s=float(case.timeout_s),
        severity="error",
        inline_defs=case.inline_defs,
    )


def main() -> int:
    tau_bin = find_tau_bin(ROOT)
    if not tau_bin:
        raise SystemExit("tau binary not found")

    out_root = ROOT / "generated" / "tau_lang_optimization_traces"
    out_root.mkdir(parents=True, exist_ok=True)

    atomic_outputs: dict[str, Dict[int, Dict[str, int]]] = {}
    results: list[dict[str, object]] = []
    ok_all = True

    for case in optimization_tau_trace_cases():
        case_dir = out_root / case.case_id
        case_dir.mkdir(parents=True, exist_ok=True)
        start = time.perf_counter()
        error = None
        try:
            if case.mode == "spec":
                outputs, stdout_text, stderr_text, spec_text, input_text = _run_case(tau_bin, case)
                repl_text = ""
            else:
                outputs, stdout_text, stderr_text, repl_text = _run_case(tau_bin, case)
                spec_text = ""
                input_text = ""
            _compare_expected(outputs, case.expected, label=case.case_id)
            atomic_outputs[case.case_id] = outputs
            status = "PASS"
        except TauRunError as exc:
            outputs = {}
            stdout_text = exc.stdout
            stderr_text = exc.stderr
            repl_text = exc.repl_script
            spec_text = exc.spec_text
            input_text = exc.input_text
            error = f"{type(exc).__name__}: {exc}"
            status = "FAIL"
            ok_all = False
        except Exception as exc:
            outputs = {}
            stdout_text = ""
            stderr_text = ""
            repl_text = ""
            spec_text = ""
            input_text = ""
            error = f"{type(exc).__name__}: {exc}"
            status = "FAIL"
            ok_all = False

        elapsed_ms = (time.perf_counter() - start) * 1000.0
        (case_dir / "expected.json").write_text(json.dumps(case.expected, indent=2), encoding="utf-8")
        (case_dir / "outputs.json").write_text(json.dumps(outputs, indent=2), encoding="utf-8")
        (case_dir / "stdout.txt").write_text(stdout_text or "", encoding="utf-8", errors="replace")
        (case_dir / "stderr.txt").write_text(stderr_text or "", encoding="utf-8", errors="replace")
        if repl_text:
            (case_dir / "repl_script.tau").write_text(repl_text, encoding="utf-8", errors="replace")
        if spec_text:
            (case_dir / "spec_normalized.tau").write_text(spec_text, encoding="utf-8", errors="replace")
        if input_text:
            (case_dir / "spec_inputs.txt").write_text(input_text, encoding="utf-8", errors="replace")

        print(f"[{status}] {case.case_id} elapsed_ms={elapsed_ms:.2f}")
        if error:
            print(f"  {error}")

        results.append(
            {
                "case_id": case.case_id,
                "spec_id": case.spec_path.stem,
                "spec_path": str(case.spec_path),
                "status": status,
                "mode": case.mode,
                "timeout_s": case.timeout_s,
                "elapsed_ms": elapsed_ms,
                "elapsed_s": elapsed_ms / 1000.0,
                "expected": case.expected,
                "outputs_by_step": outputs,
                "rationale": case.rationale,
                "error": error,
                "artifacts_dir": str(case_dir),
            }
        )

    composite_results: list[dict[str, object]] = []

    def _o1(case_id: str) -> int:
        return int(atomic_outputs[case_id][0]["o1"])

    composites = [
        (
            "composed_batching_pass",
            _o1("batching_all_distinct_included_pass")
            & _o1("batching_all_distinct_executed_pass")
            & _o1("batching_left_in_right_exec_in_included_pass")
            & _o1("batching_left_in_right_included_in_exec_pass")
            & _o1("batching_sorted_exec_pass"),
            1,
            "Distinctness, bidirectional membership, and strict ordering all hold for the canonical batch.",
        ),
        (
            "composed_swap_exact_in_pass",
            _o1("swap_exact_in_proof_gate_pass") & _o1("swap_range_guard_pass"),
            1,
            "Proof-gated exact-in structure and safe-range guard both pass.",
        ),
        (
            "composed_swap_exact_in_fail_large_values",
            _o1("swap_exact_in_proof_gate_large_values_pass") & _o1("swap_range_guard_fail_large_values"),
            0,
            "The proof gate passes, but the added safe-range policy fails on large values.",
        ),
        (
            "composed_swap_exact_out_pass",
            _o1("swap_exact_out_proof_gate_pass") & _o1("swap_range_guard_pass_exact_out"),
            1,
            "Proof-gated exact-out structure and safe-range guard both pass.",
        ),
        (
            "composed_swap_exact_out_fail_large_values",
            _o1("swap_exact_out_proof_gate_large_values_pass") & _o1("swap_range_guard_fail_large_values_exact_out"),
            0,
            "The exact-out proof gate passes, but the added safe-range policy fails on large values.",
        ),
        (
            "composed_settlement_pass",
            _o1("settlement_price_rails_pass") & _o1("settlement_module_bundle_pass"),
            1,
            "Aligned price rails and module-flag bundle both pass.",
        ),
        (
            "composed_settlement_fail_rebate",
            _o1("settlement_price_rails_pass") & _o1("settlement_module_bundle_fail_rebate_flag"),
            0,
            "Price rails pass, but the module bundle fails because the rebate flag is cleared.",
        ),
    ]

    for case_id, got, expected, rationale in composites:
        status = "PASS" if got == expected else "FAIL"
        if status != "PASS":
            ok_all = False
        print(f"[{status}] {case_id} got={got} expected={expected}")
        composite_results.append(
            {
                "case_id": case_id,
                "status": status,
                "got": got,
                "expected": expected,
                "rationale": rationale,
            }
        )

    report_path = out_root / "report.json"
    report_path.write_text(json.dumps({"ok": ok_all, "atomic_results": results, "composite_results": composite_results}, indent=2), encoding="utf-8")
    print(f"wrote {report_path}")
    return 0 if ok_all else 1


if __name__ == "__main__":
    raise SystemExit(main())
