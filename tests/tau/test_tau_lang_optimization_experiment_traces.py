from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.tau_lang_optimizations.trace_cases import optimization_tau_trace_cases  # noqa: E402
from src.integration.tau_runner import TauRunError, find_tau_bin, run_tau_spec_steps_spec_mode  # noqa: E402
from src.integration.tau_runner import run_tau_spec_steps  # noqa: E402


def test_tau_lang_optimization_experiment_traces() -> None:
    if os.environ.get("TAU_OPT_TRACE_TESTS") != "1":
        pytest.skip("set TAU_OPT_TRACE_TESTS=1 to run Tau optimization trace tests")

    tau_bin = find_tau_bin(ROOT)
    if not tau_bin:
        pytest.skip("tau not found")

    failures: list[str] = []
    outputs_by_case: dict[str, dict[int, dict[str, int]]] = {}

    for case in optimization_tau_trace_cases():
        try:
            if case.mode == "spec":
                outputs = run_tau_spec_steps_spec_mode(
                    tau_bin=tau_bin,
                    spec_path=case.spec_path,
                    steps=case.steps,
                    timeout_s=float(case.timeout_s),
                    severity="error",
                )
            else:
                outputs = run_tau_spec_steps(
                    tau_bin=tau_bin,
                    spec_path=case.spec_path,
                    steps=case.steps,
                    timeout_s=float(case.timeout_s),
                )
        except TauRunError as exc:
            failures.append(f"{case.case_id}: Tau failed: {exc}")
            continue
        except Exception as exc:
            failures.append(f"{case.case_id}: runner error: {type(exc).__name__}: {exc}")
            continue

        outputs_by_case[case.case_id] = outputs
        for idx, exp_step in enumerate(case.expected):
            got = outputs.get(idx, {})
            for name, exp_val in exp_step.items():
                if got.get(name) != exp_val:
                    failures.append(f"{case.case_id}: {name}[{idx}] expected {exp_val} got {got.get(name)}")

    if not failures:
        composed = [
            (
                "composed_batching_pass",
                outputs_by_case["batching_all_distinct_included_pass"][0]["o1"]
                & outputs_by_case["batching_all_distinct_executed_pass"][0]["o1"]
                & outputs_by_case["batching_left_in_right_exec_in_included_pass"][0]["o1"]
                & outputs_by_case["batching_left_in_right_included_in_exec_pass"][0]["o1"]
                & outputs_by_case["batching_sorted_exec_pass"][0]["o1"],
                1,
            ),
            ("composed_swap_exact_in_pass", outputs_by_case["swap_exact_in_proof_gate_pass"][0]["o1"] & outputs_by_case["swap_range_guard_pass"][0]["o1"], 1),
            ("composed_swap_exact_in_fail_large_values", outputs_by_case["swap_exact_in_proof_gate_large_values_pass"][0]["o1"] & outputs_by_case["swap_range_guard_fail_large_values"][0]["o1"], 0),
            ("composed_swap_exact_out_pass", outputs_by_case["swap_exact_out_proof_gate_pass"][0]["o1"] & outputs_by_case["swap_range_guard_pass_exact_out"][0]["o1"], 1),
            ("composed_swap_exact_out_fail_large_values", outputs_by_case["swap_exact_out_proof_gate_large_values_pass"][0]["o1"] & outputs_by_case["swap_range_guard_fail_large_values_exact_out"][0]["o1"], 0),
            ("composed_settlement_pass", outputs_by_case["settlement_price_rails_pass"][0]["o1"] & outputs_by_case["settlement_module_bundle_pass"][0]["o1"], 1),
            ("composed_settlement_fail_rebate", outputs_by_case["settlement_price_rails_pass"][0]["o1"] & outputs_by_case["settlement_module_bundle_fail_rebate_flag"][0]["o1"], 0),
        ]
        for case_id, got, expected in composed:
            if got != expected:
                failures.append(f"{case_id}: expected {expected} got {got}")

    assert not failures, "Tau optimization trace mismatches:\n" + "\n".join(f"- {e}" for e in failures)
