# [TESTER] v1

from __future__ import annotations

import os

import pytest

from src.integration.tau_runner import TauRunError, find_tau_bin, run_tau_spec_steps_spec_mode, run_tau_spec_steps_with_trace
from src.integration.tau_trace_cases import production_tau_trace_cases


def test_production_tau_traces() -> None:
    """
    Slow: runs real Tau on a curated set of production specs with hand-checked traces.

    Enable with:
      TAU_PROD_TRACE_TESTS=1 pytest -q tests/tau/test_production_tau_traces.py
    """
    if os.environ.get("TAU_PROD_TRACE_TESTS") != "1":
        pytest.skip("set TAU_PROD_TRACE_TESTS=1 to run production Tau trace tests")

    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    failures: list[str] = []
    for case in production_tau_trace_cases():
        try:
            if case.mode == "spec":
                outputs = run_tau_spec_steps_spec_mode(
                    tau_bin=tau_bin,
                    spec_path=case.spec.path,
                    steps=case.steps,
                    timeout_s=float(case.timeout_s),
                    severity="error",
                )
            elif case.mode == "repl":
                outputs, _, _, _ = run_tau_spec_steps_with_trace(
                    tau_bin=tau_bin,
                    spec_path=case.spec.path,
                    steps=case.steps,
                    timeout_s=float(case.timeout_s),
                    severity="error",
                    inline_defs=case.inline_defs,
                    experimental=case.experimental,
                )
            else:
                raise ValueError(f"unknown Tau trace case mode: {case.mode!r}")
        except TauRunError as exc:
            failures.append(f"{case.case_id}: Tau failed: {exc}")
            continue
        except Exception as exc:
            failures.append(f"{case.case_id}: runner error: {type(exc).__name__}: {exc}")
            continue

        for idx, exp_step in enumerate(case.expected):
            got = outputs.get(idx, {})
            for name, exp_val in exp_step.items():
                if got.get(name) != exp_val:
                    failures.append(f"{case.case_id}: {name}[{idx}] expected {exp_val} got {got.get(name)}")

    assert not failures, "Production Tau trace mismatches:\n" + "\n".join(f"- {e}" for e in failures)
