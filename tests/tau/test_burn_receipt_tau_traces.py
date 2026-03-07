from __future__ import annotations

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from src.integration.tau_trace_cases import production_tau_trace_cases


def test_burn_receipt_tau_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip('tau not found')

    burn_cases = [case for case in production_tau_trace_cases() if case.case_id.startswith('burn_receipt_')]
    assert burn_cases, 'expected burn receipt trace cases'

    failures: list[str] = []
    for case in burn_cases:
        try:
            outputs = run_tau_spec_steps(
                tau_bin=tau_bin,
                spec_path=case.spec.path,
                steps=case.steps,
                timeout_s=float(case.timeout_s),
            )
        except Exception as exc:  # pragma: no cover - fail with detail instead
            failures.append(f"{case.case_id}: tau run failed: {type(exc).__name__}: {exc}")
            continue

        for idx, exp_step in enumerate(case.expected):
            got = outputs.get(idx, {})
            for name, exp_val in exp_step.items():
                if got.get(name) != exp_val:
                    failures.append(f"{case.case_id}: {name}[{idx}] expected {exp_val} got {got.get(name)}")

    assert not failures, 'Burn receipt Tau trace mismatches:\n' + '\n'.join(f'- {e}' for e in failures)
