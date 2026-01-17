# [TESTER] v1

from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from src.integration.tau_runner import run_tau_spec_steps_spec_mode


ROOT = Path(__file__).resolve().parents[2]
REGISTRY = ROOT / "tests" / "tau" / "spec_registry.json"


def test_tau_spec_registry_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    data = json.loads(REGISTRY.read_text(encoding="utf-8"))
    specs = data.get("specs", [])
    assert isinstance(specs, list) and specs, "spec_registry.json has no specs"

    failures: list[str] = []
    for entry in specs:
        if entry.get("mode") == "skip":
            continue
        spec_id = entry.get("id")
        rel_path = entry.get("path")
        if not isinstance(spec_id, str) or not spec_id:
            failures.append("registry entry missing id")
            continue
        if not isinstance(rel_path, str) or not rel_path:
            failures.append(f"{spec_id}: registry entry missing path")
            continue

        spec_path = ROOT / rel_path
        if not spec_path.exists():
            failures.append(f"{spec_id}: spec not found at {rel_path}")
            continue

        inputs = entry.get("inputs")
        expected = entry.get("expected")
        if not isinstance(inputs, list) or not isinstance(expected, list):
            failures.append(f"{spec_id}: inputs/expected must be lists")
            continue
        if len(inputs) != len(expected):
            failures.append(f"{spec_id}: inputs length {len(inputs)} != expected length {len(expected)}")
            continue
        if not inputs:
            failures.append(f"{spec_id}: empty trace")
            continue

        mode = entry.get("mode", "repl")
        try:
            if mode == "spec":
                outputs = run_tau_spec_steps_spec_mode(
                    tau_bin=tau_bin,
                    spec_path=spec_path,
                    steps=[dict(step) for step in inputs],
                    timeout_s=float(entry.get("spec_timeout", 60.0)),
                )
            else:
                outputs = run_tau_spec_steps(
                    tau_bin=tau_bin,
                    spec_path=spec_path,
                    steps=[dict(step) for step in inputs],
                    timeout_s=float(entry.get("timeout_s", 60.0)),
                )
        except Exception as exc:
            failures.append(f"{spec_id}: tau run failed: {type(exc).__name__}: {exc}")
            continue

        for idx, exp_step in enumerate(expected):
            if not isinstance(exp_step, dict):
                failures.append(f"{spec_id}: expected[{idx}] must be an object")
                continue
            got = outputs.get(idx, {})
            for out_name, exp_val in exp_step.items():
                if got.get(out_name) != exp_val:
                    failures.append(
                        f"{spec_id}: {out_name} step {idx} expected {exp_val} got {got.get(out_name)}"
                    )

    assert not failures, "Tau trace mismatches:\n" + "\n".join(f"- {e}" for e in failures)
