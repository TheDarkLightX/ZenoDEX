#!/usr/bin/env python3
"""Replay the declared supported Tau runtime subset."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps, run_tau_spec_steps_spec_mode  # noqa: E402
from tools.tau_semantic_contract_lint import DEFAULT_CONTRACT_PATH, runtime_contract_for_spec  # noqa: E402


def _load_contracts(path: Path = DEFAULT_CONTRACT_PATH) -> Mapping[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError("semantic contracts must be a JSON object")
    return raw


def supported_runtime_subset_status(root: Path = ROOT) -> dict[str, Any]:
    path = root / "tools" / "check_tau_supported_runtime_subset.py"
    tau_bin = find_tau_bin(root)
    return {
        "ok": bool(tau_bin),
        "path": str(path.relative_to(root)),
        "error": None if tau_bin else "tau binary not found",
    }


def build_supported_runtime_subset_report(
    *,
    root: Path = ROOT,
    tau_bin: str | None = None,
    contracts: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    chosen_tau_bin = tau_bin or find_tau_bin(root)
    if not chosen_tau_bin:
        return {
            "schema": "zenodex/tau-supported-runtime-subset-report/v1",
            "ok": False,
            "tau_bin": "",
            "results": [],
            "errors": ["tau binary not found"],
        }

    contract_blob = contracts if contracts is not None else _load_contracts()
    runtime_defaults = contract_blob.get("runtime_defaults", {})
    specs = contract_blob.get("specs", [])
    smoke_ids = contract_blob.get("runtime_smoke_contract_ids", [])
    if not isinstance(specs, list) or not isinstance(smoke_ids, list):
        raise ValueError("semantic contracts missing specs/runtime_smoke_contract_ids")

    by_id = {
        str(spec.get("contract_id", "")).strip(): spec
        for spec in specs
        if isinstance(spec, Mapping) and str(spec.get("contract_id", "")).strip()
    }

    results: list[dict[str, Any]] = []
    errors: list[str] = []
    for contract_id in smoke_ids:
        spec = by_id.get(str(contract_id))
        if not isinstance(spec, Mapping):
            errors.append(f"{contract_id}: missing contract entry")
            continue
        runtime_contract = runtime_contract_for_spec(spec, defaults=runtime_defaults)
        run_mode = str(spec.get("run_mode", "repl")).strip()
        spec_path = root / str(spec.get("spec_path", "")).strip()
        batched_steps, case_runs = _batched_cases(spec)
        if not batched_steps:
            errors.append(f"{contract_id}: no executable cases")
            continue

        try:
            if run_mode == "spec":
                outputs = run_tau_spec_steps_spec_mode(
                    tau_bin=chosen_tau_bin,
                    spec_path=spec_path,
                    steps=batched_steps,
                    timeout_s=float(runtime_contract.get("trace_timeout_s", 90.0)),
                )
            else:
                outputs = run_tau_spec_steps(
                    tau_bin=chosen_tau_bin,
                    spec_path=spec_path,
                    steps=batched_steps,
                    timeout_s=float(runtime_contract.get("trace_timeout_s", 90.0)),
                )
        except Exception as exc:
            errors.append(f"{contract_id}: tau run failed: {type(exc).__name__}: {exc}")
            continue

        local_errors: list[str] = []
        for case_label, start_idx, expected in case_runs:
            for rel_idx, exp in enumerate(expected):
                if not isinstance(exp, Mapping):
                    local_errors.append(f"{case_label}: expected[{rel_idx}] must be an object")
                    continue
                got = outputs.get(start_idx + rel_idx, {})
                for out_name, exp_val in exp.items():
                    if got.get(out_name) != exp_val:
                        local_errors.append(
                            f"{case_label}: {out_name} step {rel_idx} expected {exp_val} got {got.get(out_name)}"
                        )
        if local_errors:
            errors.extend(f"{contract_id}: {row}" for row in local_errors)
            continue

        results.append(
            {
                "contract_id": contract_id,
                "run_mode": run_mode,
                "style": str(spec.get("style", "")).strip(),
                "execution_lane": str(runtime_contract.get("execution_lane", "")).strip(),
                "trace_timeout_s": float(runtime_contract.get("trace_timeout_s", 90.0)),
            }
        )

    return {
        "schema": "zenodex/tau-supported-runtime-subset-report/v1",
        "ok": not errors,
        "tau_bin": str(chosen_tau_bin),
        "results": results,
        "errors": errors,
    }


def _batched_cases(spec: Mapping[str, Any]) -> tuple[list[dict[str, Any]], list[tuple[str, int, list[Mapping[str, Any]]]]]:
    batched_steps: list[dict[str, Any]] = []
    case_runs: list[tuple[str, int, list[Mapping[str, Any]]]] = []
    for section_name in ("guarantees", "forbidden_behaviors"):
        section = spec.get(section_name, [])
        if not isinstance(section, list):
            continue
        for clause in section:
            if not isinstance(clause, Mapping):
                continue
            clause_id = str(clause.get("id", "")).strip() or "<missing>"
            cases = clause.get("cases", [])
            if not isinstance(cases, list):
                continue
            for case in cases:
                if not isinstance(case, Mapping):
                    continue
                case_id = str(case.get("id", "")).strip() or "<missing>"
                steps = case.get("steps", [])
                expected = case.get("expected", [])
                if not isinstance(steps, list) or not isinstance(expected, list) or len(steps) != len(expected):
                    raise ValueError(f"malformed steps/expected for {section_name}.{clause_id}.{case_id}")
                start_idx = len(batched_steps)
                batched_steps.extend(dict(step) for step in steps if isinstance(step, Mapping))
                case_runs.append((f"{section_name}.{clause_id}.{case_id}", start_idx, list(expected)))
    return batched_steps, case_runs


def main() -> int:
    report = build_supported_runtime_subset_report()
    if report["tau_bin"] == "":
        print("error: tau binary not found", file=sys.stderr)
        return 2

    for row in report["results"]:
        print(
            "PASS",
            row["contract_id"],
            row["run_mode"],
            row["style"],
            row["execution_lane"],
            row["trace_timeout_s"],
        )

    if report["errors"]:
        print("Tau supported runtime subset failed:", file=sys.stderr)
        for row in report["errors"]:
            print(f"- {row}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
