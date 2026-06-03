#!/usr/bin/env python3
"""Lint machine-readable semantic contracts for Tau specs."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONTRACT_PATH = ROOT / "src" / "tau_specs" / "recommended" / "semantic_contracts.json"
SCHEMA = "zenodex/tau-semantic-contracts/v1"
ALLOWED_STYLES = {"host_projected_boolean_gate", "native_tau_guard"}
ALLOWED_RUN_MODES = {"repl", "spec"}
ALLOWED_EXECUTION_LANES = {"repl_with_spec_fallback", "spec_mode_stable"}


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _extract_slots(spec_text: str, prefix: str) -> set[str]:
    return {f"{prefix}{match}" for match in re.findall(rf"\b{re.escape(prefix)}(\d+)\[", spec_text)}


def _extract_slot_types(spec_text: str, prefix: str) -> dict[str, set[str]]:
    out: dict[str, set[str]] = {}
    for slot_num, ty in re.findall(rf"\b({re.escape(prefix)}\d+)\[t\]:([A-Za-z0-9_\[\]]+)", spec_text):
        out.setdefault(slot_num, set()).add(ty)
    return out


def _read_slot_defs(items: Any, *, name: str) -> tuple[list[Mapping[str, Any]], list[str]]:
    errors: list[str] = []
    if not isinstance(items, list):
        return [], [f"{name} must be a list"]
    rows: list[Mapping[str, Any]] = []
    seen: set[str] = set()
    for idx, item in enumerate(items):
        if not isinstance(item, Mapping):
            errors.append(f"{name}[{idx}] must be an object")
            continue
        slot = str(item.get("slot", "")).strip()
        atom_name = str(item.get("name", "")).strip()
        meaning = str(item.get("meaning", "")).strip()
        if not slot:
            errors.append(f"{name}[{idx}] missing slot")
        if not atom_name:
            errors.append(f"{name}[{idx}] missing name")
        if not meaning:
            errors.append(f"{name}[{idx}] missing meaning")
        if slot:
            if slot in seen:
                errors.append(f"{name} duplicate slot {slot}")
            seen.add(slot)
        rows.append(item)
    return rows, errors


def _read_runtime_defaults(obj: Mapping[str, Any]) -> tuple[dict[str, Mapping[str, Any]], list[str]]:
    raw = obj.get("runtime_defaults")
    if not isinstance(raw, Mapping):
        return {}, ["runtime_defaults must be an object"]

    defaults: dict[str, Mapping[str, Any]] = {}
    errors: list[str] = []
    for run_mode in sorted(ALLOWED_RUN_MODES):
        value = raw.get(run_mode)
        if not isinstance(value, Mapping):
            errors.append(f"runtime_defaults.{run_mode} must be an object")
            continue
        defaults[run_mode] = value
    return defaults, errors


def _runtime_contract_from_spec(
    spec: Mapping[str, Any],
    *,
    defaults: Mapping[str, Mapping[str, Any]],
    run_mode: str,
) -> tuple[Mapping[str, Any], list[str]]:
    errors: list[str] = []
    base = defaults.get(run_mode)
    if not isinstance(base, Mapping):
        return {}, [f"missing runtime_defaults entry for run_mode {run_mode!r}"]

    override = spec.get("runtime_contract")
    merged: dict[str, Any] = dict(base)
    if override is not None:
        if not isinstance(override, Mapping):
            return {}, [f"runtime_contract must be an object when present"]
        merged.update(override)
    return merged, errors


def validate_runtime_contract(
    contract_id: str,
    *,
    run_mode: str,
    runtime_contract: Mapping[str, Any],
) -> list[str]:
    errors: list[str] = []
    lane = str(runtime_contract.get("execution_lane", "")).strip()
    if lane not in ALLOWED_EXECUTION_LANES:
        errors.append(f"{contract_id}: invalid execution_lane {lane!r}")
    if run_mode == "spec" and lane != "spec_mode_stable":
        errors.append(f"{contract_id}: spec run_mode must use execution_lane 'spec_mode_stable'")
    if run_mode == "repl" and lane == "spec_mode_stable":
        errors.append(f"{contract_id}: repl run_mode must not use execution_lane 'spec_mode_stable'")

    timeout_raw = runtime_contract.get("trace_timeout_s")
    if not isinstance(timeout_raw, (int, float)) or isinstance(timeout_raw, bool) or float(timeout_raw) <= 0.0:
        errors.append(f"{contract_id}: trace_timeout_s must be a positive number")

    notes = runtime_contract.get("notes")
    if notes is not None:
        if not isinstance(notes, list) or not all(isinstance(item, str) and item.strip() for item in notes):
            errors.append(f"{contract_id}: runtime_contract.notes must be a list of non-empty strings")
    return errors


def runtime_contract_for_spec(
    spec: Mapping[str, Any],
    *,
    defaults: Mapping[str, Mapping[str, Any]],
) -> Mapping[str, Any]:
    run_mode = str(spec.get("run_mode", "")).strip()
    runtime_contract, errors = _runtime_contract_from_spec(spec, defaults=defaults, run_mode=run_mode)
    if errors:
        raise ValueError("; ".join(errors))
    return runtime_contract


def _lint_case(
    case: Mapping[str, Any],
    *,
    section_name: str,
    clause_id: str,
    output_slots: set[str],
) -> list[str]:
    errors: list[str] = []
    case_id = str(case.get("id", "")).strip()
    if not case_id:
        errors.append(f"{section_name}.{clause_id}: case missing id")
    steps = case.get("steps")
    expected = case.get("expected")
    if not isinstance(steps, list) or not steps:
        errors.append(f"{section_name}.{clause_id}.{case_id or '<missing>'}: steps must be a non-empty list")
        return errors
    if not isinstance(expected, list) or len(expected) != len(steps):
        errors.append(f"{section_name}.{clause_id}.{case_id or '<missing>'}: expected must be a list matching steps length")
        return errors
    for idx, step in enumerate(steps):
        if not isinstance(step, Mapping):
            errors.append(f"{section_name}.{clause_id}.{case_id or '<missing>'}: step {idx} must be an object")
    for idx, exp in enumerate(expected):
        if not isinstance(exp, Mapping):
            errors.append(f"{section_name}.{clause_id}.{case_id or '<missing>'}: expected[{idx}] must be an object")
            continue
        unknown = sorted(set(str(k) for k in exp.keys()) - output_slots)
        if unknown:
            errors.append(
                f"{section_name}.{clause_id}.{case_id or '<missing>'}: expected[{idx}] references unknown outputs {unknown}"
            )
    return errors


def lint_semantic_contracts(path: Path = DEFAULT_CONTRACT_PATH) -> list[str]:
    obj = _require_mapping(_load_json(path), name="contracts")
    errors: list[str] = []
    if obj.get("schema") != SCHEMA:
        errors.append(f"unexpected schema: {obj.get('schema')!r}")
    runtime_defaults, runtime_default_errors = _read_runtime_defaults(obj)
    errors.extend(runtime_default_errors)
    specs = obj.get("specs")
    if not isinstance(specs, list) or not specs:
        errors.append("specs must be a non-empty list")
        return errors

    seen_contract_ids: set[str] = set()
    for idx, spec in enumerate(specs):
        if not isinstance(spec, Mapping):
            errors.append(f"specs[{idx}] must be an object")
            continue
        contract_id = str(spec.get("contract_id", "")).strip()
        if not contract_id:
            errors.append(f"specs[{idx}] missing contract_id")
            continue
        if contract_id in seen_contract_ids:
            errors.append(f"duplicate contract_id {contract_id}")
        seen_contract_ids.add(contract_id)

        run_mode = str(spec.get("run_mode", "")).strip()
        if run_mode not in ALLOWED_RUN_MODES:
            errors.append(f"{contract_id}: invalid run_mode {run_mode!r}")
        style = str(spec.get("style", "")).strip()
        if style not in ALLOWED_STYLES:
            errors.append(f"{contract_id}: invalid style {style!r}")
        runtime_contract, runtime_errors = _runtime_contract_from_spec(
            spec,
            defaults=runtime_defaults,
            run_mode=run_mode,
        )
        for err in runtime_errors:
            errors.append(f"{contract_id}: {err}")
        if runtime_contract:
            errors.extend(validate_runtime_contract(contract_id, run_mode=run_mode, runtime_contract=runtime_contract))

        spec_rel = str(spec.get("spec_path", "")).strip()
        if not spec_rel:
            errors.append(f"{contract_id}: missing spec_path")
            continue
        spec_path = (ROOT / spec_rel).resolve()
        if not spec_path.exists():
            errors.append(f"{contract_id}: spec path does not exist: {spec_rel}")
            continue
        spec_text = spec_path.read_text(encoding="utf-8")
        used_inputs = _extract_slots(spec_text, "i")
        used_outputs = _extract_slots(spec_text, "o")
        input_types = _extract_slot_types(spec_text, "i")

        control_inputs, control_errors = _read_slot_defs(spec.get("control_inputs"), name=f"{contract_id}.control_inputs")
        data_inputs, data_errors = _read_slot_defs(spec.get("data_inputs"), name=f"{contract_id}.data_inputs")
        outputs, output_errors = _read_slot_defs(spec.get("outputs"), name=f"{contract_id}.outputs")
        errors.extend(control_errors)
        errors.extend(data_errors)
        errors.extend(output_errors)

        contract_inputs = {str(row.get("slot", "")).strip() for row in control_inputs + data_inputs if str(row.get("slot", "")).strip()}
        contract_outputs = {str(row.get("slot", "")).strip() for row in outputs if str(row.get("slot", "")).strip()}
        if used_inputs != contract_inputs:
            errors.append(f"{contract_id}: contract input slots {sorted(contract_inputs)} != spec input slots {sorted(used_inputs)}")
        if used_outputs != contract_outputs:
            errors.append(f"{contract_id}: contract output slots {sorted(contract_outputs)} != spec output slots {sorted(used_outputs)}")

        assumptions = spec.get("assumptions")
        non_goals = spec.get("non_goals")
        if not isinstance(assumptions, list) or not assumptions:
            errors.append(f"{contract_id}: assumptions must be a non-empty list")
        if not isinstance(non_goals, list) or not non_goals:
            errors.append(f"{contract_id}: non_goals must be a non-empty list")

        if style == "host_projected_boolean_gate":
            if data_inputs:
                errors.append(f"{contract_id}: host_projected_boolean_gate must not declare data_inputs")
            for slot, ty_set in sorted(input_types.items()):
                if ty_set != {"sbf"}:
                    errors.append(f"{contract_id}: input {slot} must be sbf-only for host_projected_boolean_gate, got {sorted(ty_set)}")
        elif style == "native_tau_guard":
            if not data_inputs:
                errors.append(f"{contract_id}: native_tau_guard must declare data_inputs")

        for section_name in ("guarantees", "forbidden_behaviors"):
            section = spec.get(section_name)
            if not isinstance(section, list) or not section:
                errors.append(f"{contract_id}: {section_name} must be a non-empty list")
                continue
            seen_clause_ids: set[str] = set()
            for clause_idx, clause in enumerate(section):
                if not isinstance(clause, Mapping):
                    errors.append(f"{contract_id}: {section_name}[{clause_idx}] must be an object")
                    continue
                clause_id = str(clause.get("id", "")).strip()
                desc = str(clause.get("description", "")).strip()
                if not clause_id:
                    errors.append(f"{contract_id}: {section_name}[{clause_idx}] missing id")
                    continue
                if clause_id in seen_clause_ids:
                    errors.append(f"{contract_id}: duplicate {section_name} id {clause_id}")
                seen_clause_ids.add(clause_id)
                if not desc:
                    errors.append(f"{contract_id}: {section_name}.{clause_id} missing description")
                cases = clause.get("cases")
                if not isinstance(cases, list) or not cases:
                    errors.append(f"{contract_id}: {section_name}.{clause_id} must have at least one case")
                    continue
                for case in cases:
                    errors.extend(
                        _lint_case(
                            _require_mapping(case, name=f"{contract_id}.{section_name}.{clause_id}.case"),
                            section_name=f"{contract_id}.{section_name}",
                            clause_id=clause_id,
                            output_slots=used_outputs,
                        )
                    )

    smoke_ids = obj.get("runtime_smoke_contract_ids")
    if not isinstance(smoke_ids, list) or not smoke_ids or not all(isinstance(item, str) and item.strip() for item in smoke_ids):
        errors.append("runtime_smoke_contract_ids must be a non-empty list of non-empty strings")
    else:
        for contract_id in smoke_ids:
            if contract_id not in seen_contract_ids:
                errors.append(f"runtime_smoke_contract_ids references unknown contract_id {contract_id!r}")
    return errors


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--contracts",
        default=str(DEFAULT_CONTRACT_PATH),
        help="Path to semantic_contracts.json",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    errors = lint_semantic_contracts(Path(args.contracts).expanduser().resolve())
    if errors:
        sys.stderr.write("Tau semantic contract lint failed:\n")
        for err in errors:
            sys.stderr.write(f"- {err}\n")
        return 1
    sys.stdout.write("ok\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
