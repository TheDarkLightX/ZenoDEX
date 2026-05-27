#!/usr/bin/env python3
"""Lint host-projected fact contracts for runtime-facing Tau specs."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONTRACT_PATH = ROOT / "src" / "tau_specs" / "recommended" / "host_projection_contracts.json"
SCHEMA = "zenodex/tau-host-projection-contracts/v1"
ALLOWED_BUG_CLASSES = {
    "config_or_release",
    "external_process",
    "filesystem_or_path",
    "governance_reset",
    "network_or_peer",
    "oracle_or_time",
    "replay_or_idempotency",
    "serialization_or_canonicalization",
    "wallet_boundary",
}


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _extract_input_slots(spec_text: str) -> set[str]:
    return {f"i{match}" for match in re.findall(r"\bi(\d+)\[t\]", spec_text)}


def _extract_input_slot_names_from_comments(spec_text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in spec_text.splitlines():
        match = re.match(r"\s*#\s*(i\d+)\s*=\s*([A-Za-z0-9_]+)", line)
        if match:
            out[match.group(1)] = match.group(2)
    return out


def _nonempty_str(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _nonempty_str_list(value: Any) -> bool:
    return isinstance(value, list) and bool(value) and all(_nonempty_str(item) for item in value)


def lint_host_projection_contracts(path: Path = DEFAULT_CONTRACT_PATH) -> list[str]:
    obj = _require_mapping(_load_json(path), name="host projection contracts")
    errors: list[str] = []
    if obj.get("schema") != SCHEMA:
        errors.append(f"unexpected schema: {obj.get('schema')!r}")

    specs = obj.get("specs")
    if not isinstance(specs, list) or not specs:
        errors.append("specs must be a non-empty list")
        return errors

    seen_paths: set[str] = set()
    for idx, raw_spec in enumerate(specs):
        if not isinstance(raw_spec, Mapping):
            errors.append(f"specs[{idx}] must be an object")
            continue

        spec_rel = str(raw_spec.get("spec_path", "")).strip()
        if not spec_rel:
            errors.append(f"specs[{idx}] missing spec_path")
            continue
        if spec_rel in seen_paths:
            errors.append(f"{spec_rel}: duplicate spec_path")
        seen_paths.add(spec_rel)

        spec_path = (ROOT / spec_rel).resolve()
        try:
            spec_path.relative_to(ROOT)
        except ValueError:
            errors.append(f"{spec_rel}: spec_path escapes repository root")
            continue
        if not spec_path.exists():
            errors.append(f"{spec_rel}: spec file does not exist")
            continue

        boundary = raw_spec.get("boundary")
        if not _nonempty_str(boundary):
            errors.append(f"{spec_rel}: boundary must be a non-empty string")

        default_on_missing = raw_spec.get("default_on_missing_fact")
        if default_on_missing != 0:
            errors.append(f"{spec_rel}: default_on_missing_fact must be 0")

        contracts = raw_spec.get("host_fact_contracts")
        if not isinstance(contracts, Mapping) or not contracts:
            errors.append(f"{spec_rel}: host_fact_contracts must be a non-empty object")
            continue

        spec_text = spec_path.read_text(encoding="utf-8")
        actual_slots = _extract_input_slots(spec_text)
        comment_names = _extract_input_slot_names_from_comments(spec_text)
        declared_slots = {str(slot).strip() for slot in contracts.keys()}

        missing = sorted(actual_slots - declared_slots)
        extra = sorted(declared_slots - actual_slots)
        if missing:
            errors.append(f"{spec_rel}: missing host fact contracts for {missing}")
        if extra:
            errors.append(f"{spec_rel}: host fact contracts reference unknown slots {extra}")

        for slot in sorted(declared_slots):
            value = contracts.get(slot)
            if not isinstance(value, Mapping):
                errors.append(f"{spec_rel}.{slot}: contract must be an object")
                continue

            name = value.get("name")
            if not _nonempty_str(name):
                errors.append(f"{spec_rel}.{slot}: name must be a non-empty string")
            expected_name = comment_names.get(slot)
            if expected_name and _nonempty_str(name) and str(name).strip() != expected_name:
                errors.append(f"{spec_rel}.{slot}: name {name!r} does not match spec comment {expected_name!r}")

            if value.get("fail_closed_default") != 0:
                errors.append(f"{spec_rel}.{slot}: fail_closed_default must be 0")

            bug_class = str(value.get("runtime_bug_class", "")).strip()
            if bug_class not in ALLOWED_BUG_CLASSES:
                errors.append(f"{spec_rel}.{slot}: invalid runtime_bug_class {bug_class!r}")

            if not _nonempty_str(value.get("producer_surface")):
                errors.append(f"{spec_rel}.{slot}: producer_surface must be a non-empty string")
            if not _nonempty_str_list(value.get("evidence_required")):
                errors.append(f"{spec_rel}.{slot}: evidence_required must be a non-empty string list")
            if not _nonempty_str_list(value.get("negative_tests")):
                errors.append(f"{spec_rel}.{slot}: negative_tests must be a non-empty string list")

    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contracts", default=str(DEFAULT_CONTRACT_PATH), help="Path to host_projection_contracts.json")
    args = parser.parse_args(argv)

    errors = lint_host_projection_contracts(Path(args.contracts).expanduser().resolve())
    if errors:
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        return 1
    print("Tau host projection contracts OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
