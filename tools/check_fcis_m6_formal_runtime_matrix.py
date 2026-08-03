#!/usr/bin/env python3
"""Fail-closed consistency gate for the M6 formal/runtime obligation matrix."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

import yaml

PROJECTION_ID = re.compile(r"^(?:derive|project)_[a-z0-9_]+_v1$")


def check(root: Path) -> dict[str, Any]:
    suite = json.loads(
        (root / "formal/esso/fcis_m6_formal_suite_v1.json").read_text(encoding="utf-8")
    )
    matrix = json.loads(
        (root / "docs/research/FCIS_M6_FORMAL_RUNTIME_REFINEMENT_MATRIX_V1.json").read_text(
            encoding="utf-8"
        )
    )
    result = json.loads((root / matrix["bounded_result"]).read_text(encoding="utf-8"))
    feature = (root / matrix["feature_file"]).read_text(encoding="utf-8")
    errors: list[str] = []

    entries = matrix.get("entries", [])
    by_id = {entry["model_id"]: entry for entry in entries}
    if len(by_id) != len(entries):
        errors.append("duplicate matrix model id")

    suite_ids: list[str] = []
    used_projections: set[str] = set()
    for item in suite["models"]:
        model = yaml.safe_load((root / item["path"]).read_text(encoding="utf-8"))
        model_id = model["meta"]["model_id"]
        suite_ids.append(model_id)
        entry = by_id.get(model_id)
        if entry is None:
            errors.append(f"missing matrix entry {model_id}")
            continue

        actions = [action["id"] for action in model["actions"]]
        invariants = [invariant["id"] for invariant in model["invariants"]]
        if entry["model_path"] != item["path"]:
            errors.append(f"{model_id}: model path drift")
        if entry["principal_role"] != item["role"]:
            errors.append(f"{model_id}: principal role drift")
        if entry["formal_actions"] != actions:
            errors.append(f"{model_id}: action registry drift")
        if entry["formal_invariants"] != invariants:
            errors.append(f"{model_id}: invariant registry drift")
        if set(entry["action_to_scenario"]) != set(actions):
            errors.append(f"{model_id}: incomplete action-to-scenario map")
        if any(
            entry["action_to_scenario"].get(action) != entry["scenario_tag"] for action in actions
        ):
            errors.append(f"{model_id}: crossed scenario mapping")
        if entry["scenario_tag"] not in feature:
            errors.append(f"{model_id}: scenario tag absent from feature file")

        projections = entry.get("runtime_projection", [])
        if not projections:
            errors.append(f"{model_id}: no runtime projection obligation")
        if len(projections) != len(set(projections)):
            errors.append(f"{model_id}: duplicate runtime projection obligation")
        for projection in projections:
            if not isinstance(projection, str) or PROJECTION_ID.fullmatch(projection) is None:
                errors.append(f"{model_id}: malformed projection id {projection!r}")
            else:
                used_projections.add(projection)
        if entry["runtime_status"] != "SPEC_ONLY_UNMOUNTED":
            errors.append(
                f"{model_id}: unsupported runtime promotion claim {entry['runtime_status']}"
            )

    if len(suite_ids) != len(set(suite_ids)):
        errors.append("duplicate suite model id")
    if set(by_id) != set(suite_ids):
        errors.append("matrix/suite model set differs")
    if matrix["composition_obligation"]["premises"] != suite_ids:
        errors.append("composition premise order differs from the formal suite")

    projection_contract = matrix.get("projection_contract", {})
    if projection_contract.get("status") != "DECLARED_ONLY_NO_RUNTIME_IMPLEMENTATION":
        errors.append("projection contract must remain explicitly unimplemented")
    registered = projection_contract.get("registered_ids", [])
    if registered != sorted(set(registered)):
        errors.append("runtime projection registry must be unique and sorted")
    if set(registered) != used_projections:
        errors.append("runtime projection registry differs from matrix use")

    if set(result.get("models", {})) != set(suite_ids):
        errors.append("bounded result model set differs from suite")
    if result["verdict"] != "PASS_BOUNDED_INDEPENDENT_REPLAY":
        errors.append("bounded formal replay is not green")
    if result["mutants_killed"] != result["mutants_total"]:
        errors.append("not all formal mutants are killed")
    if matrix["composition_obligation"]["status"] != "THEOREM_STATEMENT_FROZEN_PROOF_OPEN":
        errors.append("composition theorem must not be promoted by this packet")

    verdict = "FORMAL_RUNTIME_MATRIX_MATCH" if not errors else "FORMAL_RUNTIME_MATRIX_MISMATCH"
    return {
        "verdict": verdict,
        "models": len(suite_ids),
        "actions": sum(len(entry["formal_actions"]) for entry in entries),
        "invariants": sum(len(entry["formal_invariants"]) for entry in entries),
        "registered_projection_obligations": len(registered),
        "projection_contract_status": projection_contract.get("status"),
        "errors": errors,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    report = check(args.root)
    print(json.dumps(report, indent=2))
    return 0 if report["verdict"] == "FORMAL_RUNTIME_MATRIX_MATCH" else 1


if __name__ == "__main__":
    raise SystemExit(main())
