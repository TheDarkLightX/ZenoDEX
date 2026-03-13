#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin
from src.integration.tau_spec_assurance import ROOT, collect_assurance_entry_cases, safe_eval
from tools.check_tau_formal_plan import DEFAULT_PLAN, validate_tau_formal_plan


DEFAULT_REGISTRY = ROOT / "tests" / "tau" / "spec_assurance_registry.json"
DEFAULT_CONTRACTS_DIR = ROOT / "formal" / "tau" / "contracts"
DEFAULT_ATLASES_DIR = ROOT / "formal" / "tau" / "atlases"
CHECK_STATUSES = {"active", "promoted"}


@dataclass(frozen=True)
class TauFormalContractsResult:
    errors: list[str]
    checked_specs: list[str]
    tau_checked_specs: list[str]


def _load_json(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError(f"{path}: expected JSON object")
    return raw


def _load_registry(path: Path) -> dict[str, dict[str, Any]]:
    raw = _load_json(path)
    specs = raw.get("specs", [])
    if not isinstance(specs, list):
        raise ValueError(f"{path}: specs must be a list")
    out: dict[str, dict[str, Any]] = {}
    for entry in specs:
        if not isinstance(entry, dict):
            raise ValueError(f"{path}: spec entries must be objects")
        spec_id = str(entry.get("id", "")).strip()
        if not spec_id:
            raise ValueError(f"{path}: spec entry missing id")
        out[spec_id] = entry
    return out


def _sort_output_name(name: str) -> tuple[int, str]:
    suffix = name[1:]
    if suffix.isdigit():
        return int(suffix), name
    return 10**9, name


def _load_contract_output_exprs(contract: Mapping[str, Any]) -> dict[str, str]:
    outputs = contract.get("outputs", [])
    if not isinstance(outputs, list) or not outputs:
        raise ValueError("contract outputs must be a non-empty list")
    exprs: dict[str, str] = {}
    for output in outputs:
        if not isinstance(output, Mapping):
            raise ValueError("contract output entries must be objects")
        name = str(output.get("name", "")).strip()
        expr = str(output.get("contract_expr", "")).strip()
        if not name or not expr:
            raise ValueError("contract outputs must define name and contract_expr")
        exprs[name] = expr
    return exprs


def _coerce_output_bit(value: object) -> int:
    if isinstance(value, bool):
        return 1 if value else 0
    if isinstance(value, int):
        return int(value)
    raise ValueError(f"expected bool/int output, got {value!r}")


def _evaluate_contract_vector(
    *,
    inputs: Mapping[str, int],
    output_exprs: Mapping[str, str],
    output_order: list[str],
) -> dict[str, int]:
    context = {name: int(value) for name, value in inputs.items()}
    out: dict[str, int] = {}
    for name in output_order:
        out[name] = _coerce_output_bit(safe_eval(output_exprs[name], context))
    return out


def _vector_tuple(vector: Mapping[str, int], output_order: list[str]) -> tuple[int, ...]:
    return tuple(int(vector[name]) for name in output_order)


def _vector_id(vector: Mapping[str, int], output_order: list[str]) -> str:
    return "".join(str(int(vector[name])) for name in output_order)


def _vector_formula(vector: Mapping[str, int], output_order: list[str]) -> str:
    return " && ".join(f"{name}={int(vector[name])}" for name in output_order)


def _theorem_kinds(contract: Mapping[str, Any]) -> set[str]:
    theorem_rows = contract.get("theorems", [])
    if not isinstance(theorem_rows, list):
        return set()
    kinds: set[str] = set()
    for row in theorem_rows:
        if not isinstance(row, Mapping):
            continue
        kind = str(row.get("kind", "")).strip()
        if kind:
            kinds.add(kind)
    return kinds


def _required_artifacts(profile: Mapping[str, Any]) -> set[str]:
    values = profile.get("required_artifacts", [])
    if not isinstance(values, list):
        return set()
    return {str(value).strip() for value in values if str(value).strip()}


def validate_tau_formal_contract_artifacts(
    *,
    plan_path: Path = DEFAULT_PLAN,
    registry_path: Path = DEFAULT_REGISTRY,
    contracts_dir: Path = DEFAULT_CONTRACTS_DIR,
    atlases_dir: Path = DEFAULT_ATLASES_DIR,
    tau_bin: str | None = None,
) -> TauFormalContractsResult:
    errors: list[str] = []
    checked_specs: list[str] = []
    tau_checked_specs: list[str] = []

    plan_result = validate_tau_formal_plan(plan_path)
    errors.extend(plan_result.errors)
    if plan_result.errors:
        return TauFormalContractsResult(errors=errors, checked_specs=checked_specs, tau_checked_specs=tau_checked_specs)

    plan = _load_json(plan_path)
    profiles_by_id = {
        str(profile.get("id", "")).strip(): profile
        for profile in plan.get("profiles", [])
        if isinstance(profile, Mapping)
    }
    registry = _load_registry(registry_path)

    contract_paths = sorted(contracts_dir.glob("*.contract.json"))
    if not contract_paths:
        errors.append(f"{contracts_dir}: no formal contract artifacts found")
        return TauFormalContractsResult(errors=errors, checked_specs=checked_specs, tau_checked_specs=tau_checked_specs)

    seen_specs: set[str] = set()
    for contract_path in contract_paths:
        contract = _load_json(contract_path)
        spec_id = str(contract.get("spec_id", "")).strip()
        if not spec_id:
            errors.append(f"{contract_path}: missing spec_id")
            continue
        if spec_id in seen_specs:
            errors.append(f"{contract_path}: duplicate formal contract for spec {spec_id}")
            continue
        seen_specs.add(spec_id)

        contract_status = str(contract.get("contract_status", "")).strip()
        if contract_status not in CHECK_STATUSES:
            # Only enforce active/promoted contracts; drafts are scaffolding.
            continue

        scoped_error_count = len(errors)
        spec_path_rel = str(contract.get("spec_path", "")).strip()
        if not spec_path_rel:
            errors.append(f"{contract_path}: missing spec_path")
            continue
        spec_path = ROOT / spec_path_rel
        if not spec_path.exists():
            errors.append(f"{contract_path}: missing spec file {spec_path_rel}")
            continue

        spec_root_rel = Path(str(plan["root"]))
        try:
            assigned_key = Path(spec_path_rel).relative_to(spec_root_rel).as_posix()
        except ValueError:
            errors.append(f"{contract_path}: spec_path {spec_path_rel} not under plan root {spec_root_rel}")
            continue
        assigned = plan_result.assignments.get(assigned_key)
        if assigned is None:
            errors.append(f"{contract_path}: spec {spec_id} is not assigned to a proof profile")
            continue
        profile_id = assigned["profile"]
        profile = profiles_by_id.get(profile_id, {})

        theorem_kinds = _theorem_kinds(contract)
        required_theorems = profile.get("required_theorems", [])
        if isinstance(required_theorems, list):
            for kind in required_theorems:
                if isinstance(kind, str) and kind not in theorem_kinds:
                    errors.append(f"{contract_path}: missing theorem kind {kind!r} required by profile {profile_id}")

        output_exprs = _load_contract_output_exprs(contract)
        output_order = sorted(output_exprs.keys(), key=_sort_output_name)

        atlas_path = atlases_dir / f"{spec_id}.atlas.json"
        if not atlas_path.exists():
            errors.append(f"{contract_path}: expected atlas file {atlas_path.relative_to(ROOT)}")
            continue
        atlas = _load_json(atlas_path)

        if atlas.get("spec_id") != spec_id:
            errors.append(f"{atlas_path}: spec_id mismatch for {spec_id}")
        if atlas.get("spec_path") != spec_path_rel:
            errors.append(f"{atlas_path}: spec_path mismatch for {spec_id}")
        if atlas.get("contract_ref") != contract_path.relative_to(ROOT).as_posix():
            errors.append(f"{atlas_path}: contract_ref mismatch for {spec_id}")

        proof_scope = str(contract.get("proof_scope", "")).strip()
        if str(atlas.get("proof_scope", "")).strip() != proof_scope:
            errors.append(f"{atlas_path}: proof_scope does not match contract for {spec_id}")
        if atlas.get("output_order") != output_order:
            errors.append(f"{atlas_path}: output_order does not match contract outputs for {spec_id}")

        if str(atlas.get("atlas_status", "")).strip() not in CHECK_STATUSES:
            errors.append(f"{atlas_path}: atlas_status must be active/promoted for active contract")

        partition_checks = atlas.get("partition_checks", {})
        if not isinstance(partition_checks, Mapping):
            errors.append(f"{atlas_path}: partition_checks must be an object")
        else:
            if partition_checks.get("disjointness") != "proved":
                errors.append(f"{atlas_path}: disjointness must be proved")
            if partition_checks.get("exhaustiveness") != "proved":
                errors.append(f"{atlas_path}: exhaustiveness must be proved")
            required_artifacts = _required_artifacts(profile)
            if "tau_differential_report" in required_artifacts:
                if partition_checks.get("tau_differential") != "proved":
                    errors.append(f"{atlas_path}: tau_differential must be proved for profile {profile_id}")
                if partition_checks.get("interpreter_equivalence") != "proved":
                    errors.append(f"{atlas_path}: interpreter_equivalence must be proved for profile {profile_id}")

        # Bounded-domain exactness replay is only available when an assurance registry
        # harness exists for the spec. Active bounded contracts must have that replay.
        entry = registry.get(spec_id)
        if proof_scope == "bounded_assurance_domain":
            if entry is None:
                errors.append(
                    f"{contract_path}: missing assurance registry entry for bounded contract {spec_id}"
                )
            else:
                mirror_report = collect_assurance_entry_cases(
                    tau_bin=None,
                    entry=entry,
                    root=ROOT,
                    oracle_outputs_override=output_exprs,
                    execution_backend_override="mirror_combinational",
                )
                mirror_mismatches = mirror_report.get("oracle_mismatches", [])
                if mirror_mismatches:
                    errors.append(
                        f"{spec_id}: contract and extracted Tau mirror disagree on {len(mirror_mismatches)} explicit-domain cases"
                    )

                case_details = mirror_report.get("case_details", [])
                if not isinstance(case_details, list):
                    errors.append(f"{spec_id}: mirror report missing case_details")
                else:
                    observed_vectors: set[tuple[int, ...]] = set()
                    case_inputs_by_vector: dict[tuple[int, ...], dict[str, int]] = {}
                    for case in case_details:
                        oracle_outputs = getattr(case, "oracle_outputs", None)
                        inputs = getattr(case, "inputs", None)
                        if not isinstance(oracle_outputs, Mapping) or not isinstance(inputs, Mapping):
                            errors.append(f"{spec_id}: malformed case detail entry")
                            continue
                        observed = _vector_tuple(oracle_outputs, output_order)
                        observed_vectors.add(observed)
                        case_inputs_by_vector.setdefault(
                            observed,
                            {str(k): int(v) for k, v in inputs.items()},
                        )

                    regions = atlas.get("regions", [])
                    if not isinstance(regions, list):
                        errors.append(f"{atlas_path}: regions must be a list")
                    else:
                        region_by_vector: dict[tuple[int, ...], Mapping[str, Any]] = {}
                        for region in regions:
                            if not isinstance(region, Mapping):
                                errors.append(f"{atlas_path}: region entries must be objects")
                                continue
                            output_vector = region.get("output_vector", {})
                            if not isinstance(output_vector, Mapping):
                                errors.append(f"{atlas_path}: region missing output_vector")
                                continue
                            if sorted(output_vector.keys(), key=_sort_output_name) != output_order:
                                errors.append(f"{atlas_path}: region output_vector keys do not match output_order")
                                continue
                            vector = _vector_tuple(output_vector, output_order)
                            if vector in region_by_vector:
                                errors.append(f"{atlas_path}: duplicate region for output vector {vector}")
                                continue
                            region_by_vector[vector] = region

                            expected_region_id = _vector_id(output_vector, output_order)
                            if region.get("region_id") != expected_region_id:
                                errors.append(f"{atlas_path}: region_id mismatch for vector {vector}")
                            expected_formula = _vector_formula(output_vector, output_order)
                            if region.get("region_formula") != expected_formula:
                                errors.append(f"{atlas_path}: region_formula mismatch for vector {vector}")

                            should_be_reachable = vector in observed_vectors
                            expected_status = "reachable" if should_be_reachable else "unreachable"
                            if region.get("reachability_status") != expected_status:
                                errors.append(
                                    f"{atlas_path}: vector {vector} marked {region.get('reachability_status')!r}, expected {expected_status!r}"
                                )

                            witness_inputs = region.get("witness_inputs")
                            if should_be_reachable:
                                if not isinstance(witness_inputs, Mapping):
                                    errors.append(f"{atlas_path}: reachable vector {vector} is missing witness_inputs")
                                else:
                                    witness_vector = _evaluate_contract_vector(
                                        inputs={str(k): int(v) for k, v in witness_inputs.items()},
                                        output_exprs=output_exprs,
                                        output_order=output_order,
                                    )
                                    if _vector_tuple(witness_vector, output_order) != vector:
                                        errors.append(f"{atlas_path}: witness_inputs do not reproduce vector {vector}")
                            else:
                                if witness_inputs is not None:
                                    errors.append(f"{atlas_path}: unreachable vector {vector} must not carry witness_inputs")

                        for vector in itertools.product([0, 1], repeat=len(output_order)):
                            if vector not in region_by_vector:
                                errors.append(f"{atlas_path}: missing region for output vector {vector}")
                                continue
                            if vector in observed_vectors:
                                sample_inputs = case_inputs_by_vector[vector]
                                sample_vector = _evaluate_contract_vector(
                                    inputs=sample_inputs,
                                    output_exprs=output_exprs,
                                    output_order=output_order,
                                )
                                if _vector_tuple(sample_vector, output_order) != vector:
                                    errors.append(
                                        f"{spec_id}: sampled reachable case does not satisfy its contract vector {vector}"
                                    )

                if tau_bin:
                    tau_report = collect_assurance_entry_cases(
                        tau_bin=tau_bin,
                        entry=entry,
                        root=ROOT,
                        oracle_outputs_override=output_exprs,
                    )
                    tau_mismatches = list(tau_report.get("oracle_mismatches", []))
                    if tau_mismatches:
                        errors.append(
                            f"{spec_id}: contract and Tau binary disagree on {len(tau_mismatches)} explicit-domain cases"
                        )
                    else:
                        tau_checked_specs.append(spec_id)

        if len(errors) == scoped_error_count and (not tau_bin or spec_id in tau_checked_specs or proof_scope != "bounded_assurance_domain"):
            checked_specs.append(spec_id)

    return TauFormalContractsResult(
        errors=errors,
        checked_specs=checked_specs,
        tau_checked_specs=tau_checked_specs,
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate active/promoted Tau formal contracts and atlases against profile requirements."
    )
    parser.add_argument("--plan", default=str(DEFAULT_PLAN), help="Path to Tau formal proof plan JSON.")
    parser.add_argument("--registry", default=str(DEFAULT_REGISTRY), help="Path to Tau assurance registry JSON.")
    parser.add_argument("--contracts-dir", default=str(DEFAULT_CONTRACTS_DIR), help="Path to formal contracts directory.")
    parser.add_argument("--atlases-dir", default=str(DEFAULT_ATLASES_DIR), help="Path to formal atlases directory.")
    parser.add_argument("--tau-bin", default="", help="Optional Tau binary path for differential checking.")
    parser.add_argument(
        "--use-discovered-tau",
        action="store_true",
        help="If set, attempt to discover tau on PATH/workspace when --tau-bin is not provided.",
    )
    args = parser.parse_args()

    tau_bin = args.tau_bin.strip() or None
    if tau_bin is None and args.use_discovered_tau:
        tau_bin = find_tau_bin()

    result = validate_tau_formal_contract_artifacts(
        plan_path=Path(args.plan),
        registry_path=Path(args.registry),
        contracts_dir=Path(args.contracts_dir),
        atlases_dir=Path(args.atlases_dir),
        tau_bin=tau_bin,
    )
    if result.errors:
        for error in result.errors:
            print(f"ERROR: {error}")
        return 1

    print(f"checked formal specs: {len(result.checked_specs)}")
    for spec_id in result.checked_specs:
        print(f"  {spec_id}")
    if tau_bin:
        print(f"tau differential checked: {len(result.tau_checked_specs)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
