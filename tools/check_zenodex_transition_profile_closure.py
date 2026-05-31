#!/usr/bin/env python3
"""Validate ZenoDEX critical transition-family replay/proof closure."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

DEFAULT_MANIFEST = ROOT / "docs" / "ZENODEX_TRANSITION_PROFILE_CLOSURE_V0.json"
DEFAULT_HOST_COVERAGE = ROOT / "docs" / "ZENODEX_HOST_INDEPENDENT_COVERAGE_V0.json"
DEFAULT_BATCH_PROOF = ROOT / "docs" / "ZENODEX_BATCH_PROOF_COVERAGE_V0.json"
DEFAULT_PROOF_MATRIX = ROOT / "docs" / "ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json"
DEFAULT_PROOF_PROFILES = ROOT / "config" / "proof_profiles" / "zeno_ledger_profiles.json"

SCHEMA = "zenodex.transition_profile_closure.v0"
REPORT_SCHEMA = "zenodex.transition_profile_closure_report.v0"
CHECKER_COMMAND = "python3 tools/check_zenodex_transition_profile_closure.py"
CHECKER_TEST_COMMAND = "pytest -q tests/tools/test_check_zenodex_transition_profile_closure.py"

ADMISSION_MODES = {"deterministic_replay", "zkvm_proof"}
ADMITTED_PUBLIC_DATA = {
    "deterministic_replay": "public_inputs_and_replay_artifacts",
    "zkvm_proof": "public_inputs_and_proof_artifacts",
}
UNSUPPORTED_PUBLIC_DATA = "fail_closed_non_admitted"
REQUIRED_PROOF_REQUIRED_BEHAVIOR = {
    "rejects_missing_proof",
    "rejects_wrong_profile_id",
    "rejects_unsupported_transition_family",
    "metadata_only_cannot_authorize_transition",
}
REQUIRED_FAIL_CLOSED_CHECKS = {
    "reject_missing_proof",
    "reject_wrong_profile_id",
    "reject_unsupported_transition_family",
}

REQUIRED_SURFACE_FAMILIES: dict[str, set[str]] = {
    "spot_intent_admission_and_settlement": {
        "create_pool",
        "swap_exact_in",
        "swap_exact_out",
        "add_liquidity",
        "remove_liquidity",
        "nonce_sequencing",
        "accepted_receipts_root",
        "rejected_receipt_execution",
    },
    "spot_v1_risc0_supported_transition_kernel": {
        "empty_transition",
        "faucet_mint",
        "create_pool",
        "swap_exact_in",
        "add_liquidity",
        "remove_liquidity",
        "liquidity_cycle_block",
    },
    "upba_bounded_grid_and_exact_out_certificates": {
        "upba_exact_out_batch_clearing",
        "bounded_grid_certificate_verification",
        "candidate_root_binding",
        "fill_vector_root_binding",
    },
    "oracle_critical_action_authorization": {
        "oracle_perps_settlement_authorization",
        "oracle_zusd_lifecycle_authorization",
        "oracle_guarded_routing_authorization",
        "oracle_trigger_execution_authorization",
        "oracle_typed_dex_settlement_authorization",
    },
    "perps_bounded_production_candidate_surface": {
        "perps_order_settlement",
        "perps_funding_application",
        "perps_liquidation",
        "perps_insurance_fund_accounting",
        "perps_oracle_bound_runtime_shell",
    },
    "zusd_lifecycle_microgate_surface": {
        "zusd_mint",
        "zusd_repay",
        "zusd_redeem",
        "zusd_liquidation",
        "zusd_stability_pool_claim",
        "zusd_oracle_authorized_lifecycle",
    },
    "proof_mining_reward_and_claimability_surface": {
        "proof_mining_claimability",
        "proof_mining_reward_payout",
        "proof_mining_manager_state_transition",
    },
}

REQUIRED_UNSUPPORTED_PROFILE_OPERATIONS: dict[str, set[str]] = {
    "spot_v1_single_pool_success": {
        "rejected_receipts",
        "swap_exact_out",
        "upba_batch_clearing",
        "multi_hop",
        "native_assets",
    }
}


def validate_transition_profile_closure_v0(
    manifest: Any,
    *,
    host_coverage_path: Path = DEFAULT_HOST_COVERAGE,
    batch_proof_path: Path = DEFAULT_BATCH_PROOF,
    proof_matrix_path: Path = DEFAULT_PROOF_MATRIX,
    proof_profiles_path: Path = DEFAULT_PROOF_PROFILES,
    repo_root: Path = ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != SCHEMA:
        errors.append("schema mismatch")

    host_surfaces = _load_host_surfaces(host_coverage_path, errors)
    batch_gap_lanes = _load_batch_gap_lanes(batch_proof_path, errors)
    supported_proof_ids = _load_supported_proof_ids(proof_matrix_path, errors)
    proof_profiles = _load_proof_profiles(proof_profiles_path, errors)

    _validate_claim_boundary(_mapping(obj.get("claim_boundary"), "claim_boundary", errors), errors)
    _validate_release_gates(obj.get("release_gates"), host_coverage_path, errors)
    _validate_proof_required_behavior(obj.get("proof_required_behavior"), errors)

    admitted_reports: list[dict[str, Any]] = []
    families_by_surface: dict[str, set[str]] = {}
    admitted_zk_by_profile_operation: set[tuple[str, str]] = set()
    admitted_replay_surfaces: set[str] = set()
    seen_admitted_ids: set[str] = set()
    for index, raw_group in enumerate(_list(obj.get("admitted_transition_families"), "admitted_transition_families", errors)):
        report = _validate_admitted_group(
            raw_group,
            index=index,
            host_surfaces=host_surfaces,
            supported_proof_ids=supported_proof_ids,
            proof_profiles=proof_profiles,
            repo_root=repo_root,
        )
        admitted_reports.append(report)
        errors.extend(f"admitted_transition_families[{index}]: {error}" for error in report["errors"])
        group_id = report["id"]
        if group_id:
            if group_id in seen_admitted_ids:
                errors.append(f"admitted_transition_families[{index}]: duplicate id")
            seen_admitted_ids.add(group_id)
        surface_id = report["surface_id"]
        if surface_id:
            families_by_surface.setdefault(surface_id, set()).update(report["families"])
            if report["admission_mode"] == "deterministic_replay":
                admitted_replay_surfaces.add(surface_id)
        if report["admission_mode"] == "zkvm_proof":
            profile_id = report["governed_profile_id"]
            for family in report["families"]:
                admitted_zk_by_profile_operation.add((profile_id, family))

    unsupported_reports: list[dict[str, Any]] = []
    unsupported_by_profile_operation: set[tuple[str, str]] = set()
    seen_unsupported_ids: set[str] = set()
    for index, raw_entry in enumerate(
        _list(obj.get("unsupported_proof_required_families"), "unsupported_proof_required_families", errors)
    ):
        report = _validate_unsupported_entry(
            raw_entry,
            index=index,
            host_surfaces=host_surfaces,
            proof_profiles=proof_profiles,
            repo_root=repo_root,
        )
        unsupported_reports.append(report)
        errors.extend(f"unsupported_proof_required_families[{index}]: {error}" for error in report["errors"])
        entry_id = report["id"]
        if entry_id:
            if entry_id in seen_unsupported_ids:
                errors.append(f"unsupported_proof_required_families[{index}]: duplicate id")
            seen_unsupported_ids.add(entry_id)
        if report["proof_required_profile_id"] and report["profile_operation"]:
            unsupported_by_profile_operation.add((report["proof_required_profile_id"], report["profile_operation"]))

    transition_surface_ids = {
        surface_id
        for surface_id, surface in host_surfaces.items()
        if surface.get("counts_as_transition_coverage") is True
    }
    for surface_id in sorted(transition_surface_ids):
        if surface_id not in families_by_surface:
            errors.append(f"missing admitted transition-family mapping for transition surface: {surface_id}")
    for surface_id, required_families in sorted(REQUIRED_SURFACE_FAMILIES.items()):
        present = families_by_surface.get(surface_id, set())
        missing = sorted(required_families - present)
        if missing:
            errors.append(f"{surface_id} missing required families: {','.join(missing)}")

    for profile_id, required_operations in sorted(REQUIRED_UNSUPPORTED_PROFILE_OPERATIONS.items()):
        profile = proof_profiles.get(profile_id)
        not_covered = _str_set(profile.get("not_covered") if profile else [], "not_covered", [])
        for operation in sorted(required_operations):
            if operation not in not_covered:
                errors.append(f"{profile_id} no longer lists required not_covered operation: {operation}")
            if (profile_id, operation) not in unsupported_by_profile_operation:
                errors.append(f"missing unsupported proof-required entry: {profile_id}:{operation}")
            if (profile_id, operation) in admitted_zk_by_profile_operation:
                errors.append(f"unsupported proof-required operation also admitted as zkvm_proof: {profile_id}:{operation}")

    for lane in batch_gap_lanes:
        if lane.get("value_moving") is not True:
            continue
        if lane.get("current_fallback") != "deterministic_replay":
            continue
        host_surface_id = lane.get("host_surface_id")
        if isinstance(host_surface_id, str) and host_surface_id not in admitted_replay_surfaces:
            gap_id = lane.get("proof_gap_id", "<unknown>")
            errors.append(f"value-moving proof gap lacks deterministic replay closure: {gap_id}:{host_surface_id}")

    admitted_family_count = sum(len(report["families"]) for report in admitted_reports)
    value_moving_family_count = sum(len(report["value_moving_families"]) for report in admitted_reports)
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "admitted_group_count": len(admitted_reports),
        "admitted_family_count": admitted_family_count,
        "value_moving_family_count": value_moving_family_count,
        "unsupported_proof_required_count": len(unsupported_reports),
        "transition_surface_count": len(transition_surface_ids),
        "mapped_transition_surface_count": len(transition_surface_ids & set(families_by_surface)),
        "admitted_groups": admitted_reports,
        "unsupported_proof_required": unsupported_reports,
    }


def _validate_claim_boundary(boundary: Mapping[str, Any], errors: list[str]) -> None:
    if boundary.get("full_node_host_independence") != "supported_scoped":
        errors.append("claim_boundary.full_node_host_independence must be supported_scoped")
    if boundary.get("succinct_everything_host_independence") != "frontier_open":
        errors.append("claim_boundary.succinct_everything_host_independence must be frontier_open")
    for key in (
        "host_may_be_byzantine",
        "unsupported_proof_required_paths_are_fail_closed",
        "metadata_only_cannot_authorize_value_moving_transition",
    ):
        if boundary.get(key) is not True:
            errors.append(f"claim_boundary.{key} must be true")
    _str(boundary.get("transition_acceptance_rule"), "claim_boundary.transition_acceptance_rule", errors)


def _validate_release_gates(value: Any, host_coverage_path: Path, errors: list[str]) -> None:
    gates = _str_list(value, "release_gates", errors)
    for required in (CHECKER_COMMAND, CHECKER_TEST_COMMAND):
        if required not in gates:
            errors.append(f"release_gates missing: {required}")
    try:
        host = json.loads(host_coverage_path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"host coverage manifest load failed: {exc}")
        return
    host_gates = _str_list(host.get("release_gates") if isinstance(host, Mapping) else None, "host release_gates", errors)
    if CHECKER_COMMAND not in host_gates:
        errors.append("host coverage release_gates must include transition profile closure checker")


def _validate_proof_required_behavior(value: Any, errors: list[str]) -> None:
    behavior = _mapping(value, "proof_required_behavior", errors)
    for key in sorted(REQUIRED_PROOF_REQUIRED_BEHAVIOR):
        if behavior.get(key) is not True:
            errors.append(f"proof_required_behavior.{key} must be true")


def _validate_admitted_group(
    raw_group: Any,
    *,
    index: int,
    host_surfaces: Mapping[str, Mapping[str, Any]],
    supported_proof_ids: set[str],
    proof_profiles: Mapping[str, Mapping[str, Any]],
    repo_root: Path,
) -> dict[str, Any]:
    del index
    errors: list[str] = []
    group = _mapping(raw_group, "admitted_transition_family", errors)
    group_id = _str(group.get("id"), "id", errors)
    surface_id = _str(group.get("surface_id"), "surface_id", errors)
    admission_mode = _str(group.get("admission_mode"), "admission_mode", errors)
    governed_profile_id = _str(group.get("governed_profile_id"), "governed_profile_id", errors)
    public_data = _str(group.get("public_data_availability"), "public_data_availability", errors)
    families = _str_set(group.get("families"), "families", errors)
    value_moving_families = _str_set(group.get("value_moving_families"), "value_moving_families", errors)
    evidence_paths = _str_list(group.get("evidence_paths"), "evidence_paths", errors)
    checker_commands = _str_list(group.get("checker_commands"), "checker_commands", errors)
    limits = _str_list(group.get("limits"), "limits", errors)

    surface = host_surfaces.get(surface_id)
    if surface is None:
        errors.append(f"surface_id missing from host coverage manifest: {surface_id}")
    else:
        if surface.get("counts_as_transition_coverage") is not True:
            errors.append("admitted family must reference a transition-coverage host surface")

    if admission_mode not in ADMISSION_MODES:
        errors.append(f"admission_mode has unsupported value: {admission_mode}")
    elif public_data != ADMITTED_PUBLIC_DATA[admission_mode]:
        errors.append(f"{admission_mode} requires {ADMITTED_PUBLIC_DATA[admission_mode]}")
    if value_moving_families - families:
        errors.append("value_moving_families must be a subset of families")
    if not families:
        errors.append("families must be non-empty")
    if not value_moving_families and surface_id not in {
        "spot_v1_risc0_supported_transition_kernel",
        "upba_bounded_grid_and_exact_out_certificates",
    }:
        errors.append("transition groups must identify value_moving_families")

    if admission_mode == "zkvm_proof":
        proof_surface_id = _str(group.get("proof_surface_id"), "proof_surface_id", errors)
        if proof_surface_id not in supported_proof_ids:
            errors.append(f"proof_surface_id missing from proof coverage matrix: {proof_surface_id}")
        if governed_profile_id not in proof_profiles:
            errors.append(f"zkvm_proof governed_profile_id missing from proof profiles: {governed_profile_id}")
        if surface_id == "spot_v1_risc0_supported_transition_kernel" and surface is not None:
            covered = _str_set(surface.get("covered_operations"), "covered_operations", errors)
            not_covered = _str_set(surface.get("not_covered_operations"), "not_covered_operations", errors)
            uncovered = sorted(families - covered)
            if uncovered:
                errors.append("spot v1 zk families not covered by host Risc0 operations: " + ",".join(uncovered))
            conflicting = sorted(families & not_covered)
            if conflicting:
                errors.append("spot v1 zk families conflict with not_covered_operations: " + ",".join(conflicting))
    elif "proof_surface_id" in group:
        errors.append("deterministic_replay groups must not carry proof_surface_id")

    if not checker_commands:
        errors.append("checker_commands must be non-empty")
    if not limits:
        errors.append("limits must be non-empty")
    _validate_paths_exist(evidence_paths, repo_root, errors)

    return {
        "id": group_id,
        "surface_id": surface_id,
        "admission_mode": admission_mode,
        "governed_profile_id": governed_profile_id,
        "families": sorted(families),
        "value_moving_families": sorted(value_moving_families),
        "ok": not errors,
        "errors": errors,
    }


def _validate_unsupported_entry(
    raw_entry: Any,
    *,
    index: int,
    host_surfaces: Mapping[str, Mapping[str, Any]],
    proof_profiles: Mapping[str, Mapping[str, Any]],
    repo_root: Path,
) -> dict[str, Any]:
    del index
    errors: list[str] = []
    entry = _mapping(raw_entry, "unsupported_proof_required_family", errors)
    entry_id = _str(entry.get("id"), "id", errors)
    surface_id = _str(entry.get("surface_id"), "surface_id", errors)
    profile_id = _str(entry.get("proof_required_profile_id"), "proof_required_profile_id", errors)
    profile_operation = _str(entry.get("profile_operation"), "profile_operation", errors)
    transition_family = _str(entry.get("transition_family"), "transition_family", errors)
    public_data = _str(entry.get("public_data_availability"), "public_data_availability", errors)
    fail_closed_checks = _str_set(entry.get("fail_closed_checks"), "fail_closed_checks", errors)
    evidence_paths = _str_list(entry.get("evidence_paths"), "evidence_paths", errors)
    checker_commands = _str_list(entry.get("checker_commands"), "checker_commands", errors)
    limits = _str_list(entry.get("limits"), "limits", errors)

    if surface_id not in host_surfaces:
        errors.append(f"surface_id missing from host coverage manifest: {surface_id}")
    profile = proof_profiles.get(profile_id)
    if profile is None:
        errors.append(f"proof_required_profile_id missing from proof profiles: {profile_id}")
    else:
        not_covered = _str_set(profile.get("not_covered"), "not_covered", errors)
        if profile_operation not in not_covered:
            errors.append(f"profile_operation is not listed as not_covered by {profile_id}: {profile_operation}")
    if public_data != UNSUPPORTED_PUBLIC_DATA:
        errors.append(f"unsupported proof-required families must use {UNSUPPORTED_PUBLIC_DATA}")
    missing_checks = sorted(REQUIRED_FAIL_CLOSED_CHECKS - fail_closed_checks)
    if missing_checks:
        errors.append("fail_closed_checks missing: " + ",".join(missing_checks))
    if not transition_family:
        errors.append("transition_family must be non-empty")
    if not checker_commands:
        errors.append("checker_commands must be non-empty")
    if not limits:
        errors.append("limits must be non-empty")
    _validate_paths_exist(evidence_paths, repo_root, errors)

    return {
        "id": entry_id,
        "surface_id": surface_id,
        "proof_required_profile_id": profile_id,
        "profile_operation": profile_operation,
        "transition_family": transition_family,
        "ok": not errors,
        "errors": errors,
    }


def _load_host_surfaces(path: Path, errors: list[str]) -> dict[str, Mapping[str, Any]]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"host coverage manifest load failed: {exc}")
        return {}
    if not isinstance(obj, Mapping):
        errors.append("host coverage manifest must be an object")
        return {}
    out: dict[str, Mapping[str, Any]] = {}
    for surface in _list(obj.get("critical_surfaces"), "host critical_surfaces", errors):
        if not isinstance(surface, Mapping):
            continue
        surface_id = surface.get("id")
        if isinstance(surface_id, str) and surface_id:
            out[surface_id] = surface
    return out


def _load_batch_gap_lanes(path: Path, errors: list[str]) -> list[Mapping[str, Any]]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"batch proof manifest load failed: {exc}")
        return []
    if not isinstance(obj, Mapping):
        errors.append("batch proof manifest must be an object")
        return []
    out: list[Mapping[str, Any]] = []
    for lane in _list(obj.get("proof_gap_batch_lanes"), "proof_gap_batch_lanes", errors):
        if isinstance(lane, Mapping):
            out.append(lane)
    return out


def _load_supported_proof_ids(path: Path, errors: list[str]) -> set[str]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"proof matrix load failed: {exc}")
        return set()
    if not isinstance(obj, Mapping):
        errors.append("proof matrix must be an object")
        return set()
    out: set[str] = set()
    for surface in _list(obj.get("supported_surfaces"), "supported_surfaces", errors):
        if isinstance(surface, Mapping) and isinstance(surface.get("id"), str):
            out.add(str(surface["id"]))
    return out


def _load_proof_profiles(path: Path, errors: list[str]) -> dict[str, Mapping[str, Any]]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"proof profiles load failed: {exc}")
        return {}
    if not isinstance(obj, Mapping):
        errors.append("proof profiles registry must be an object")
        return {}
    out: dict[str, Mapping[str, Any]] = {}
    for profile in _list(obj.get("profiles"), "proof profiles", errors):
        if not isinstance(profile, Mapping):
            continue
        profile_id = profile.get("profile_id")
        if isinstance(profile_id, str) and profile_id:
            out[profile_id] = profile
    return out


def _validate_paths_exist(paths: list[str], repo_root: Path, errors: list[str]) -> None:
    if not paths:
        errors.append("evidence_paths must be non-empty")
        return
    root = repo_root.resolve()
    missing: list[str] = []
    for rel_path in paths:
        candidate = (repo_root / rel_path).resolve()
        try:
            candidate.relative_to(root)
        except ValueError:
            errors.append(f"evidence path escapes repo: {rel_path}")
            continue
        if not candidate.exists():
            missing.append(rel_path)
    if missing:
        errors.append("evidence_paths missing: " + ",".join(missing))


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return []
    return value


def _str(value: Any, name: str, errors: list[str]) -> str:
    if not isinstance(value, str) or value == "":
        errors.append(f"{name} must be a non-empty string")
        return ""
    return value


def _str_list(value: Any, name: str, errors: list[str]) -> list[str]:
    items = _list(value, name, errors)
    out: list[str] = []
    for index, item in enumerate(items):
        parsed = _str(item, f"{name}[{index}]", errors)
        if parsed:
            out.append(parsed)
    return out


def _str_set(value: Any, name: str, errors: list[str]) -> set[str]:
    return set(_str_list(value, name, errors))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--host-coverage", type=Path, default=DEFAULT_HOST_COVERAGE)
    parser.add_argument("--batch-proof", type=Path, default=DEFAULT_BATCH_PROOF)
    parser.add_argument("--proof-matrix", type=Path, default=DEFAULT_PROOF_MATRIX)
    parser.add_argument("--proof-profiles", type=Path, default=DEFAULT_PROOF_PROFILES)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    report = validate_transition_profile_closure_v0(
        manifest,
        host_coverage_path=args.host_coverage,
        batch_proof_path=args.batch_proof,
        proof_matrix_path=args.proof_matrix,
        proof_profiles_path=args.proof_profiles,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
