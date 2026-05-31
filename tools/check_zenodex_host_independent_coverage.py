#!/usr/bin/env python3
"""Validate the ZenoDEX host-independent coverage boundary."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

import yaml

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

DEFAULT_MANIFEST = ROOT / "docs" / "ZENODEX_HOST_INDEPENDENT_COVERAGE_V0.json"
DEFAULT_CLAIMS_REGISTRY = ROOT / "docs" / "claims_registry.yaml"
DEFAULT_PROOF_MATRIX = ROOT / "docs" / "ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json"
DEFAULT_PRODUCTION_PROFILE = ROOT / "config" / "deploy" / "production-strict.yaml"

SCHEMA = "zenodex.host_independent_coverage.v0"
REPORT_SCHEMA = "zenodex.host_independent_coverage_report.v0"

SUPPORTED_CLAIM_STATUSES = {"proved", "supported"}
SURFACE_STATUSES = {"covered", "covered_scoped", "open"}
VERIFIER_MODES = {
    "deterministic_replay",
    "zkvm_proof",
    "proof_metadata_and_report_replay",
    "checkpoint_quorum_replay",
    "fail_closed_blocked",
}
PUBLIC_DATA_MODES = {
    "public_inputs_and_replay_artifacts",
    "public_inputs_and_proof_artifacts",
    "checkpoint_data_and_quorum_signature",
    "metadata_only_non_transition",
    "blocked_until_public_inputs_and_proofs",
}
TRANSITION_MODES = {"deterministic_replay", "zkvm_proof"}
NON_TRANSITION_MODES = {"proof_metadata_and_report_replay", "checkpoint_quorum_replay"}
FULL_NODE_SCOPE = "full_node_host_independence"
SUCCINCT_SCOPE = "succinct_everything_host_independence"


def validate_host_independent_coverage_v0(
    manifest: Any,
    *,
    claims_registry: Path = DEFAULT_CLAIMS_REGISTRY,
    proof_matrix: Path = DEFAULT_PROOF_MATRIX,
    production_profile: Path = DEFAULT_PRODUCTION_PROFILE,
    repo_root: Path = ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != SCHEMA:
        errors.append("schema mismatch")

    claim_status_by_id = _load_claim_status_by_id(claims_registry, errors)
    proof_ids, proof_gap_ids = _load_proof_matrix_ids(proof_matrix, errors)
    _validate_production_profile(production_profile, errors)

    boundary = _mapping(obj.get("claim_boundary"), "claim_boundary", errors)
    _validate_claim_boundary(boundary, errors)

    release_gates = _str_list(obj.get("release_gates"), "release_gates", errors)
    for required_gate in (
        "python3 tools/check_zenodex_host_independent_coverage.py",
        "python3 tools/check_zenodex_batch_proof_coverage.py",
        "python3 tools/check_zenodex_proof_substrate_obligations.py",
        "python3 tools/check_zenodex_transition_profile_closure.py",
        "python3 tools/check_zenodex_critical_value_surface_inventory.py",
    ):
        if required_gate not in release_gates:
            errors.append(f"release_gates must include: {required_gate}")

    surfaces = _list(obj.get("critical_surfaces"), "critical_surfaces", errors)
    surface_reports: list[dict[str, Any]] = []
    full_node_open: list[str] = []
    succinct_open: list[str] = []
    seen: set[str] = set()
    for index, raw_surface in enumerate(surfaces):
        report = _validate_surface(
            raw_surface,
            index=index,
            claim_status_by_id=claim_status_by_id,
            proof_ids=proof_ids,
            proof_gap_ids=proof_gap_ids,
            repo_root=repo_root,
        )
        surface_reports.append(report)
        errors.extend(f"critical_surfaces[{index}]: {error}" for error in report["errors"])
        surface_id = report["id"]
        if surface_id:
            if surface_id in seen:
                errors.append(f"critical_surfaces[{index}]: duplicate id")
            seen.add(surface_id)
        if FULL_NODE_SCOPE in report["required_for"] and report["coverage_status"] == "open":
            full_node_open.append(surface_id)
        if SUCCINCT_SCOPE in report["required_for"] and report["coverage_status"] == "open":
            succinct_open.append(surface_id)

    if boundary.get("full_node_host_independence") in {"supported", "supported_scoped"} and full_node_open:
        errors.append(
            "full_node_host_independence cannot be supported while full-node surfaces are open: "
            + ",".join(sorted(full_node_open))
        )
    if boundary.get("succinct_everything_host_independence") in {"supported", "supported_scoped"} and succinct_open:
        errors.append(
            "succinct_everything_host_independence cannot be supported while succinct surfaces are open: "
            + ",".join(sorted(succinct_open))
        )

    non_claims = _str_set(obj.get("non_claims"), "non_claims", errors)
    for required in (
        "does_not_claim_docker_removes_host_trust",
        "does_not_claim_full_zk_execution_for_all_zenodex_surfaces",
        "does_not_claim_metadata_only_is_transition_correctness",
    ):
        if required not in non_claims:
            errors.append(f"missing required non-claim: {required}")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "surface_count": len(surfaces),
        "full_node_open_surfaces": sorted(full_node_open),
        "succinct_open_surfaces": sorted(succinct_open),
        "surfaces": surface_reports,
    }


def _validate_claim_boundary(boundary: Mapping[str, Any], errors: list[str]) -> None:
    if boundary.get("docker_is_correctness_boundary") is not False:
        errors.append("docker_is_correctness_boundary must be false")
    _str(boundary.get("host_adversary_model"), "claim_boundary.host_adversary_model", errors)
    _str(boundary.get("performance_posture"), "claim_boundary.performance_posture", errors)
    full_node = _str(boundary.get("full_node_host_independence"), "claim_boundary.full_node_host_independence", errors)
    succinct = _str(
        boundary.get("succinct_everything_host_independence"),
        "claim_boundary.succinct_everything_host_independence",
        errors,
    )
    for name, value in (
        ("claim_boundary.full_node_host_independence", full_node),
        ("claim_boundary.succinct_everything_host_independence", succinct),
    ):
        if value and value not in {"supported", "supported_scoped", "frontier_open"}:
            errors.append(f"{name} has unsupported status: {value}")
    lessons = _str_list(boundary.get("lean_ethereum_design_lessons"), "claim_boundary.lean_ethereum_design_lessons", errors)
    if len(lessons) < 3:
        errors.append("claim_boundary.lean_ethereum_design_lessons must include at least three lessons")


def _validate_surface(
    raw_surface: Any,
    *,
    index: int,
    claim_status_by_id: Mapping[str, str],
    proof_ids: set[str],
    proof_gap_ids: set[str],
    repo_root: Path,
) -> dict[str, Any]:
    errors: list[str] = []
    surface = _mapping(raw_surface, f"critical_surfaces[{index}]", errors)
    surface_id = _str(surface.get("id"), "id", errors)
    _str(surface.get("description"), "description", errors)
    required_for = _str_list(surface.get("required_for"), "required_for", errors)
    coverage_status = _str(surface.get("coverage_status"), "coverage_status", errors)
    verifier_mode = _str(surface.get("verifier_mode"), "verifier_mode", errors)
    public_data_availability = _str(
        surface.get("public_data_availability"),
        "public_data_availability",
        errors,
    )
    counts_as_transition = surface.get("counts_as_transition_coverage")
    claim_ids = _str_list(surface.get("claim_ids"), "claim_ids", errors, allow_empty=True)
    proof_surface_ids = _str_list(surface.get("proof_surface_ids"), "proof_surface_ids", errors, allow_empty=True)
    proof_gap_refs = _str_list(surface.get("proof_gap_ids"), "proof_gap_ids", errors, allow_empty=True)
    evidence_paths = _str_list(surface.get("evidence_paths"), "evidence_paths", errors, allow_empty=True)
    checker_commands = _str_list(surface.get("checker_commands"), "checker_commands", errors, allow_empty=True)
    limits = _str_list(surface.get("limits"), "limits", errors, allow_empty=True)

    if coverage_status and coverage_status not in SURFACE_STATUSES:
        errors.append(f"coverage_status has unsupported value: {coverage_status}")
    if verifier_mode and verifier_mode not in VERIFIER_MODES:
        errors.append(f"verifier_mode has unsupported value: {verifier_mode}")
    if public_data_availability and public_data_availability not in PUBLIC_DATA_MODES:
        errors.append(
            "public_data_availability has unsupported value: "
            + public_data_availability
        )
    if not isinstance(counts_as_transition, bool):
        errors.append("counts_as_transition_coverage must be boolean")
        counts_as_transition = False

    if counts_as_transition is True and verifier_mode not in TRANSITION_MODES:
        errors.append("transition coverage must use deterministic_replay or zkvm_proof")
    if counts_as_transition is True and verifier_mode == "deterministic_replay":
        if public_data_availability != "public_inputs_and_replay_artifacts":
            errors.append(
                "deterministic transition coverage requires public_inputs_and_replay_artifacts"
            )
    if counts_as_transition is True and verifier_mode == "zkvm_proof":
        if public_data_availability != "public_inputs_and_proof_artifacts":
            errors.append(
                "zk transition coverage requires public_inputs_and_proof_artifacts"
            )
    if verifier_mode in NON_TRANSITION_MODES and counts_as_transition is True:
        errors.append("metadata/report/checkpoint replay must not count as transition coverage")
    if verifier_mode == "proof_metadata_and_report_replay":
        if public_data_availability != "metadata_only_non_transition":
            errors.append(
                "proof metadata/report replay must use metadata_only_non_transition"
            )
    if verifier_mode == "checkpoint_quorum_replay":
        if public_data_availability != "checkpoint_data_and_quorum_signature":
            errors.append(
                "checkpoint quorum replay must use checkpoint_data_and_quorum_signature"
            )
    if verifier_mode == "fail_closed_blocked" and coverage_status != "open":
        errors.append("fail_closed_blocked surfaces must be open")
    if verifier_mode == "fail_closed_blocked":
        if public_data_availability != "blocked_until_public_inputs_and_proofs":
            errors.append(
                "fail_closed_blocked surfaces must use blocked_until_public_inputs_and_proofs"
            )
    if coverage_status == "open" and verifier_mode != "fail_closed_blocked":
        errors.append("open surfaces must use fail_closed_blocked")
    if FULL_NODE_SCOPE in required_for and coverage_status != "open" and counts_as_transition is not True:
        errors.append("full-node covered surfaces must count as transition coverage")

    if coverage_status in {"covered", "covered_scoped"}:
        if not claim_ids and not proof_surface_ids and not evidence_paths:
            errors.append("covered surfaces need claim_ids, proof_surface_ids, or evidence_paths")
        if not checker_commands:
            errors.append("covered surfaces need checker_commands")
        if not limits:
            errors.append("covered surfaces need explicit limits")

    missing_claim_ids = [claim_id for claim_id in claim_ids if claim_status_by_id.get(claim_id) not in SUPPORTED_CLAIM_STATUSES]
    if missing_claim_ids:
        errors.append("claim_ids missing or unsupported: " + ",".join(missing_claim_ids))

    missing_proof_ids = [proof_id for proof_id in proof_surface_ids if proof_id not in proof_ids]
    if missing_proof_ids:
        errors.append("proof_surface_ids missing from proof coverage matrix: " + ",".join(missing_proof_ids))
    missing_gap_ids = [gap_id for gap_id in proof_gap_refs if gap_id not in proof_gap_ids]
    if missing_gap_ids:
        errors.append("proof_gap_ids missing from proof coverage matrix: " + ",".join(missing_gap_ids))

    missing_paths = []
    for rel_path in evidence_paths:
        candidate = (repo_root / rel_path).resolve()
        try:
            candidate.relative_to(repo_root.resolve())
        except ValueError:
            errors.append(f"evidence path escapes repo: {rel_path}")
            continue
        if not candidate.exists():
            missing_paths.append(rel_path)
    if missing_paths:
        errors.append("evidence_paths missing: " + ",".join(missing_paths))

    return {
        "id": surface_id,
        "ok": not errors,
        "errors": errors,
        "required_for": required_for,
        "coverage_status": coverage_status,
        "verifier_mode": verifier_mode,
        "public_data_availability": public_data_availability,
        "counts_as_transition_coverage": counts_as_transition,
        "claim_count": len(claim_ids),
        "proof_surface_count": len(proof_surface_ids),
        "proof_gap_count": len(proof_gap_refs),
    }


def _load_claim_status_by_id(path: Path, errors: list[str]) -> dict[str, str]:
    try:
        raw = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, yaml.YAMLError) as exc:
        errors.append(f"claims registry load failed: {exc}")
        return {}
    if not isinstance(raw, Mapping):
        errors.append("claims registry must be an object")
        return {}
    claims = raw.get("claims")
    if not isinstance(claims, list):
        errors.append("claims registry claims must be a list")
        return {}
    out: dict[str, str] = {}
    for claim in claims:
        if not isinstance(claim, Mapping):
            continue
        claim_id = claim.get("id")
        status = claim.get("status")
        if isinstance(claim_id, str) and isinstance(status, str):
            out[claim_id] = status
    return out


def _load_proof_matrix_ids(path: Path, errors: list[str]) -> tuple[set[str], set[str]]:
    try:
        matrix = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"proof matrix load failed: {exc}")
        return set(), set()
    if not isinstance(matrix, Mapping):
        errors.append("proof matrix must be an object")
        return set(), set()
    supported = _list(matrix.get("supported_surfaces"), "proof_matrix.supported_surfaces", errors)
    gaps = _list(matrix.get("gap_surfaces"), "proof_matrix.gap_surfaces", errors)
    supported_ids = {item["id"] for item in supported if isinstance(item, Mapping) and isinstance(item.get("id"), str)}
    gap_ids = {item["id"] for item in gaps if isinstance(item, Mapping) and isinstance(item.get("id"), str)}
    return supported_ids, gap_ids


def _validate_production_profile(path: Path, errors: list[str]) -> None:
    try:
        profile = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, yaml.YAMLError) as exc:
        errors.append(f"production profile load failed: {exc}")
        return
    if not isinstance(profile, Mapping):
        errors.append("production profile must be an object")
        return
    proof_policy = profile.get("proof_policy")
    if not isinstance(proof_policy, Mapping):
        errors.append("production profile proof_policy must be an object")
        return
    if proof_policy.get("proof_metadata_required") is not True:
        errors.append("production-strict proof_policy.proof_metadata_required must be true")


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
    if not isinstance(value, str) or not value:
        errors.append(f"{name} must be a non-empty string")
        return ""
    return value


def _str_list(value: Any, name: str, errors: list[str], *, allow_empty: bool = False) -> list[str]:
    if value is None and allow_empty:
        return []
    items = _list(value, name, errors)
    if not allow_empty and not items:
        errors.append(f"{name} must be a non-empty list")
    out: list[str] = []
    for item_index, item in enumerate(items):
        parsed = _str(item, f"{name}[{item_index}]", errors)
        if parsed:
            out.append(parsed)
    return out


def _str_set(value: Any, name: str, errors: list[str]) -> set[str]:
    return set(_str_list(value, name, errors))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--claims-registry", type=Path, default=DEFAULT_CLAIMS_REGISTRY)
    parser.add_argument("--proof-matrix", type=Path, default=DEFAULT_PROOF_MATRIX)
    parser.add_argument("--production-profile", type=Path, default=DEFAULT_PRODUCTION_PROFILE)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = validate_host_independent_coverage_v0(
        json.loads(args.manifest.read_text(encoding="utf-8")),
        claims_registry=args.claims_registry,
        proof_matrix=args.proof_matrix,
        production_profile=args.production_profile,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
