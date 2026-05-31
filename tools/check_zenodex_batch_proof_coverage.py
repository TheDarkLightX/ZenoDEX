#!/usr/bin/env python3
"""Validate ZenoDEX batch-proof coverage lanes for open proof gaps."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

DEFAULT_MANIFEST = ROOT / "docs" / "ZENODEX_BATCH_PROOF_COVERAGE_V0.json"
DEFAULT_HOST_COVERAGE = ROOT / "docs" / "ZENODEX_HOST_INDEPENDENT_COVERAGE_V0.json"
DEFAULT_PROOF_MATRIX = ROOT / "docs" / "ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json"

SCHEMA = "zenodex.batch_proof_coverage.v0"
REPORT_SCHEMA = "zenodex.batch_proof_coverage_report.v0"
GAP_STATUS = "open_real_proof_gap"
SUPPORTED_LANE_STATUSES = {"covered", "covered_scoped"}
SUPPORTED_FALLBACKS = {
    "deterministic_replay",
    "zkvm_proof",
    "proof_metadata_and_report_replay",
    "checkpoint_quorum_replay",
    "fail_closed_blocked",
}
REQUIRED_PUBLIC_INPUT_FIELDS = {
    "chain_id",
    "profile_id",
    "proof_system_id",
    "pre_state_root",
    "post_state_root",
    "transition_batch_root",
    "transition_count",
    "public_data_root",
}


def validate_batch_proof_coverage_v0(
    manifest: Any,
    *,
    host_coverage_path: Path = DEFAULT_HOST_COVERAGE,
    proof_matrix_path: Path = DEFAULT_PROOF_MATRIX,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != SCHEMA:
        errors.append("schema mismatch")

    host_surfaces = _load_host_surfaces(host_coverage_path, errors)
    supported_proof_ids, gap_ids = _load_proof_matrix_ids(proof_matrix_path, errors)

    boundary = _mapping(obj.get("claim_boundary"), "claim_boundary", errors)
    _validate_claim_boundary(boundary, errors)
    _validate_batching_model(_mapping(obj.get("batching_model"), "batching_model", errors), errors)
    _validate_required_public_input_fields(obj.get("required_public_input_fields"), errors)
    _validate_fail_closed_policy(_mapping(obj.get("fail_closed_policy"), "fail_closed_policy", errors), errors)

    supported_reports = [
        _validate_supported_lane(raw, index=index, supported_proof_ids=supported_proof_ids, host_surfaces=host_surfaces)
        for index, raw in enumerate(_list(obj.get("current_supported_proof_lanes"), "current_supported_proof_lanes", errors))
    ]
    for index, report in enumerate(supported_reports):
        errors.extend(f"current_supported_proof_lanes[{index}]: {error}" for error in report["errors"])

    gap_reports: list[dict[str, Any]] = []
    seen_gaps: set[str] = set()
    for index, raw_lane in enumerate(_list(obj.get("proof_gap_batch_lanes"), "proof_gap_batch_lanes", errors)):
        report = _validate_gap_lane(raw_lane, index=index, host_surfaces=host_surfaces, proof_gap_ids=gap_ids)
        gap_reports.append(report)
        errors.extend(f"proof_gap_batch_lanes[{index}]: {error}" for error in report["errors"])
        gap_id = report["proof_gap_id"]
        if gap_id:
            if gap_id in seen_gaps:
                errors.append(f"proof_gap_batch_lanes[{index}]: duplicate proof_gap_id")
            seen_gaps.add(gap_id)

    missing_gap_lanes = sorted(gap_ids - seen_gaps)
    extra_gap_lanes = sorted(seen_gaps - gap_ids)
    if missing_gap_lanes:
        errors.append("missing proof_gap_batch_lanes for: " + ",".join(missing_gap_lanes))
    if extra_gap_lanes:
        errors.append("proof_gap_batch_lanes not in proof coverage matrix gaps: " + ",".join(extra_gap_lanes))

    succinct_status = boundary.get("succinct_everything_host_independence")
    if succinct_status != "frontier_open" and seen_gaps:
        errors.append("succinct_everything_host_independence must remain frontier_open while proof gaps exist")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "supported_lane_count": len(supported_reports),
        "proof_gap_lane_count": len(gap_reports),
        "proof_gap_ids": sorted(gap_ids),
        "covered_gap_ids": sorted(seen_gaps),
        "missing_gap_lanes": missing_gap_lanes,
        "extra_gap_lanes": extra_gap_lanes,
        "supported_lanes": supported_reports,
        "gap_lanes": gap_reports,
    }


def _validate_claim_boundary(boundary: Mapping[str, Any], errors: list[str]) -> None:
    if boundary.get("succinct_everything_host_independence") != "frontier_open":
        errors.append("claim_boundary.succinct_everything_host_independence must be frontier_open")
    for key in (
        "batching_is_performance_mechanism_not_trust_boundary",
        "provers_are_untrusted",
        "verifier_accepts_only_public_inputs_and_valid_proofs",
        "replay_fallback_required_until_full_zk_green",
    ):
        if boundary.get(key) is not True:
            errors.append(f"claim_boundary.{key} must be true")
    if boundary.get("private_hardware_details_public") is not False:
        errors.append("claim_boundary.private_hardware_details_public must be false")


def _validate_batching_model(model: Mapping[str, Any], errors: list[str]) -> None:
    for key in (
        "batch_unit",
        "parallelism_model",
        "aggregation_model",
        "validator_work_model",
        "data_availability_model",
    ):
        _str(model.get(key), f"batching_model.{key}", errors)


def _validate_required_public_input_fields(value: Any, errors: list[str]) -> None:
    fields = set(_str_list(value, "required_public_input_fields", errors))
    missing = sorted(REQUIRED_PUBLIC_INPUT_FIELDS - fields)
    if missing:
        errors.append("required_public_input_fields missing: " + ",".join(missing))


def _validate_fail_closed_policy(policy: Mapping[str, Any], errors: list[str]) -> None:
    for key in (
        "proof_required_profile_rejects_missing_proof",
        "proof_required_profile_rejects_wrong_profile_id",
        "proof_required_profile_rejects_uncovered_transition_family",
        "metadata_only_cannot_count_as_transition_proof",
        "replay_fallback_profile_replays_public_artifacts",
    ):
        if policy.get(key) is not True:
            errors.append(f"fail_closed_policy.{key} must be true")


def _validate_supported_lane(
    raw_lane: Any,
    *,
    index: int,
    supported_proof_ids: set[str],
    host_surfaces: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    del index
    errors: list[str] = []
    lane = _mapping(raw_lane, "supported_lane", errors)
    proof_surface_id = _str(lane.get("proof_surface_id"), "proof_surface_id", errors)
    host_surface_id = _str(lane.get("host_surface_id"), "host_surface_id", errors)
    status = _str(lane.get("status"), "status", errors)
    if status and status not in SUPPORTED_LANE_STATUSES:
        errors.append(f"status has unsupported value: {status}")
    if proof_surface_id and proof_surface_id not in supported_proof_ids:
        errors.append(f"proof_surface_id missing from supported proof matrix: {proof_surface_id}")
    _validate_host_surface_ref(host_surface_id, host_surfaces, errors)
    _validate_public_fields(lane.get("public_input_fields"), errors)
    for key in ("batch_unit", "aggregation_plan"):
        _str(lane.get(key), key, errors)
    if not _str_list(lane.get("covered_transition_families"), "covered_transition_families", errors):
        errors.append("covered_transition_families must be non-empty")
    if not _str_list(lane.get("limits"), "limits", errors):
        errors.append("limits must be non-empty")
    return {
        "proof_surface_id": proof_surface_id,
        "host_surface_id": host_surface_id,
        "ok": not errors,
        "errors": errors,
    }


def _validate_gap_lane(
    raw_lane: Any,
    *,
    index: int,
    host_surfaces: Mapping[str, Mapping[str, Any]],
    proof_gap_ids: set[str],
) -> dict[str, Any]:
    del index
    errors: list[str] = []
    lane = _mapping(raw_lane, "proof_gap_lane", errors)
    proof_gap_id = _str(lane.get("proof_gap_id"), "proof_gap_id", errors)
    host_surface_id = _str(lane.get("host_surface_id"), "host_surface_id", errors)
    status = _str(lane.get("status"), "status", errors)
    current_fallback = _str(lane.get("current_fallback"), "current_fallback", errors)
    value_moving = lane.get("value_moving")

    if proof_gap_id and proof_gap_id not in proof_gap_ids:
        errors.append(f"proof_gap_id missing from proof matrix gaps: {proof_gap_id}")
    if status != GAP_STATUS:
        errors.append("proof gap lane status must be open_real_proof_gap")
    if current_fallback not in SUPPORTED_FALLBACKS:
        errors.append(f"current_fallback has unsupported value: {current_fallback}")
    if not isinstance(value_moving, bool):
        errors.append("value_moving must be boolean")

    host_surface = _validate_host_surface_ref(host_surface_id, host_surfaces, errors)
    if value_moving is True and host_surface is not None:
        if host_surface.get("counts_as_transition_coverage") is not True:
            errors.append("value-moving gap lane must reference a transition-coverage host surface")

    for key in ("batch_unit", "parallelism", "aggregation_plan", "proof_required_fail_closed_rule"):
        _str(lane.get(key), key, errors)
    _validate_public_fields(lane.get("public_input_fields"), errors)
    _validate_performance_gate(_mapping(lane.get("performance_gate"), "performance_gate", errors), errors)
    requirements = _str_list(lane.get("promotion_requirements"), "promotion_requirements", errors)
    if len(requirements) < 3:
        errors.append("promotion_requirements must contain at least three items")

    return {
        "proof_gap_id": proof_gap_id,
        "host_surface_id": host_surface_id,
        "value_moving": value_moving,
        "ok": not errors,
        "errors": errors,
    }


def _validate_host_surface_ref(
    host_surface_id: str,
    host_surfaces: Mapping[str, Mapping[str, Any]],
    errors: list[str],
) -> Mapping[str, Any] | None:
    if not host_surface_id:
        return None
    surface = host_surfaces.get(host_surface_id)
    if surface is None:
        errors.append(f"host_surface_id missing from host coverage manifest: {host_surface_id}")
        return None
    return surface


def _validate_public_fields(value: Any, errors: list[str]) -> None:
    fields = set(_str_list(value, "public_input_fields", errors))
    missing = sorted(REQUIRED_PUBLIC_INPUT_FIELDS - fields)
    if missing:
        errors.append("public_input_fields missing: " + ",".join(missing))


def _validate_performance_gate(gate: Mapping[str, Any], errors: list[str]) -> None:
    for key in ("requires_warm_batched_benchmark", "requires_p95_p99"):
        if gate.get(key) is not True:
            errors.append(f"performance_gate.{key} must be true")
    if gate.get("allows_private_hardware_details_public") is not False:
        errors.append("performance_gate.allows_private_hardware_details_public must be false")


def _load_host_surfaces(path: Path, errors: list[str]) -> dict[str, Mapping[str, Any]]:
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"host coverage manifest load failed: {exc}")
        return {}
    surfaces = manifest.get("critical_surfaces")
    if not isinstance(surfaces, list):
        errors.append("host coverage manifest critical_surfaces must be a list")
        return {}
    return {
        str(surface["id"]): surface
        for surface in surfaces
        if isinstance(surface, Mapping) and isinstance(surface.get("id"), str)
    }


def _load_proof_matrix_ids(path: Path, errors: list[str]) -> tuple[set[str], set[str]]:
    try:
        matrix = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"proof matrix load failed: {exc}")
        return set(), set()
    supported = _list(matrix.get("supported_surfaces"), "proof_matrix.supported_surfaces", errors)
    gaps = _list(matrix.get("gap_surfaces"), "proof_matrix.gap_surfaces", errors)
    supported_ids = {item["id"] for item in supported if isinstance(item, Mapping) and isinstance(item.get("id"), str)}
    gap_ids = {item["id"] for item in gaps if isinstance(item, Mapping) and isinstance(item.get("id"), str)}
    return supported_ids, gap_ids


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


def _str_list(value: Any, name: str, errors: list[str]) -> list[str]:
    items = _list(value, name, errors)
    if not items:
        errors.append(f"{name} must be a non-empty list")
    out: list[str] = []
    for item_index, item in enumerate(items):
        parsed = _str(item, f"{name}[{item_index}]", errors)
        if parsed:
            out.append(parsed)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--host-coverage", type=Path, default=DEFAULT_HOST_COVERAGE)
    parser.add_argument("--proof-matrix", type=Path, default=DEFAULT_PROOF_MATRIX)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = validate_batch_proof_coverage_v0(
        json.loads(args.manifest.read_text(encoding="utf-8")),
        host_coverage_path=args.host_coverage,
        proof_matrix_path=args.proof_matrix,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
