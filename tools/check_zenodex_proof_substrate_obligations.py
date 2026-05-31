#!/usr/bin/env python3
"""Validate the Tau-vs-zk proof substrate obligation partition."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

DEFAULT_MANIFEST = ROOT / "docs" / "ZENODEX_PROOF_SUBSTRATE_OBLIGATIONS_V0.json"
DEFAULT_PROOF_MATRIX = ROOT / "docs" / "ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json"
DEFAULT_BATCH_PROOF = ROOT / "docs" / "ZENODEX_BATCH_PROOF_COVERAGE_V0.json"
DEFAULT_TRANSITION_CLOSURE = ROOT / "docs" / "ZENODEX_TRANSITION_PROFILE_CLOSURE_V0.json"
DEFAULT_HOST_COVERAGE = ROOT / "docs" / "ZENODEX_HOST_INDEPENDENT_COVERAGE_V0.json"

SCHEMA = "zenodex.proof_substrate_obligations.v0"
REPORT_SCHEMA = "zenodex.proof_substrate_obligations_report.v0"

REQUIRED_SUBSTRATES = {
    "tau_guard",
    "deterministic_replay",
    "zkvm_execution",
    "checkpoint_quorum_replay",
    "proof_metadata_replay",
    "fail_closed_profile_gate",
    "external_consensus_or_oracle",
}
EXECUTION_SUBSTRATES = {"deterministic_replay", "zkvm_execution"}
VALUE_MOVING_REQUIRED_PUBLIC_FIELDS = {
    "chain_id",
    "profile_id",
    "proof_system_id",
    "pre_state_root",
    "post_state_root",
    "transition_batch_root",
    "transition_count",
    "public_data_root",
}
REQUIRED_NON_CLAIMS = {
    "does_not_claim_tau_closes_real_zkvm_execution_gaps",
    "does_not_claim_tau_proves_external_oracle_truth",
    "does_not_claim_tau_proves_light_client_finality",
    "does_not_claim_tau_proves_value_moving_state_roots",
    "does_not_claim_unsupported_spot_v1_operations_are_proof_admitted",
}


def validate_proof_substrate_obligations_v0(
    manifest: Any,
    *,
    proof_matrix_path: Path = DEFAULT_PROOF_MATRIX,
    batch_proof_path: Path = DEFAULT_BATCH_PROOF,
    transition_closure_path: Path = DEFAULT_TRANSITION_CLOSURE,
    host_coverage_path: Path = DEFAULT_HOST_COVERAGE,
    repo_root: Path = ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != SCHEMA:
        errors.append("schema mismatch")

    proof_gap_ids = _load_proof_gap_ids(proof_matrix_path, errors)
    batch_gap_lanes = _load_batch_gap_lanes(batch_proof_path, errors)
    unsupported_entries = _load_unsupported_entries(transition_closure_path, errors)
    spot_not_covered = _load_spot_not_covered_operations(host_coverage_path, errors)

    boundary = _mapping(obj.get("claim_boundary"), "claim_boundary", errors)
    _validate_claim_boundary(boundary, errors)
    _validate_release_gates(obj.get("release_gates"), errors)
    _validate_substrate_classes(obj.get("substrate_classes"), errors)

    proof_gap_reports: list[dict[str, Any]] = []
    seen_proof_gaps: set[str] = set()
    tau_guard_gap_count = 0
    zkvm_required_gap_count = 0
    for index, raw_obligation in enumerate(
        _list(obj.get("proof_gap_obligations"), "proof_gap_obligations", errors)
    ):
        report = _validate_proof_gap_obligation(
            raw_obligation,
            index=index,
            proof_gap_ids=proof_gap_ids,
            batch_gap_lanes=batch_gap_lanes,
            repo_root=repo_root,
        )
        proof_gap_reports.append(report)
        errors.extend(f"proof_gap_obligations[{index}]: {error}" for error in report["errors"])
        proof_gap_id = report["proof_gap_id"]
        if proof_gap_id:
            if proof_gap_id in seen_proof_gaps:
                errors.append(f"proof_gap_obligations[{index}]: duplicate proof_gap_id")
            seen_proof_gaps.add(proof_gap_id)
        if report["tau_status"] != "not_applicable":
            tau_guard_gap_count += 1
        if report["required_non_tau_substrate"] == "zkvm_execution":
            zkvm_required_gap_count += 1

    missing_proof_gaps = sorted(proof_gap_ids - seen_proof_gaps)
    extra_proof_gaps = sorted(seen_proof_gaps - proof_gap_ids)
    if missing_proof_gaps:
        errors.append("missing proof_gap_obligations for: " + ",".join(missing_proof_gaps))
    if extra_proof_gaps:
        errors.append("proof_gap_obligations not in proof matrix gaps: " + ",".join(extra_proof_gaps))

    unsupported_reports: list[dict[str, Any]] = []
    seen_unsupported: set[str] = set()
    unsupported_transition_families: set[str] = set()
    for index, raw_obligation in enumerate(
        _list(
            obj.get("unsupported_proof_required_family_obligations"),
            "unsupported_proof_required_family_obligations",
            errors,
        )
    ):
        report = _validate_unsupported_family_obligation(
            raw_obligation,
            index=index,
            unsupported_entries=unsupported_entries,
            repo_root=repo_root,
        )
        unsupported_reports.append(report)
        errors.extend(
            f"unsupported_proof_required_family_obligations[{index}]: {error}"
            for error in report["errors"]
        )
        unsupported_id = report["unsupported_family_id"]
        if unsupported_id:
            if unsupported_id in seen_unsupported:
                errors.append(
                    f"unsupported_proof_required_family_obligations[{index}]: duplicate unsupported_family_id"
                )
            seen_unsupported.add(unsupported_id)
        if report["transition_family"]:
            unsupported_transition_families.add(report["transition_family"])

    expected_unsupported = set(unsupported_entries)
    missing_unsupported = sorted(expected_unsupported - seen_unsupported)
    extra_unsupported = sorted(seen_unsupported - expected_unsupported)
    if missing_unsupported:
        errors.append(
            "missing unsupported_proof_required_family_obligations for: "
            + ",".join(missing_unsupported)
        )
    if extra_unsupported:
        errors.append(
            "unsupported_proof_required_family_obligations not in transition closure: "
            + ",".join(extra_unsupported)
        )

    missing_spot_not_covered = sorted(spot_not_covered - unsupported_transition_families)
    if missing_spot_not_covered:
        errors.append(
            "spot not_covered_operations missing unsupported-family obligations: "
            + ",".join(missing_spot_not_covered)
        )

    non_claims = _str_set(obj.get("non_claims"), "non_claims", errors)
    missing_non_claims = sorted(REQUIRED_NON_CLAIMS - non_claims)
    if missing_non_claims:
        errors.append("missing required non-claims: " + ",".join(missing_non_claims))

    tau_closed_real_proof_gap_count = sum(
        1 for report in proof_gap_reports if report["tau_can_close_gap"] is True
    )

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "proof_gap_obligation_count": len(proof_gap_reports),
        "proof_gap_ids": sorted(proof_gap_ids),
        "missing_proof_gap_obligations": missing_proof_gaps,
        "extra_proof_gap_obligations": extra_proof_gaps,
        "tau_guard_gap_count": tau_guard_gap_count,
        "zkvm_required_gap_count": zkvm_required_gap_count,
        "tau_closed_real_proof_gap_count": tau_closed_real_proof_gap_count,
        "unsupported_family_obligation_count": len(unsupported_reports),
        "missing_unsupported_family_obligations": missing_unsupported,
        "extra_unsupported_family_obligations": extra_unsupported,
        "spot_not_covered_operations": sorted(spot_not_covered),
        "proof_gap_obligations": proof_gap_reports,
        "unsupported_family_obligations": unsupported_reports,
    }


def _validate_claim_boundary(boundary: Mapping[str, Any], errors: list[str]) -> None:
    if boundary.get("succinct_everything_host_independence") != "frontier_open":
        errors.append("claim_boundary.succinct_everything_host_independence must be frontier_open")
    for key in (
        "tau_is_guard_or_policy_substrate",
        "tau_inputs_are_host_projected_facts",
        "tau_guard_evidence_cannot_close_execution_proof_gaps",
        "value_moving_transitions_require_replay_or_zkvm_execution",
        "external_truth_requires_external_evidence",
    ):
        if boundary.get(key) is not True:
            errors.append(f"claim_boundary.{key} must be true")
    if boundary.get("docker_is_correctness_boundary") is not False:
        errors.append("claim_boundary.docker_is_correctness_boundary must be false")


def _validate_release_gates(value: Any, errors: list[str]) -> None:
    gates = set(_str_list(value, "release_gates", errors))
    for required in (
        "python3 tools/check_zenodex_proof_substrate_obligations.py",
        "pytest -q tests/tools/test_check_zenodex_proof_substrate_obligations.py",
    ):
        if required not in gates:
            errors.append(f"release_gates must include: {required}")


def _validate_substrate_classes(value: Any, errors: list[str]) -> None:
    classes = _list(value, "substrate_classes", errors)
    seen: set[str] = set()
    counts_by_id: dict[str, bool] = {}
    for index, raw_item in enumerate(classes):
        item = _mapping(raw_item, f"substrate_classes[{index}]", errors)
        class_id = _str(item.get("id"), "id", errors)
        counts_as_execution = item.get("counts_as_execution_proof")
        _str(item.get("description"), "description", errors)
        if class_id:
            if class_id in seen:
                errors.append(f"substrate_classes[{index}]: duplicate id")
            seen.add(class_id)
        if not isinstance(counts_as_execution, bool):
            errors.append(f"substrate_classes[{index}]: counts_as_execution_proof must be boolean")
        elif class_id:
            counts_by_id[class_id] = counts_as_execution

    missing = sorted(REQUIRED_SUBSTRATES - seen)
    extra = sorted(seen - REQUIRED_SUBSTRATES)
    if missing:
        errors.append("substrate_classes missing: " + ",".join(missing))
    if extra:
        errors.append("substrate_classes unsupported: " + ",".join(extra))

    for class_id in EXECUTION_SUBSTRATES:
        if counts_by_id.get(class_id) is not True:
            errors.append(f"substrate_classes.{class_id} must count as execution proof")
    for class_id in REQUIRED_SUBSTRATES - EXECUTION_SUBSTRATES:
        if counts_by_id.get(class_id) is not False:
            errors.append(f"substrate_classes.{class_id} must not count as execution proof")


def _validate_proof_gap_obligation(
    raw_obligation: Any,
    *,
    index: int,
    proof_gap_ids: set[str],
    batch_gap_lanes: Mapping[str, Mapping[str, Any]],
    repo_root: Path,
) -> dict[str, Any]:
    del index
    errors: list[str] = []
    obligation = _mapping(raw_obligation, "proof_gap_obligation", errors)
    proof_gap_id = _str(obligation.get("proof_gap_id"), "proof_gap_id", errors)
    host_surface_id = _str(obligation.get("host_surface_id"), "host_surface_id", errors)
    value_moving = obligation.get("value_moving")
    current_fallback = _str(obligation.get("current_fallback"), "current_fallback", errors)
    required_non_tau = _str(obligation.get("required_non_tau_substrate"), "required_non_tau_substrate", errors)
    tau_status = _str(obligation.get("tau_status"), "tau_status", errors)
    tau_scope = _str(obligation.get("tau_scope"), "tau_scope", errors)
    tau_can_close = obligation.get("tau_can_close_gap")

    if proof_gap_id and proof_gap_id not in proof_gap_ids:
        errors.append(f"proof_gap_id missing from proof matrix gaps: {proof_gap_id}")
    batch_lane = batch_gap_lanes.get(proof_gap_id)
    if batch_lane is None:
        errors.append(f"proof_gap_id missing from batch proof lanes: {proof_gap_id}")
    else:
        if host_surface_id and batch_lane.get("host_surface_id") != host_surface_id:
            errors.append(
                "host_surface_id must match batch proof lane: "
                + str(batch_lane.get("host_surface_id"))
            )
        if isinstance(value_moving, bool) and batch_lane.get("value_moving") != value_moving:
            errors.append("value_moving must match batch proof lane")
        if current_fallback and batch_lane.get("current_fallback") != current_fallback:
            errors.append(
                "current_fallback must match batch proof lane: "
                + str(batch_lane.get("current_fallback"))
            )
        if batch_lane.get("status") != "open_real_proof_gap":
            errors.append("batch proof lane must remain open_real_proof_gap")

    if not isinstance(value_moving, bool):
        errors.append("value_moving must be boolean")
        value_moving = False
    if required_non_tau not in REQUIRED_SUBSTRATES - {"tau_guard"}:
        errors.append(f"required_non_tau_substrate has unsupported value: {required_non_tau}")
    if tau_can_close is not False:
        errors.append("tau_can_close_gap must be false for current real-proof gaps")
    if tau_status == "not_applicable" and _str_list(
        obligation.get("tau_evidence_paths"),
        "tau_evidence_paths",
        errors,
        allow_empty=True,
    ):
        errors.append("tau_evidence_paths must be empty when tau_status is not_applicable")
    elif tau_status != "not_applicable":
        _validate_existing_paths(
            obligation.get("tau_evidence_paths"),
            "tau_evidence_paths",
            repo_root,
            errors,
            allow_empty=False,
        )

    _validate_existing_paths(
        obligation.get("non_tau_evidence_paths"),
        "non_tau_evidence_paths",
        repo_root,
        errors,
        allow_empty=False,
    )
    public_fields = set(
        _str_list(
            obligation.get("required_public_input_fields"),
            "required_public_input_fields",
            errors,
        )
    )
    if value_moving is True:
        missing_fields = sorted(VALUE_MOVING_REQUIRED_PUBLIC_FIELDS - public_fields)
        if missing_fields:
            errors.append("value-moving required_public_input_fields missing: " + ",".join(missing_fields))
        if required_non_tau != "zkvm_execution":
            errors.append("value-moving real-proof gaps require zkvm_execution as the non-Tau substrate")
    _str(obligation.get("missing_proof"), "missing_proof", errors)
    limits = _str_list(obligation.get("limits"), "limits", errors)
    if len(limits) < 2:
        errors.append("limits must contain at least two items")
    if not tau_scope:
        errors.append("tau_scope must describe why Tau can or cannot apply")

    return {
        "proof_gap_id": proof_gap_id,
        "host_surface_id": host_surface_id,
        "value_moving": value_moving,
        "required_non_tau_substrate": required_non_tau,
        "tau_status": tau_status,
        "tau_can_close_gap": tau_can_close,
        "ok": not errors,
        "errors": errors,
    }


def _validate_unsupported_family_obligation(
    raw_obligation: Any,
    *,
    index: int,
    unsupported_entries: Mapping[str, Mapping[str, Any]],
    repo_root: Path,
) -> dict[str, Any]:
    del index
    errors: list[str] = []
    obligation = _mapping(raw_obligation, "unsupported_family_obligation", errors)
    unsupported_id = _str(obligation.get("unsupported_family_id"), "unsupported_family_id", errors)
    transition_family = _str(obligation.get("transition_family"), "transition_family", errors)
    profile_operation = _str(obligation.get("profile_operation"), "profile_operation", errors)
    value_moving = obligation.get("value_moving")
    current_authority = _str(obligation.get("current_authority"), "current_authority", errors)
    required_non_tau = _str(obligation.get("required_non_tau_substrate"), "required_non_tau_substrate", errors)
    tau_status = _str(obligation.get("tau_status"), "tau_status", errors)
    tau_can_admit = obligation.get("tau_can_admit_proof_required_profile")

    entry = unsupported_entries.get(unsupported_id)
    if entry is None:
        errors.append(f"unsupported_family_id missing from transition closure: {unsupported_id}")
    else:
        if transition_family and entry.get("transition_family") != transition_family:
            errors.append(
                "transition_family must match transition closure: "
                + str(entry.get("transition_family"))
            )
        if profile_operation and entry.get("profile_operation") != profile_operation:
            errors.append(
                "profile_operation must match transition closure: "
                + str(entry.get("profile_operation"))
            )
    if not isinstance(value_moving, bool):
        errors.append("value_moving must be boolean")
        value_moving = False
    if current_authority != "fail_closed_profile_gate":
        errors.append("current_authority must be fail_closed_profile_gate")
    if required_non_tau != "zkvm_execution":
        errors.append("unsupported proof-required families require zkvm_execution for proof admission")
    if tau_can_admit is not False:
        errors.append("tau_can_admit_proof_required_profile must be false")
    if tau_status == "not_applicable" and _str_list(
        obligation.get("tau_evidence_paths"),
        "tau_evidence_paths",
        errors,
        allow_empty=True,
    ):
        errors.append("tau_evidence_paths must be empty when tau_status is not_applicable")
    elif tau_status != "not_applicable":
        _validate_existing_paths(
            obligation.get("tau_evidence_paths"),
            "tau_evidence_paths",
            repo_root,
            errors,
            allow_empty=True,
        )
    _validate_existing_paths(
        obligation.get("fail_closed_evidence_paths"),
        "fail_closed_evidence_paths",
        repo_root,
        errors,
        allow_empty=False,
    )
    _str(obligation.get("missing_proof"), "missing_proof", errors)
    limits = _str_list(obligation.get("limits"), "limits", errors)
    if len(limits) < 2:
        errors.append("limits must contain at least two items")

    return {
        "unsupported_family_id": unsupported_id,
        "transition_family": transition_family,
        "profile_operation": profile_operation,
        "value_moving": value_moving,
        "required_non_tau_substrate": required_non_tau,
        "tau_status": tau_status,
        "tau_can_admit_proof_required_profile": tau_can_admit,
        "ok": not errors,
        "errors": errors,
    }


def _load_proof_gap_ids(path: Path, errors: list[str]) -> set[str]:
    try:
        matrix = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"proof matrix load failed: {exc}")
        return set()
    gaps = _list(_mapping(matrix, "proof matrix", errors).get("gap_surfaces"), "proof_matrix.gap_surfaces", errors)
    return {item["id"] for item in gaps if isinstance(item, Mapping) and isinstance(item.get("id"), str)}


def _load_batch_gap_lanes(path: Path, errors: list[str]) -> dict[str, Mapping[str, Any]]:
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"batch proof manifest load failed: {exc}")
        return {}
    lanes = _list(
        _mapping(manifest, "batch proof manifest", errors).get("proof_gap_batch_lanes"),
        "proof_gap_batch_lanes",
        errors,
    )
    out: dict[str, Mapping[str, Any]] = {}
    for lane in lanes:
        if isinstance(lane, Mapping) and isinstance(lane.get("proof_gap_id"), str):
            out[lane["proof_gap_id"]] = lane
    return out


def _load_unsupported_entries(path: Path, errors: list[str]) -> dict[str, Mapping[str, Any]]:
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"transition closure manifest load failed: {exc}")
        return {}
    entries = _list(
        _mapping(manifest, "transition closure manifest", errors).get("unsupported_proof_required_families"),
        "unsupported_proof_required_families",
        errors,
    )
    out: dict[str, Mapping[str, Any]] = {}
    for entry in entries:
        if isinstance(entry, Mapping) and isinstance(entry.get("id"), str):
            out[entry["id"]] = entry
    return out


def _load_spot_not_covered_operations(path: Path, errors: list[str]) -> set[str]:
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"host coverage manifest load failed: {exc}")
        return set()
    surfaces = _list(
        _mapping(manifest, "host coverage manifest", errors).get("critical_surfaces"),
        "critical_surfaces",
        errors,
    )
    for surface in surfaces:
        if isinstance(surface, Mapping) and surface.get("id") == "spot_v1_risc0_supported_transition_kernel":
            return set(_str_list(surface.get("not_covered_operations"), "spot.not_covered_operations", errors))
    errors.append("host coverage missing spot_v1_risc0_supported_transition_kernel")
    return set()


def _validate_existing_paths(
    value: Any,
    name: str,
    repo_root: Path,
    errors: list[str],
    *,
    allow_empty: bool,
) -> list[str]:
    paths = _str_list(value, name, errors, allow_empty=allow_empty)
    if not paths and not allow_empty:
        errors.append(f"{name} must be non-empty")
    for rel_path in paths:
        candidate = (repo_root / rel_path).resolve()
        try:
            candidate.relative_to(repo_root.resolve())
        except ValueError:
            errors.append(f"{name} contains path outside repo: {rel_path}")
            continue
        if not candidate.exists():
            errors.append(f"{name} missing: {rel_path}")
    return paths


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
    if not items and not allow_empty:
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
    parser.add_argument("--proof-matrix", type=Path, default=DEFAULT_PROOF_MATRIX)
    parser.add_argument("--batch-proof", type=Path, default=DEFAULT_BATCH_PROOF)
    parser.add_argument("--transition-closure", type=Path, default=DEFAULT_TRANSITION_CLOSURE)
    parser.add_argument("--host-coverage", type=Path, default=DEFAULT_HOST_COVERAGE)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = validate_proof_substrate_obligations_v0(
        json.loads(args.manifest.read_text(encoding="utf-8")),
        proof_matrix_path=args.proof_matrix,
        batch_proof_path=args.batch_proof,
        transition_closure_path=args.transition_closure,
        host_coverage_path=args.host_coverage,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
