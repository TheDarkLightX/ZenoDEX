#!/usr/bin/env python3
"""Validate ZenoLedger proof profile bindings."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILES = ROOT / "config" / "proof_profiles" / "zeno_ledger_profiles.json"
SCHEMA = "zenodex/zeno_ledger/proof_profiles/v1"
REPORT_SCHEMA = "zenodex/zeno_ledger/proof_profiles_report/v1"
REQUIRED_PROFILES = {
    "spot_v1_single_pool_success",
    "spot_v2_upba",
    "ingress_v1",
    "recursive_epoch_v1",
}
REQUIRED_PROFILE_COVERAGE = {
    "spot_v1_single_pool_success": {"swap_exact_in", "accepted_receipts_root"},
    "spot_v2_upba": {"upba_batch_clearing_inside_guest", "bounded_grid_certificate_verification"},
    "ingress_v1": {"rejected_receipts", "production_admission_semantics"},
    "recursive_epoch_v1": {"transaction_proof_aggregation", "block_level_receipt"},
}


def validate_proof_profiles_v1(registry: Any, *, repo_root: Path = ROOT) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(registry, "registry", errors)
    if obj.get("schema") != SCHEMA:
        errors.append("schema mismatch")
    matrix_path_value = obj.get("coverage_matrix_path")
    matrix_hash = obj.get("coverage_matrix_sha256")
    if not isinstance(matrix_path_value, str) or not matrix_path_value:
        errors.append("coverage_matrix_path must be a non-empty string")
        matrix_path = repo_root / "missing"
    else:
        matrix_path = repo_root / matrix_path_value
    if not isinstance(matrix_hash, str) or len(matrix_hash) != 64:
        errors.append("coverage_matrix_sha256 must be a 64-character hex string")
    elif matrix_path.exists():
        actual = hashlib.sha256(matrix_path.read_bytes()).hexdigest()
        if actual != matrix_hash:
            errors.append("coverage_matrix_sha256 mismatch")
    else:
        errors.append("coverage matrix path missing")

    raw_profiles = obj.get("profiles")
    if not isinstance(raw_profiles, list) or not raw_profiles:
        errors.append("profiles must be a non-empty list")
        raw_profiles = []

    seen: set[str] = set()
    profile_reports: list[dict[str, Any]] = []
    for index, raw in enumerate(raw_profiles):
        item_errors: list[str] = []
        profile = _mapping(raw, f"profiles[{index}]", item_errors)
        profile_id = _string(profile.get("profile_id"), "profile_id", item_errors)
        covered = _string_set(profile.get("covered"), "covered", item_errors)
        not_covered = _string_set(profile.get("not_covered"), "not_covered", item_errors)
        non_claims = _string_set(profile.get("non_claims"), "non_claims", item_errors)
        if profile_id:
            if profile_id in seen:
                item_errors.append("duplicate profile_id")
            seen.add(profile_id)
            required = REQUIRED_PROFILE_COVERAGE.get(profile_id, set())
            missing = sorted(required - covered)
            if missing:
                item_errors.append(f"missing required coverage: {','.join(missing)}")
        if not_covered and not non_claims:
            item_errors.append("profiles with not_covered entries must include non_claims")
        if covered & not_covered:
            item_errors.append("covered and not_covered entries must be disjoint")
        profile_reports.append(
            {
                "profile_id": profile_id,
                "ok": not item_errors,
                "covered_count": len(covered),
                "not_covered_count": len(not_covered),
                "non_claim_count": len(non_claims),
                "errors": item_errors,
            }
        )
        errors.extend(f"profiles[{index}]: {error}" for error in item_errors)

    missing_profiles = sorted(REQUIRED_PROFILES - seen)
    if missing_profiles:
        errors.append(f"missing required profiles: {','.join(missing_profiles)}")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "profile_count": len(raw_profiles),
        "profiles": profile_reports,
    }


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _string(value: Any, name: str, errors: list[str]) -> str:
    if not isinstance(value, str) or not value:
        errors.append(f"{name} must be a non-empty string")
        return ""
    return value


def _string_set(value: Any, name: str, errors: list[str]) -> set[str]:
    if not isinstance(value, list) or not value:
        errors.append(f"{name} must be a non-empty list")
        return set()
    out: set[str] = set()
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item:
            errors.append(f"{name}[{index}] must be a non-empty string")
        else:
            out.add(item)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profiles", type=Path, default=DEFAULT_PROFILES)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = validate_proof_profiles_v1(json.loads(args.profiles.read_text(encoding="utf-8")))
    print(json.dumps(report, indent=2 if args.json else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
