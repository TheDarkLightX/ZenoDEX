#!/usr/bin/env python3
"""Validate UPBA policy profile files."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILE_DIR = ROOT / "config" / "upba"
SCHEMA = "zenodex/upba_policy_profile/v1"
REPORT_SCHEMA = "zenodex/upba_policy_profiles_report/v1"
ORDER = ("conservative", "balanced", "fast")


def validate_upba_policy_profile_v1(profile: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(profile, "profile", errors)
    if obj.get("schema") != SCHEMA:
        errors.append("schema mismatch")
    profile_id = obj.get("profile_id")
    if profile_id not in ORDER:
        errors.append("profile_id must be conservative, balanced, or fast")
        profile_id = ""

    int_fields = (
        "max_relative_loss_ppm",
        "max_absolute_loss_atoms",
        "fill_quantum_atoms",
        "candidate_evaluation_count",
        "max_trade_fraction_ppm",
    )
    ints: dict[str, int] = {}
    for field in int_fields:
        value = obj.get(field)
        if isinstance(value, int) and not isinstance(value, bool) and value > 0:
            ints[field] = value
        else:
            errors.append(f"{field} must be a positive integer")

    bools: dict[str, bool] = {}
    for field in (
        "proof_required",
        "energy_scorer_allowed",
        "energy_may_omit_candidates",
        "energy_omit_requires_certificate",
        "fallback_required",
        "user_warning_required",
    ):
        value = obj.get(field)
        if isinstance(value, bool):
            bools[field] = value
        else:
            errors.append(f"{field} must be bool")

    if bools.get("energy_may_omit_candidates") and not bools.get("energy_omit_requires_certificate"):
        errors.append("energy omission requires deterministic suffix-bound or selected-set certificate")
    if bools.get("energy_scorer_allowed") and bools.get("energy_may_omit_candidates"):
        errors.append("default ZenoEnergy policy must be order-only")
    if bools.get("proof_required") is not True:
        errors.append("UPBA policy profiles must require proof")
    if bools.get("fallback_required") is not True:
        errors.append("UPBA policy profiles must require fallback")
    if ints.get("max_trade_fraction_ppm", 0) > 1_000_000:
        errors.append("max_trade_fraction_ppm must be <= 1000000")

    return {
        "profile_id": profile_id,
        "ok": not errors,
        "errors": errors,
        "integers": ints,
    }


def validate_upba_policy_dir_v1(profile_dir: Path = DEFAULT_PROFILE_DIR) -> dict[str, Any]:
    errors: list[str] = []
    reports: dict[str, dict[str, Any]] = {}
    for path in sorted(profile_dir.glob("policy_*.json")):
        report = validate_upba_policy_profile_v1(json.loads(path.read_text(encoding="utf-8")))
        report["path"] = str(path)
        if report["profile_id"] in reports:
            errors.append(f"duplicate profile_id: {report['profile_id']}")
        if report["profile_id"]:
            reports[report["profile_id"]] = report
        errors.extend(f"{path.name}: {error}" for error in report["errors"])
    for profile_id in ORDER:
        if profile_id not in reports:
            errors.append(f"missing profile: {profile_id}")
    if all(profile_id in reports for profile_id in ORDER):
        _check_monotonic(reports, errors)
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "profiles": [reports[key] for key in ORDER if key in reports],
    }


def _check_monotonic(reports: Mapping[str, Mapping[str, Any]], errors: list[str]) -> None:
    stricter_to_looser = [reports[key]["integers"] for key in ORDER]
    increasing_fields = ("max_relative_loss_ppm", "max_absolute_loss_atoms", "fill_quantum_atoms", "max_trade_fraction_ppm")
    decreasing_fields = ("candidate_evaluation_count",)
    for field in increasing_fields:
        values = [item[field] for item in stricter_to_looser]
        if values != sorted(values):
            errors.append(f"{field} must increase from conservative to fast")
    for field in decreasing_fields:
        values = [item[field] for item in stricter_to_looser]
        if values != sorted(values, reverse=True):
            errors.append(f"{field} must decrease from conservative to fast")


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile-dir", type=Path, default=DEFAULT_PROFILE_DIR)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = validate_upba_policy_dir_v1(args.profile_dir)
    print(json.dumps(report, indent=2 if args.json else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
