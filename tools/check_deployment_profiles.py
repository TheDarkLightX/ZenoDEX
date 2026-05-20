"""Fail-closed checks for deployment profile documents."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping


def validate_deployment_profile(profile: Mapping[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    profile_id = str(profile.get("profile_id", ""))
    if profile.get("schema") != "zenodex/deployment_profile/v1":
        errors.append("schema must be zenodex/deployment_profile/v1")
    if not profile_id:
        errors.append("profile_id must be non-empty")

    key_policy = profile.get("key_policy")
    if not isinstance(key_policy, Mapping):
        errors.append("key_policy must be an object")
    elif profile_id == "production-strict":
        if key_policy.get("raw_private_key_flags_allowed") is not False:
            errors.append("production-strict must reject raw private key flags")
        if key_policy.get("production_key_receipts_required") is not True:
            errors.append("production-strict must require production key receipts")

    required_auth = profile.get("required_auth")
    if not isinstance(required_auth, Mapping):
        errors.append("required_auth must be an object")
    proof_policy = profile.get("proof_policy")
    if not isinstance(proof_policy, Mapping):
        errors.append("proof_policy must be an object")
    peer_policy = profile.get("peer_policy")
    if not isinstance(peer_policy, Mapping):
        errors.append("peer_policy must be an object")

    return {
        "schema": "zenodex/deployment_profile_check/v1",
        "profile_id": profile_id,
        "ok": not errors,
        "errors": errors,
    }


def validate_profile_dir(path: Path) -> dict[str, Any]:
    errors: list[str] = []
    profiles: list[dict[str, Any]] = []
    if not path.exists():
        return {
            "schema": "zenodex/deployment_profile_dir_check/v1",
            "path": str(path),
            "ok": False,
            "profiles": [],
            "errors": [f"profile directory missing: {path}"],
        }

    for profile_path in sorted(path.glob("*.json")):
        try:
            value = json.loads(profile_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            errors.append(f"{profile_path.name}: invalid json: {exc}")
            continue
        if not isinstance(value, Mapping):
            errors.append(f"{profile_path.name}: profile must be an object")
            continue
        report = validate_deployment_profile(value)
        profiles.append({**report, "path": str(profile_path)})
        errors.extend(f"{profile_path.name}: {error}" for error in report["errors"])

    expected = {"local-dev", "public-testnet", "production-strict"}
    found = {str(profile.get("profile_id", "")) for profile in profiles}
    missing = sorted(expected - found)
    errors.extend(f"missing deployment profile: {profile_id}" for profile_id in missing)
    return {
        "schema": "zenodex/deployment_profile_dir_check/v1",
        "path": str(path),
        "ok": not errors,
        "profiles": profiles,
        "errors": errors,
    }
