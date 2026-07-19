#!/usr/bin/env python3
"""Validate ZenoDEX deployment profile files."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Mapping

import yaml  # type: ignore[import-untyped]

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILE_DIR = ROOT / "config" / "deploy"
SCHEMA = "zenodex/deployment_profile/v1"
REPORT_SCHEMA = "zenodex/deployment_profiles_report/v1"
REQUIRED_PROFILES = ("local-dev", "public-testnet", "production-strict")
PRODUCTION_RUNTIME_POLICY: dict[str, bool] = {
    "allow_path_lookup": False,
    "plaintext_fixture_keys_allowed": False,
    "local_only_routes_allowed": False,
    "env_config_file_allowlist_required": True,
    "dependency_sbom_required": True,
    "secret_scan_required": True,
    "external_static_analysis_required_in_ci": True,
}
PRODUCTION_KEY_POLICY: dict[str, bool] = {
    "raw_private_key_flags_allowed": False,
    "production_key_receipts_required": True,
    "browser_key_generation_allowed": False,
    "external_signer_required": True,
    "signer_user_approval_required": True,
}
STRICT_PERPS_POLICY: dict[str, bool] = {
    "isolated_partial_liquidate_tau_source_binding_required": True,
    "isolated_partial_liquidate_tau_source_state_root_binding_required": True,
    "isolated_partial_liquidate_tau_source_membership_proof_required": True,
    "isolated_partial_liquidate_tau_source_root_authority_required": True,
    "isolated_partial_liquidate_tau_source_admission_envelope_required": True,
    "isolated_partial_liquidate_tau_source_authority_policy_receipt_required": True,
    "isolated_partial_liquidate_tau_source_authority_policy_receipt_verifier_required": True,
    "isolated_partial_liquidate_tau_source_authority_policy_receipt_verifier_sha256_required": True,
    "isolated_partial_liquidate_tau_source_authority_policy_receipt_verifier_build_receipt_required": True,
    "isolated_partial_liquidate_tau_source_authority_policy_receipt_verifier_build_receipt_signature_required": True,
    "isolated_partial_liquidate_tau_source_authority_policy_receipt_verifier_release_bundle_required": True,
    "isolated_partial_liquidate_tau_source_authority_policy_receipt_verifier_release_registry_required": True,
}
STRICT_SPOT_POLICY: dict[str, bool] = {
    "route_price_interval_trusted_policy_root_required": True,
    "route_price_interval_trusted_policy_root_bundle_required": True,
    "route_price_interval_trusted_policy_root_bundle_quorum_required": True,
    "route_price_interval_max_width_bps_required": True,
}


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _require_bool(obj: Mapping[str, Any], key: str, errors: list[str], prefix: str) -> bool | None:
    value = obj.get(key)
    if not isinstance(value, bool):
        errors.append(f"{prefix}.{key} must be bool")
        return None
    return value


def validate_deployment_profile(profile: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(profile, "profile", errors)
    if obj.get("schema") != SCHEMA:
        errors.append("schema mismatch")
    profile_id = obj.get("profile_id")
    if not isinstance(profile_id, str) or not profile_id:
        errors.append("profile_id must be a non-empty string")
        profile_id = ""
    if not isinstance(obj.get("threat_model"), str) or not obj.get("threat_model"):
        errors.append("threat_model must be a non-empty string")
    routes = obj.get("allowed_routes")
    if not isinstance(routes, list) or not routes or not all(isinstance(item, str) and item for item in routes):
        errors.append("allowed_routes must be a non-empty string list")

    for key in (
        "required_auth",
        "key_policy",
        "proof_policy",
        "spot_policy",
        "runtime_policy",
        "perps_policy",
        "peer_policy",
        "gossip_policy",
        "observability_policy",
    ):
        _mapping(obj.get(key), key, errors)

    key_policy = _mapping(obj.get("key_policy"), "key_policy", errors)
    proof_policy = _mapping(obj.get("proof_policy"), "proof_policy", errors)
    spot_policy = _mapping(obj.get("spot_policy"), "spot_policy", errors)
    runtime_policy = _mapping(obj.get("runtime_policy"), "runtime_policy", errors)
    perps_policy = _mapping(obj.get("perps_policy"), "perps_policy", errors)
    peer_policy = _mapping(obj.get("peer_policy"), "peer_policy", errors)
    gossip_policy = _mapping(obj.get("gossip_policy"), "gossip_policy", errors)
    observability_policy = _mapping(obj.get("observability_policy"), "observability_policy", errors)

    raw_keys = _require_bool(key_policy, "raw_private_key_flags_allowed", errors, "key_policy")
    _require_bool(key_policy, "production_key_receipts_required", errors, "key_policy")
    browser_keygen = _require_bool(key_policy, "browser_key_generation_allowed", errors, "key_policy")
    proof_required = _require_bool(proof_policy, "proof_metadata_required", errors, "proof_policy")
    dynamic_peer_cap = _require_bool(peer_policy, "dynamic_peer_cap_required", errors, "peer_policy")
    transport_auth = _require_bool(gossip_policy, "transport_auth_required", errors, "gossip_policy")
    metrics_required = _require_bool(observability_policy, "metrics_required", errors, "observability_policy")
    runtime_allow_path_lookup = _require_bool(
        runtime_policy, "allow_path_lookup", errors, "runtime_policy"
    )

    upba_policy = obj.get("upba_policy")
    if upba_policy not in {"conservative", "balanced", "fast"}:
        errors.append("upba_policy must be conservative, balanced, or fast")

    if profile_id == "production-strict":
        if raw_keys is not False:
            errors.append("production-strict must reject raw private key flags")
        for key, expected in PRODUCTION_KEY_POLICY.items():
            if key_policy.get(key) is not expected:
                errors.append(
                    f"production-strict key_policy.{key} must be {str(expected).lower()}"
                )
        if proof_required is not True:
            errors.append("production-strict must require proof metadata")
        for key, expected in PRODUCTION_RUNTIME_POLICY.items():
            if runtime_policy.get(key) is not expected:
                errors.append(
                    f"production-strict runtime_policy.{key} must be {str(expected).lower()}"
                )
        for key, expected in STRICT_PERPS_POLICY.items():
            if perps_policy.get(key) is not expected:
                errors.append(
                    f"production-strict perps_policy.{key} must be {str(expected).lower()}"
                )
        for key, expected in STRICT_SPOT_POLICY.items():
            if spot_policy.get(key) is not expected:
                errors.append(
                    f"production-strict spot_policy.{key} must be {str(expected).lower()}"
                )
        if dynamic_peer_cap is not True:
            errors.append("production-strict must require dynamic peer cap")
        if transport_auth is not True:
            errors.append("production-strict must require transport auth")
        if metrics_required is not True:
            errors.append("production-strict must require metrics")
        if upba_policy != "conservative":
            errors.append("production-strict must use conservative UPBA policy")

    if profile_id == "public-testnet" and raw_keys is not False:
        errors.append("public-testnet must reject raw private key flags")
    if profile_id == "public-testnet":
        for key, expected in STRICT_SPOT_POLICY.items():
            if spot_policy.get(key) is not expected:
                errors.append(
                    f"public-testnet spot_policy.{key} must be {str(expected).lower()}"
                )
        if browser_keygen is not False:
            errors.append("public-testnet must disable browser key generation")
        if runtime_allow_path_lookup is not False:
            errors.append("public-testnet must disable runtime path lookup")

    return {
        "profile_id": profile_id,
        "ok": not errors,
        "errors": errors,
    }


def validate_profile_dir(profile_dir: Path = DEFAULT_PROFILE_DIR) -> dict[str, Any]:
    errors: list[str] = []
    profiles: dict[str, dict[str, Any]] = {}
    reports: list[dict[str, Any]] = []
    for path in sorted(profile_dir.glob("*.yaml")):
        try:
            payload = yaml.safe_load(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, yaml.YAMLError) as exc:  # pragma: no cover
            reports.append({"path": str(path), "profile_id": "", "ok": False, "errors": [f"parse failed: {exc}"]})
            continue
        report = validate_deployment_profile(payload)
        report["path"] = str(path)
        reports.append(report)
        if report["profile_id"]:
            if report["profile_id"] in profiles:
                errors.append(f"duplicate profile_id: {report['profile_id']}")
            profiles[report["profile_id"]] = report
        errors.extend(f"{path.name}: {error}" for error in report["errors"])
    for required in REQUIRED_PROFILES:
        if required not in profiles:
            errors.append(f"missing required profile: {required}")
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "profile_dir": str(profile_dir),
        "errors": errors,
        "profiles": reports,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile-dir", type=Path, default=DEFAULT_PROFILE_DIR)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = validate_profile_dir(args.profile_dir)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        for item in report["profiles"]:
            status = "ok" if item["ok"] else "fail"
            print(f"{item['profile_id'] or item['path']}: {status}")
            for error in item["errors"]:
                print(f"  error: {error}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
