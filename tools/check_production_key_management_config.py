#!/usr/bin/env python3
"""Validate production key-management configuration files."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.production_key_management_v0 import (
    DEFAULT_ACTION_POLICIES_V0,
    build_action_policy_v0,
    validate_action_policy_v0,
    validate_key_descriptor_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0


CONFIG_SCHEMA_V0 = "zenodex.production_key_management.config.v0"
RESULT_SCHEMA_V0 = "zenodex.production_key_management.config_check.v1"


def config_content_hash_v0(config: Mapping[str, Any]) -> str:
    body = dict(config)
    body.pop("config_hash", None)
    return hash_v0("production_key_management_config_v0", body)


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _require_mapping(value: object, *, name: str, errors: list[str]) -> Mapping[str, Any] | None:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be a JSON object")
        return None
    return value


def _require_list(value: object, *, name: str, errors: list[str]) -> list[Any]:
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return []
    return value


def _policy_strength_errors(*, action: str, policy: Mapping[str, Any], default: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if policy.get("action") != action:
        errors.append(f"{action}: policy action mismatch")
    if policy.get("role") != default.get("role"):
        errors.append(f"{action}: policy role differs from default")
    if default.get("critical") is True and policy.get("critical") is not True:
        errors.append(f"{action}: policy weakens critical flag")
    if int(policy.get("threshold", -1)) < int(default.get("threshold", 0)):
        errors.append(f"{action}: policy weakens threshold")
    if int(policy.get("min_distinct_custodians", -1)) < int(default.get("min_distinct_custodians", 0)):
        errors.append(f"{action}: policy weakens distinct-custodian threshold")
    for field in ("hardware_required", "timelock_required", "transparency_required"):
        if default.get(field) is True and policy.get(field) is not True:
            errors.append(f"{action}: policy weakens {field}")
    if policy.get("break_glass_allowed") is True and default.get("break_glass_allowed") is not True:
        errors.append(f"{action}: policy expands break-glass scope")
    return errors


def _active_production_keys_for_role(keys: list[Mapping[str, Any]], role: str) -> list[Mapping[str, Any]]:
    return [
        key
        for key in keys
        if key.get("role") == role and key.get("environment") == "production" and key.get("status") == "active"
    ]


def _policy_quorum_errors(*, action: str, policy: Mapping[str, Any], keys: list[Mapping[str, Any]]) -> list[str]:
    role_keys = _active_production_keys_for_role(keys, str(policy["role"]))
    threshold = int(policy["threshold"])
    min_distinct = int(policy["min_distinct_custodians"])
    if len(role_keys) < threshold:
        return [f"{action}: insufficient active production keys for threshold"]
    if len({str(key["custodian_id"]) for key in role_keys}) < min_distinct:
        return [f"{action}: insufficient active production custodians for quorum"]
    if policy.get("hardware_required") is True:
        non_software = [key for key in role_keys if key.get("storage_class") in {"hardware", "hsm", "mpc"}]
        if len(non_software) < threshold or len({str(key["custodian_id"]) for key in non_software}) < min_distinct:
            return [f"{action}: insufficient non-software custody quorum"]
    return []


def _apply_rotation(keys: list[Mapping[str, Any]], rotation: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    revoke_ids = {str(key_id) for key_id in _require_list(rotation.get("revoke_key_ids"), name="rotation.revoke_key_ids", errors=[])}
    add_keys = _require_list(rotation.get("add_keys"), name="rotation.add_keys", errors=[])
    next_keys: list[Mapping[str, Any]] = []
    for key in keys:
        if str(key.get("key_id")) in revoke_ids:
            updated = dict(key)
            updated["status"] = "revoked"
            updated["key_descriptor_hash"] = hash_v0(
                "production_key_descriptor_v0",
                {k: v for k, v in updated.items() if k != "key_descriptor_hash"},
            )
            next_keys.append(updated)
        else:
            next_keys.append(dict(key))
    next_keys.extend(dict(key) for key in add_keys if isinstance(key, Mapping))
    return next_keys


def validate_config(config: Mapping[str, Any], *, policy_model: Mapping[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []
    summaries: dict[str, Any] = {}

    obj = _require_mapping(config, name="config", errors=errors)
    if obj is None:
        return {
            "schema": RESULT_SCHEMA_V0,
            "ok": False,
            "errors": errors,
            "warnings": warnings,
            "config_hash": None,
            "actions": summaries,
        }
    expected_keys = {
        "schema",
        "environment",
        "config_hash",
        "policies",
        "keys",
        "revoked_key_ids",
        "signer_rotations",
        "recovery_policies",
    }
    if set(obj.keys()) != expected_keys:
        errors.append("config keys mismatch")
    if obj.get("schema") != CONFIG_SCHEMA_V0:
        errors.append("config schema mismatch")
    if obj.get("environment") != "production":
        errors.append("config environment must be production")
    config_hash = config_content_hash_v0(obj)
    if obj.get("config_hash") != config_hash:
        errors.append("config_hash mismatch")

    raw_policies = _require_mapping(obj.get("policies"), name="config.policies", errors=errors) or {}
    raw_keys = _require_list(obj.get("keys"), name="config.keys", errors=errors)
    revoked_key_ids = {str(key_id) for key_id in _require_list(obj.get("revoked_key_ids"), name="config.revoked_key_ids", errors=errors)}
    signer_rotations = _require_list(obj.get("signer_rotations"), name="config.signer_rotations", errors=errors)
    recovery_policies = _require_mapping(obj.get("recovery_policies"), name="config.recovery_policies", errors=errors) or {}

    default_model_policies = policy_model.get("action_policies")
    if not isinstance(default_model_policies, Mapping):
        errors.append("policy_model action_policies must be a JSON object")
        default_model_policies = {}

    policies: dict[str, Mapping[str, Any]] = {}
    for action, default_policy in DEFAULT_ACTION_POLICIES_V0.items():
        raw_policy = raw_policies.get(action)
        if not isinstance(raw_policy, Mapping):
            errors.append(f"{action}: missing policy")
            continue
        try:
            validate_action_policy_v0(raw_policy)
        except Exception as exc:
            errors.append(f"{action}: invalid policy: {exc}")
            continue
        model_default = default_model_policies.get(action)
        if not isinstance(model_default, Mapping):
            errors.append(f"{action}: missing policy in policy model")
            continue
        model_default_policy = build_action_policy_v0(action=action, **dict(model_default))
        errors.extend(_policy_strength_errors(action=action, policy=raw_policy, default=model_default_policy))
        policies[action] = raw_policy

    if set(raw_policies.keys()) - set(DEFAULT_ACTION_POLICIES_V0.keys()):
        errors.append("config contains unknown action policy")

    keys: list[Mapping[str, Any]] = []
    seen_key_ids: set[str] = set()
    for index, raw_key in enumerate(raw_keys):
        if not isinstance(raw_key, Mapping):
            errors.append(f"keys[{index}] must be a JSON object")
            continue
        try:
            validate_key_descriptor_v0(raw_key)
        except Exception as exc:
            errors.append(f"keys[{index}] invalid: {exc}")
            continue
        key_id = str(raw_key["key_id"])
        if key_id in seen_key_ids:
            errors.append(f"keys[{index}] duplicate key_id")
        seen_key_ids.add(key_id)
        if raw_key["status"] == "revoked" and key_id not in revoked_key_ids:
            errors.append(f"{key_id}: revoked key missing from revocation log")
        if key_id in revoked_key_ids and raw_key["status"] == "active":
            errors.append(f"{key_id}: revoked key cannot be active")
        if raw_key["storage_class"] == "mpc" and not raw_key.get("recovery_policy_hash"):
            errors.append(f"{key_id}: mpc key requires non-secret recovery_policy_hash")
        if raw_key.get("custody_model") == "sss_recovery_only" and raw_key["status"] == "active":
            errors.append(f"{key_id}: Shamir recovery-only key cannot be active signer")
        keys.append(raw_key)

    recovery_hashes = set(recovery_policies.keys())
    for key in keys:
        recovery_hash = key.get("recovery_policy_hash")
        if recovery_hash is not None and str(recovery_hash) not in recovery_hashes:
            warnings.append(f"{key['key_id']}: recovery_policy_hash has no local recovery policy detail")

    for action, policy in policies.items():
        action_errors = _policy_quorum_errors(action=action, policy=policy, keys=keys)
        errors.extend(action_errors)
        summaries[action] = {
            "role": policy["role"],
            "threshold": policy["threshold"],
            "min_distinct_custodians": policy["min_distinct_custodians"],
            "quorum_ok": not action_errors,
        }

    for index, raw_rotation in enumerate(signer_rotations):
        rotation = _require_mapping(raw_rotation, name=f"signer_rotations[{index}]", errors=errors)
        if rotation is None:
            continue
        next_keys = _apply_rotation(keys, rotation)
        for action, policy in policies.items():
            for error in _policy_quorum_errors(action=action, policy=policy, keys=next_keys):
                errors.append(f"signer_rotations[{index}] would break future quorum: {error}")

    return {
        "schema": RESULT_SCHEMA_V0,
        "ok": not errors,
        "errors": errors,
        "warnings": warnings,
        "config_hash": config_hash,
        "actions": summaries,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--policy-model", required=True, type=Path)
    args = parser.parse_args(argv)

    result = validate_config(_load_json(args.config), policy_model=_load_json(args.policy_model))
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
