#!/usr/bin/env python3
"""Check a production-candidate ZenoProof verifier governance policy."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(1, str(TOOLS))

from zenoproof_reward_payout_replay import build_status as build_reward_payout_status  # noqa: E402
from zenoproof_verify import (  # noqa: E402
    REGISTRY_SCHEMA,
    sha256_json,
    verify_registry_manifest,
)


POLICY_SCHEMA = "zenodex.zenoproof.production_governance_policy.v1"
REPORT_SCHEMA = "zenodex.zenoproof.production_governance_policy_check.v1"
DEFAULT_REGISTRY = ROOT / "tools" / "zenoproof_registry_manifest.json"
ADDRESS_RE = re.compile(r"^0x[0-9a-fA-F]{40}$")
SHA_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOP_LEVEL_KEYS = {
    "schema",
    "policy_id",
    "policy_name",
    "environment",
    "registry_manifest_path",
    "registry_manifest_id",
    "governance",
    "code_signing",
    "sandbox",
    "revocation",
    "verifier_policy",
    "oracle_bridge_policy",
    "reward_settlement",
    "not_claimed",
}
GOVERNANCE_KEYS = {
    "contract_address",
    "policy_epoch",
    "timelock_seconds",
    "verifier_onboarding_quorum",
    "verifier_revocation_quorum",
    "emergency_pause_role",
    "governance_approval_receipt",
    "governance_execution_receipt",
}
CODE_SIGNING_KEYS = {
    "required",
    "scheme",
    "release_signer_identity",
    "artifact_digest_alg",
    "policy_bundle_digest",
}
SANDBOX_KEYS = {
    "required",
    "deterministic_worker_image_digest",
    "seccomp_profile_digest",
    "network_disabled",
    "filesystem_readonly",
    "max_input_bytes",
    "max_timeout_ms",
}
REVOCATION_KEYS = {
    "enabled",
    "revocation_list_receipt",
    "emergency_revocation_enabled",
    "revocation_drill_receipt",
    "max_revocation_delay_seconds",
}
VERIFIER_POLICY_KEYS = {
    "forbidden_execution_modes",
    "devnet_only_verifier_ids",
    "production_enabled_verifier_ids",
    "min_production_verifiers",
    "min_distinct_proof_kinds",
    "path_lookup_mode",
}
ORACLE_BRIDGE_KEYS = {
    "o3_receipt_required",
    "o5_independence_witness_required",
    "min_o5_distinct_verifier_count",
    "min_o5_distinct_proof_kind_count",
    "registry_dag_dependency_required",
}
REWARD_SETTLEMENT_KEYS = {
    "bounded_pool_required",
    "no_minting_required",
    "live_payout_enabled",
    "reward_payout_replay_required",
    "token_settlement_policy_id",
}
REQUIRED_NOT_CLAIMS = {
    "does_not_claim_live_proof_network",
    "does_not_claim_governance_revocation_live",
    "does_not_claim_production_verifier_sandbox_deployed",
    "does_not_claim_live_proof_mining_payouts",
    "does_not_claim_reporter_or_prover_honesty",
}
STATIC_EXECUTION_MODES = {"local_static_accept"}
PRODUCTION_EXECUTION_MODES = {"subprocess_json"}
BASE_GO_LIVE_BLOCKERS = [
    "proof_governance_execution_not_verified_onchain",
    "production_verifier_code_signing_not_verified",
    "production_verifier_sandbox_not_deployed",
    "revocation_drill_not_replayed_on_live_registry",
    "proof_network_public_soak_not_completed",
]


def _canonical_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def policy_content_hash(policy: Mapping[str, Any]) -> str:
    payload = dict(policy)
    payload.pop("policy_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def _sha(label: str) -> str:
    return "sha256:" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must be a JSON object")
    return obj


def _is_sha(value: Any) -> bool:
    return isinstance(value, str) and SHA_RE.fullmatch(value) is not None


def _is_address(value: Any) -> bool:
    return isinstance(value, str) and ADDRESS_RE.fullmatch(value) is not None


def _unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], label: str, errors: list[str]) -> None:
    for key in obj:
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _obj_field(obj: Mapping[str, Any], key: str, errors: list[str]) -> Mapping[str, Any]:
    value = obj.get(key)
    if not isinstance(value, Mapping):
        errors.append(f"{key}_must_be_object")
        return {}
    return value


def _string_list(obj: Mapping[str, Any], key: str, errors: list[str]) -> list[str]:
    value = obj.get(key)
    if not isinstance(value, list):
        errors.append(f"{key}_must_be_list")
        return []
    result: list[str] = []
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item.strip():
            errors.append(f"{key}_{index}_must_be_nonempty_string")
        else:
            result.append(item)
    return result


def _int_field(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int,
    maximum: int | None = None,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{key}_must_be_int")
        return None
    if value < minimum:
        errors.append(f"{key}_below_min:{minimum}")
    if maximum is not None and value > maximum:
        errors.append(f"{key}_above_max:{maximum}")
    return int(value)


def _bool_true(obj: Mapping[str, Any], key: str, errors: list[str]) -> None:
    value = obj.get(key)
    if not isinstance(value, bool):
        errors.append(f"{key}_must_be_bool")
    elif value is not True:
        errors.append(f"{key}_must_be_true")


def _registry_verifiers(registry: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    verifiers = registry.get("verifiers")
    if not isinstance(verifiers, list):
        return []
    return [verifier for verifier in verifiers if isinstance(verifier, Mapping)]


def _registry_id(registry: Mapping[str, Any]) -> str:
    return sha256_json(registry)


def _sample_registry() -> Mapping[str, Any]:
    return _load_json(DEFAULT_REGISTRY)


def sample_policy(registry: Mapping[str, Any] | None = None) -> dict[str, Any]:
    active_registry = dict(registry or _sample_registry())
    verifiers = _registry_verifiers(active_registry)
    devnet_only = sorted(
        str(verifier["verifier_id"])
        for verifier in verifiers
        if verifier.get("execution_mode") in STATIC_EXECUTION_MODES and isinstance(verifier.get("verifier_id"), str)
    )
    production_enabled = sorted(
        str(verifier["verifier_id"])
        for verifier in verifiers
        if verifier.get("execution_mode") in PRODUCTION_EXECUTION_MODES and isinstance(verifier.get("verifier_id"), str)
    )
    policy: dict[str, Any] = {
        "schema": POLICY_SCHEMA,
        "policy_name": "zenoproof-production-governance-candidate-1",
        "environment": "production-candidate",
        "registry_manifest_path": "tools/zenoproof_registry_manifest.json",
        "registry_manifest_id": _registry_id(active_registry),
        "governance": {
            "contract_address": "0x5555555555555555555555555555555555555555",
            "policy_epoch": active_registry.get("policy_epoch", 0),
            "timelock_seconds": 172_800,
            "verifier_onboarding_quorum": 4,
            "verifier_revocation_quorum": 3,
            "emergency_pause_role": "zenoproof-governance-guardian-1",
            "governance_approval_receipt": _sha("zenoproof.production_governance.approval"),
            "governance_execution_receipt": _sha("zenoproof.production_governance.execution.pending"),
        },
        "code_signing": {
            "required": True,
            "scheme": "sigstore-bundle-v1",
            "release_signer_identity": "release@zenodex.org",
            "artifact_digest_alg": "sha256",
            "policy_bundle_digest": _sha("zenoproof.production_governance.policy_bundle"),
        },
        "sandbox": {
            "required": True,
            "deterministic_worker_image_digest": _sha("zenoproof.production_governance.worker_image"),
            "seccomp_profile_digest": _sha("zenoproof.production_governance.seccomp"),
            "network_disabled": True,
            "filesystem_readonly": True,
            "max_input_bytes": 1_000_000,
            "max_timeout_ms": 120_000,
        },
        "revocation": {
            "enabled": True,
            "revocation_list_receipt": _sha("zenoproof.production_governance.revocation_list"),
            "emergency_revocation_enabled": True,
            "revocation_drill_receipt": _sha("zenoproof.production_governance.revocation_drill.pending"),
            "max_revocation_delay_seconds": 86_400,
        },
        "verifier_policy": {
            "forbidden_execution_modes": sorted(STATIC_EXECUTION_MODES),
            "devnet_only_verifier_ids": devnet_only,
            "production_enabled_verifier_ids": production_enabled,
            "min_production_verifiers": 6,
            "min_distinct_proof_kinds": 6,
            "path_lookup_mode": "public_replay_devnet_only",
        },
        "oracle_bridge_policy": {
            "o3_receipt_required": True,
            "o5_independence_witness_required": True,
            "min_o5_distinct_verifier_count": 2,
            "min_o5_distinct_proof_kind_count": 2,
            "registry_dag_dependency_required": True,
        },
        "reward_settlement": {
            "bounded_pool_required": True,
            "no_minting_required": True,
            "live_payout_enabled": False,
            "reward_payout_replay_required": True,
            "token_settlement_policy_id": _sha("zenoproof.production_governance.reward_settlement_policy"),
        },
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }
    policy["policy_id"] = policy_content_hash(policy)
    return policy


def check_policy(
    policy: Mapping[str, Any],
    registry: Mapping[str, Any],
    reward_payout_status: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    go_live_blockers = list(BASE_GO_LIVE_BLOCKERS)
    _unknown_fields(policy, allowed=TOP_LEVEL_KEYS, label="policy", errors=errors)
    if policy.get("schema") != POLICY_SCHEMA:
        errors.append("policy_schema_mismatch")
    expected_policy_id = policy_content_hash(policy)
    if policy.get("policy_id") != expected_policy_id:
        errors.append("policy_id_mismatch")
    if policy.get("environment") != "production-candidate":
        errors.append("environment_must_be_production_candidate")
    if policy.get("registry_manifest_id") != _registry_id(registry):
        errors.append("registry_manifest_id_mismatch")

    registry_errors = verify_registry_manifest(registry)
    errors.extend(f"registry:{error}" for error in registry_errors)
    if registry.get("schema") != REGISTRY_SCHEMA:
        errors.append("registry_schema_mismatch")

    governance = _obj_field(policy, "governance", errors)
    if governance:
        _unknown_fields(governance, allowed=GOVERNANCE_KEYS, label="governance", errors=errors)
        if not _is_address(governance.get("contract_address")):
            errors.append("governance_contract_address_invalid")
        policy_epoch = _int_field(governance, "policy_epoch", errors, minimum=1)
        if isinstance(policy_epoch, int) and registry.get("policy_epoch") != policy_epoch:
            errors.append("governance_policy_epoch_mismatch")
        _int_field(governance, "timelock_seconds", errors, minimum=86_400)
        _int_field(governance, "verifier_onboarding_quorum", errors, minimum=3)
        _int_field(governance, "verifier_revocation_quorum", errors, minimum=2)
        pause_role = governance.get("emergency_pause_role")
        if not isinstance(pause_role, str) or not pause_role.strip():
            errors.append("emergency_pause_role_required")
        for key in ("governance_approval_receipt", "governance_execution_receipt"):
            if not _is_sha(governance.get(key)):
                errors.append(f"{key}_must_be_sha256")

    code_signing = _obj_field(policy, "code_signing", errors)
    if code_signing:
        _unknown_fields(code_signing, allowed=CODE_SIGNING_KEYS, label="code_signing", errors=errors)
        _bool_true(code_signing, "required", errors)
        if code_signing.get("scheme") not in {"sigstore-bundle-v1", "cosign-keyless-v1", "hardware-key-signature-v1"}:
            errors.append("code_signing_scheme_unsupported")
        if code_signing.get("artifact_digest_alg") != "sha256":
            errors.append("artifact_digest_alg_must_be_sha256")
        identity = code_signing.get("release_signer_identity")
        if not isinstance(identity, str) or not identity.strip() or "dev" in identity.lower():
            errors.append("release_signer_identity_not_production")
        if not _is_sha(code_signing.get("policy_bundle_digest")):
            errors.append("policy_bundle_digest_must_be_sha256")

    sandbox = _obj_field(policy, "sandbox", errors)
    if sandbox:
        _unknown_fields(sandbox, allowed=SANDBOX_KEYS, label="sandbox", errors=errors)
        _bool_true(sandbox, "required", errors)
        _bool_true(sandbox, "network_disabled", errors)
        _bool_true(sandbox, "filesystem_readonly", errors)
        for key in ("deterministic_worker_image_digest", "seccomp_profile_digest"):
            if not _is_sha(sandbox.get(key)):
                errors.append(f"{key}_must_be_sha256")
        max_input_bytes = _int_field(sandbox, "max_input_bytes", errors, minimum=1, maximum=1_000_000)
        max_timeout_ms = _int_field(sandbox, "max_timeout_ms", errors, minimum=1, maximum=120_000)
    else:
        max_input_bytes = None
        max_timeout_ms = None

    revocation = _obj_field(policy, "revocation", errors)
    if revocation:
        _unknown_fields(revocation, allowed=REVOCATION_KEYS, label="revocation", errors=errors)
        _bool_true(revocation, "enabled", errors)
        _bool_true(revocation, "emergency_revocation_enabled", errors)
        _int_field(revocation, "max_revocation_delay_seconds", errors, minimum=1, maximum=86_400)
        for key in ("revocation_list_receipt", "revocation_drill_receipt"):
            if not _is_sha(revocation.get(key)):
                errors.append(f"{key}_must_be_sha256")

    verifier_policy = _obj_field(policy, "verifier_policy", errors)
    production_enabled_ids: list[str] = []
    devnet_only_ids: list[str] = []
    distinct_proof_kinds: set[str] = set()
    production_path_lookup_count = 0
    if verifier_policy:
        _unknown_fields(verifier_policy, allowed=VERIFIER_POLICY_KEYS, label="verifier_policy", errors=errors)
        forbidden_modes = set(_string_list(verifier_policy, "forbidden_execution_modes", errors))
        devnet_only_ids = _string_list(verifier_policy, "devnet_only_verifier_ids", errors)
        production_enabled_ids = _string_list(verifier_policy, "production_enabled_verifier_ids", errors)
        min_production_verifiers = _int_field(verifier_policy, "min_production_verifiers", errors, minimum=1)
        min_distinct_proof_kinds = _int_field(verifier_policy, "min_distinct_proof_kinds", errors, minimum=1)
        if not STATIC_EXECUTION_MODES.issubset(forbidden_modes):
            errors.append("static_execution_modes_must_be_forbidden")
        path_lookup_mode = verifier_policy.get("path_lookup_mode")
        if path_lookup_mode not in {"disabled", "public_replay_devnet_only"}:
            errors.append("path_lookup_mode_invalid")
        elif path_lookup_mode != "disabled":
            go_live_blockers.append("public_replay_verifiers_still_allow_path_lookup")

        verifier_by_id = {
            str(verifier.get("verifier_id")): verifier
            for verifier in _registry_verifiers(registry)
            if isinstance(verifier.get("verifier_id"), str)
        }
        for verifier_id, verifier in verifier_by_id.items():
            mode = verifier.get("execution_mode")
            if mode in STATIC_EXECUTION_MODES and verifier_id not in devnet_only_ids:
                errors.append(f"static_verifier_not_marked_devnet_only:{verifier_id}")
        if set(devnet_only_ids) & set(production_enabled_ids):
            errors.append("devnet_only_verifier_enabled_for_production")
        for verifier_id in production_enabled_ids:
            verifier = verifier_by_id.get(verifier_id)
            if verifier is None:
                errors.append(f"production_verifier_unknown:{verifier_id}")
                continue
            if verifier.get("execution_mode") not in PRODUCTION_EXECUTION_MODES:
                errors.append(f"production_verifier_execution_mode_invalid:{verifier_id}")
            if verifier.get("revoked") is True:
                errors.append(f"production_verifier_revoked:{verifier_id}")
            proof_kinds = verifier.get("proof_kinds")
            if isinstance(proof_kinds, list):
                distinct_proof_kinds.update(str(kind) for kind in proof_kinds if isinstance(kind, str))
            if verifier.get("allow_path_lookup") is True:
                production_path_lookup_count += 1
            if isinstance(max_input_bytes, int):
                raw_max_input = verifier.get("max_input_bytes")
                if not isinstance(raw_max_input, int) or isinstance(raw_max_input, bool) or raw_max_input > max_input_bytes:
                    errors.append(f"production_verifier_max_input_exceeds_policy:{verifier_id}")
            if isinstance(max_timeout_ms, int):
                raw_timeout = verifier.get("timeout_ms")
                if not isinstance(raw_timeout, int) or isinstance(raw_timeout, bool) or raw_timeout > max_timeout_ms:
                    errors.append(f"production_verifier_timeout_exceeds_policy:{verifier_id}")
        if isinstance(min_production_verifiers, int) and len(production_enabled_ids) < min_production_verifiers:
            errors.append("production_verifier_count_below_policy")
        if isinstance(min_distinct_proof_kinds, int) and len(distinct_proof_kinds) < min_distinct_proof_kinds:
            errors.append("distinct_proof_kind_count_below_policy")

    oracle_bridge = _obj_field(policy, "oracle_bridge_policy", errors)
    if oracle_bridge:
        _unknown_fields(oracle_bridge, allowed=ORACLE_BRIDGE_KEYS, label="oracle_bridge_policy", errors=errors)
        _bool_true(oracle_bridge, "o3_receipt_required", errors)
        _bool_true(oracle_bridge, "o5_independence_witness_required", errors)
        _bool_true(oracle_bridge, "registry_dag_dependency_required", errors)
        _int_field(oracle_bridge, "min_o5_distinct_verifier_count", errors, minimum=2)
        _int_field(oracle_bridge, "min_o5_distinct_proof_kind_count", errors, minimum=2)

    reward_settlement = _obj_field(policy, "reward_settlement", errors)
    if reward_settlement:
        _unknown_fields(reward_settlement, allowed=REWARD_SETTLEMENT_KEYS, label="reward_settlement", errors=errors)
        _bool_true(reward_settlement, "bounded_pool_required", errors)
        _bool_true(reward_settlement, "no_minting_required", errors)
        _bool_true(reward_settlement, "reward_payout_replay_required", errors)
        if not _is_sha(reward_settlement.get("token_settlement_policy_id")):
            errors.append("token_settlement_policy_id_must_be_sha256")
        live_payout = reward_settlement.get("live_payout_enabled")
        if not isinstance(live_payout, bool):
            errors.append("live_payout_enabled_must_be_bool")
        elif live_payout is False:
            go_live_blockers.append("live_proof_mining_token_settlement_not_enabled")

    active_reward_status = dict(reward_payout_status or build_reward_payout_status(registry=registry))
    if active_reward_status.get("status") != "accepted":
        errors.append("reward_payout_replay_rejected")
        errors.extend(f"reward_payout:{error}" for error in active_reward_status.get("errors", []))

    not_claimed = policy.get("not_claimed")
    if not isinstance(not_claimed, list):
        errors.append("not_claimed_must_be_list")
    else:
        values = {str(item) for item in not_claimed if isinstance(item, str)}
        errors.extend(f"missing_not_claim:{item}" for item in sorted(REQUIRED_NOT_CLAIMS - values))

    go_live_blockers = sorted(set(go_live_blockers))
    status = "accepted" if not errors else "rejected"
    return {
        "schema": REPORT_SCHEMA,
        "ok": status == "accepted",
        "status": status,
        "policy_id": expected_policy_id,
        "registry_manifest_id": _registry_id(registry),
        "registry_error_count": len(registry_errors),
        "reward_payout_status": active_reward_status.get("status"),
        "production_enabled_verifier_count": len(production_enabled_ids),
        "devnet_only_verifier_count": len(devnet_only_ids),
        "distinct_proof_kind_count": len(distinct_proof_kinds),
        "production_verifier_path_lookup_count": production_path_lookup_count,
        "error_count": len(errors),
        "errors": errors,
        "go_live_blockers": go_live_blockers,
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy", type=Path, help="policy JSON; defaults to built-in sample policy")
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    parser.add_argument("--sample-policy", action="store_true", help="emit the built-in sample policy")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--require-live", action="store_true", help="fail if go-live blockers remain")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    registry = _load_json(args.registry)
    if args.sample_policy:
        print(json.dumps(sample_policy(registry), indent=2, sort_keys=True))
        return 0
    policy = _load_json(args.policy) if args.policy else sample_policy(registry)
    result = check_policy(policy, registry)
    if args.require_live and result["go_live_blockers"]:
        result = dict(result)
        result["ok"] = False
        result["status"] = "rejected"
        result["errors"] = [*result["errors"], "go_live_blockers_present"]
        result["error_count"] = len(result["errors"])
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"status = {result['status']}")
        print(f"error_count = {result['error_count']}")
        print(f"go_live_blocker_count = {len(result['go_live_blockers'])}")
        print(f"production_enabled_verifier_count = {result['production_enabled_verifier_count']}")
        print(f"distinct_proof_kind_count = {result['distinct_proof_kind_count']}")
        print(f"policy_id = {result['policy_id']}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
