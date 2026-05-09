#!/usr/bin/env python3
"""Check a production-candidate ZenoProof verifier governance policy."""

from __future__ import annotations

import argparse
import copy
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
RECEIPT_BUNDLE_SCHEMA = "zenodex.zenoproof.production_governance_receipt_bundle.v1"
RECEIPT_SCHEMA = "zenodex.zenoproof.production_governance_receipt.v1"
VERIFIER_RELEASE_MANIFEST_SCHEMA = "zenodex.zenoproof.verifier_release_manifest.v1"
DEFAULT_REGISTRY = ROOT / "tools" / "zenoproof_registry_manifest.json"
ADDRESS_RE = re.compile(r"^0x[0-9a-fA-F]{40}$")
TX_RE = re.compile(r"^0x[0-9a-fA-F]{64}$")
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
    "verifier_release_manifest_digest",
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
RECEIPT_BUNDLE_KEYS = {
    "schema",
    "policy_id",
    "policy_name",
    "registry_manifest_id",
    "chain_id",
    "observed_block_number",
    "observed_block_hash",
    "receipts",
    "not_claimed",
}
RECEIPT_KEYS = {
    "schema",
    "receipt_id",
    "kind",
    "chain_id",
    "contract_address",
    "tx_hash",
    "block_number",
    "block_hash",
    "log_index",
    "payload",
}
REQUIRED_RECEIPT_KINDS = {
    "code_signing_attestation",
    "governance_approval",
    "governance_execution",
    "revocation_drill",
    "revocation_list",
    "sandbox_attestation",
    "verifier_release_transparency_log",
}
RECEIPT_NOT_CLAIMS = {
    "does_not_claim_receipts_verified_against_live_rpc",
    "does_not_claim_contract_code_verified_onchain",
    "does_not_claim_public_proof_network_soak",
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


def policy_static_hash(policy: Mapping[str, Any]) -> str:
    payload = copy.deepcopy(dict(policy))
    payload.pop("policy_id", None)
    payload.pop("not_claimed", None)
    governance = payload.get("governance")
    if isinstance(governance, dict):
        governance.pop("governance_approval_receipt", None)
        governance.pop("governance_execution_receipt", None)
    revocation = payload.get("revocation")
    if isinstance(revocation, dict):
        revocation.pop("revocation_list_receipt", None)
        revocation.pop("revocation_drill_receipt", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def receipt_content_hash(receipt: Mapping[str, Any]) -> str:
    payload = dict(receipt)
    payload.pop("receipt_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def _sha(label: str) -> str:
    return "sha256:" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _tx(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must be a JSON object")
    return obj


def _is_sha(value: Any) -> bool:
    return isinstance(value, str) and SHA_RE.fullmatch(value) is not None


def _is_address(value: Any) -> bool:
    return isinstance(value, str) and ADDRESS_RE.fullmatch(value) is not None


def _is_tx(value: Any) -> bool:
    return isinstance(value, str) and TX_RE.fullmatch(value) is not None


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


def production_verifier_release_manifest(registry: Mapping[str, Any], policy: Mapping[str, Any]) -> dict[str, Any]:
    verifier_policy = policy.get("verifier_policy") if isinstance(policy.get("verifier_policy"), Mapping) else {}
    raw_ids = verifier_policy.get("production_enabled_verifier_ids")
    production_ids = sorted(str(item) for item in raw_ids if isinstance(item, str)) if isinstance(raw_ids, list) else []
    verifier_by_id = {
        str(verifier.get("verifier_id")): verifier
        for verifier in _registry_verifiers(registry)
        if isinstance(verifier.get("verifier_id"), str)
    }
    entries: list[dict[str, Any]] = []
    for index, verifier_id in enumerate(production_ids, start=1):
        verifier = verifier_by_id.get(verifier_id)
        if verifier is None:
            continue
        verifier_command = verifier.get("verifier_command")
        command = list(verifier_command) if isinstance(verifier_command, list) else []
        proof_kinds = sorted(str(kind) for kind in verifier.get("proof_kinds", []) if isinstance(kind, str))
        toolchain_ids = sorted(str(toolchain) for toolchain in verifier.get("toolchain_ids", []) if isinstance(toolchain, str))
        entry_base = {
            "allow_path_lookup": verifier.get("allow_path_lookup"),
            "current_policy_root": verifier.get("current_policy_root"),
            "execution_mode": verifier.get("execution_mode"),
            "max_input_bytes": verifier.get("max_input_bytes"),
            "name": verifier.get("name"),
            "proof_kinds": proof_kinds,
            "timeout_ms": verifier.get("timeout_ms"),
            "toolchain_ids_hash": sha256_json({"toolchain_ids": toolchain_ids}),
            "verifier_command_hash": sha256_json({"verifier_command": command}),
            "verifier_id": verifier_id,
        }
        artifact_digest = sha256_json({"verifier_release_entry": entry_base})
        entries.append(
            {
                **entry_base,
                "artifact_digest": artifact_digest,
                "transparency_log_id": _sha(f"zenoproof.production_verifier.release.{verifier_id}.{artifact_digest}"),
                "transparency_log_index": index,
            }
        )
    manifest_body = {
        "schema": VERIFIER_RELEASE_MANIFEST_SCHEMA,
        "registry_manifest_id": _registry_id(registry),
        "production_verifier_ids": production_ids,
        "verifiers": entries,
    }
    return {
        **manifest_body,
        "manifest_digest": sha256_json(manifest_body),
    }


def verifier_release_transparency_log_entries(release_manifest: Mapping[str, Any]) -> list[dict[str, Any]]:
    entries = release_manifest.get("verifiers")
    if not isinstance(entries, list):
        return []
    out: list[dict[str, Any]] = []
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        out.append(
            {
                "artifact_digest": entry.get("artifact_digest"),
                "transparency_log_id": entry.get("transparency_log_id"),
                "transparency_log_index": entry.get("transparency_log_index"),
                "verifier_id": entry.get("verifier_id"),
            }
        )
    return out


def verifier_release_transparency_log_root(release_manifest: Mapping[str, Any]) -> str:
    return sha256_json(
        {
            "schema": "zenodex.zenoproof.verifier_release_transparency_log.v1",
            "manifest_digest": release_manifest.get("manifest_digest"),
            "registry_manifest_id": release_manifest.get("registry_manifest_id"),
            "entries": verifier_release_transparency_log_entries(release_manifest),
        }
    )


def _sample_registry() -> Mapping[str, Any]:
    return _load_json(DEFAULT_REGISTRY)


def _receipt(
    *,
    kind: str,
    chain_id: str,
    contract_address: str,
    tx_hash: str,
    block_number: int,
    block_hash: str,
    log_index: int,
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    receipt: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA,
        "kind": kind,
        "chain_id": chain_id,
        "contract_address": contract_address,
        "tx_hash": tx_hash,
        "block_number": int(block_number),
        "block_hash": block_hash,
        "log_index": int(log_index),
        "payload": dict(payload),
    }
    receipt["receipt_id"] = receipt_content_hash(receipt)
    return receipt


def _sample_receipts_for_policy(policy: Mapping[str, Any], registry: Mapping[str, Any]) -> list[dict[str, Any]]:
    chain_id = "zenoproof.mainnet-candidate-1"
    static_hash = policy_static_hash(policy)
    governance = policy.get("governance") if isinstance(policy.get("governance"), Mapping) else {}
    code_signing = policy.get("code_signing") if isinstance(policy.get("code_signing"), Mapping) else {}
    sandbox = policy.get("sandbox") if isinstance(policy.get("sandbox"), Mapping) else {}
    revocation = policy.get("revocation") if isinstance(policy.get("revocation"), Mapping) else {}
    release_manifest = production_verifier_release_manifest(registry, policy)
    registry_id = _registry_id(registry)
    proposal_id = _sha(f"zenoproof.production_governance.proposal.{static_hash}.{registry_id}")
    queued_at = 1_900_000_000
    timelock_seconds = int(governance.get("timelock_seconds", 172_800))
    executable_after = queued_at + timelock_seconds
    executed_at = executable_after
    governance_contract = str(governance.get("contract_address"))
    policy_epoch = int(governance.get("policy_epoch", registry.get("policy_epoch", 0)))
    revocation_delay = int(revocation.get("max_revocation_delay_seconds", 86_400))
    drill_requested_at = executed_at + 1_000
    drill_executed_at = drill_requested_at + revocation_delay
    return [
        _receipt(
            kind="governance_approval",
            chain_id=chain_id,
            contract_address=governance_contract,
            tx_hash=_tx("zenoproof.production_governance.approval"),
            block_number=2_000,
            block_hash=_sha("zenoproof.production_governance.block.2000"),
            log_index=0,
            payload={
                "approved": True,
                "executable_after_timestamp": executable_after,
                "policy_epoch": policy_epoch,
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "proposal_id": proposal_id,
                "queued_at_timestamp": queued_at,
                "registry_manifest_id": registry_id,
                "timelock_seconds": timelock_seconds,
            },
        ),
        _receipt(
            kind="governance_execution",
            chain_id=chain_id,
            contract_address=governance_contract,
            tx_hash=_tx("zenoproof.production_governance.execution"),
            block_number=2_100,
            block_hash=_sha("zenoproof.production_governance.block.2100"),
            log_index=0,
            payload={
                "executed": True,
                "executed_at_timestamp": executed_at,
                "executable_after_timestamp": executable_after,
                "policy_epoch": policy_epoch,
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "proposal_id": proposal_id,
                "registry_manifest_id": registry_id,
            },
        ),
        _receipt(
            kind="revocation_list",
            chain_id=chain_id,
            contract_address=governance_contract,
            tx_hash=_tx("zenoproof.production_governance.revocation_list"),
            block_number=2_200,
            block_hash=_sha("zenoproof.production_governance.block.2200"),
            log_index=0,
            payload={
                "policy_epoch": policy_epoch,
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "registry_manifest_id": registry_id,
                "revocation_enabled": True,
                "revoked_verifier_ids": [],
            },
        ),
        _receipt(
            kind="revocation_drill",
            chain_id=chain_id,
            contract_address=governance_contract,
            tx_hash=_tx("zenoproof.production_governance.revocation_drill"),
            block_number=2_300,
            block_hash=_sha("zenoproof.production_governance.block.2300"),
            log_index=0,
            payload={
                "drill_executed": True,
                "executed_at_timestamp": drill_executed_at,
                "max_revocation_delay_seconds": revocation_delay,
                "policy_epoch": policy_epoch,
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "registry_manifest_id": registry_id,
                "requested_at_timestamp": drill_requested_at,
            },
        ),
        _receipt(
            kind="code_signing_attestation",
            chain_id=chain_id,
            contract_address=governance_contract,
            tx_hash=_tx("zenoproof.production_governance.code_signing_attestation"),
            block_number=2_400,
            block_hash=_sha("zenoproof.production_governance.block.2400"),
            log_index=0,
            payload={
                "artifact_digest_alg": code_signing.get("artifact_digest_alg"),
                "policy_bundle_digest": code_signing.get("policy_bundle_digest"),
                "policy_epoch": policy_epoch,
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "registry_manifest_id": registry_id,
                "release_signer_identity": code_signing.get("release_signer_identity"),
                "scheme": code_signing.get("scheme"),
                "transparency_log_observed": True,
                "verified": True,
                "verifier_release_entries": release_manifest["verifiers"],
                "verifier_release_manifest_digest": code_signing.get("verifier_release_manifest_digest"),
            },
        ),
        _receipt(
            kind="verifier_release_transparency_log",
            chain_id=chain_id,
            contract_address=governance_contract,
            tx_hash=_tx("zenoproof.production_governance.verifier_release_transparency_log"),
            block_number=2_450,
            block_hash=_sha("zenoproof.production_governance.block.2450"),
            log_index=0,
            payload={
                "entries": verifier_release_transparency_log_entries(release_manifest),
                "policy_epoch": policy_epoch,
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "registry_manifest_id": registry_id,
                "transparency_log_observed": True,
                "transparency_log_root": verifier_release_transparency_log_root(release_manifest),
                "transparency_log_tree_size": len(release_manifest["verifiers"]),
                "verified": True,
                "verifier_release_manifest_digest": code_signing.get("verifier_release_manifest_digest"),
            },
        ),
        _receipt(
            kind="sandbox_attestation",
            chain_id=chain_id,
            contract_address=governance_contract,
            tx_hash=_tx("zenoproof.production_governance.sandbox_attestation"),
            block_number=2_500,
            block_hash=_sha("zenoproof.production_governance.block.2500"),
            log_index=0,
            payload={
                "deterministic_worker_image_digest": sandbox.get("deterministic_worker_image_digest"),
                "filesystem_readonly": sandbox.get("filesystem_readonly"),
                "max_input_bytes": sandbox.get("max_input_bytes"),
                "max_timeout_ms": sandbox.get("max_timeout_ms"),
                "network_disabled": sandbox.get("network_disabled"),
                "policy_epoch": policy_epoch,
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "registry_manifest_id": registry_id,
                "seccomp_profile_digest": sandbox.get("seccomp_profile_digest"),
                "verified": True,
            },
        ),
    ]


def _sample_receipt_refs(policy: Mapping[str, Any], registry: Mapping[str, Any]) -> dict[str, dict[str, str]]:
    receipts = _sample_receipts_for_policy(policy, registry)
    by_kind = {str(receipt["kind"]): str(receipt["receipt_id"]) for receipt in receipts}
    return {
        "governance": {
            "governance_approval_receipt": by_kind["governance_approval"],
            "governance_execution_receipt": by_kind["governance_execution"],
        },
        "revocation": {
            "revocation_list_receipt": by_kind["revocation_list"],
            "revocation_drill_receipt": by_kind["revocation_drill"],
        },
    }


def sample_receipt_bundle(
    policy: Mapping[str, Any] | None = None,
    registry: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    active_registry = dict(registry or _sample_registry())
    active_policy = policy or sample_policy(active_registry)
    receipts = _sample_receipts_for_policy(active_policy, active_registry)
    return {
        "schema": RECEIPT_BUNDLE_SCHEMA,
        "policy_id": active_policy.get("policy_id"),
        "policy_name": active_policy.get("policy_name"),
        "registry_manifest_id": _registry_id(active_registry),
        "chain_id": "zenoproof.mainnet-candidate-1",
        "observed_block_number": 2_500,
        "observed_block_hash": _sha("zenoproof.production_governance.block.2500"),
        "receipts": receipts,
        "not_claimed": sorted(RECEIPT_NOT_CLAIMS),
    }


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
    release_manifest = production_verifier_release_manifest(
        active_registry,
        {"verifier_policy": {"production_enabled_verifier_ids": production_enabled}},
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
        },
        "code_signing": {
            "required": True,
            "scheme": "sigstore-bundle-v1",
            "release_signer_identity": "release@zenodex.org",
            "artifact_digest_alg": "sha256",
            "policy_bundle_digest": _sha("zenoproof.production_governance.policy_bundle"),
            "verifier_release_manifest_digest": release_manifest["manifest_digest"],
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
            "emergency_revocation_enabled": True,
            "max_revocation_delay_seconds": 86_400,
        },
        "verifier_policy": {
            "forbidden_execution_modes": sorted(STATIC_EXECUTION_MODES),
            "devnet_only_verifier_ids": devnet_only,
            "production_enabled_verifier_ids": production_enabled,
            "min_production_verifiers": 6,
            "min_distinct_proof_kinds": 6,
            "path_lookup_mode": "disabled",
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
    refs = _sample_receipt_refs(policy, active_registry)
    policy["governance"].update(refs["governance"])
    policy["revocation"].update(refs["revocation"])
    policy["policy_id"] = policy_content_hash(policy)
    return policy


def check_receipt_bundle(
    policy: Mapping[str, Any],
    registry: Mapping[str, Any],
    receipt_bundle: Mapping[str, Any] | None,
) -> dict[str, Any]:
    errors: list[str] = []
    if receipt_bundle is None:
        return {
            "schema": RECEIPT_BUNDLE_SCHEMA,
            "ok": False,
            "status": "rejected",
            "error_count": 1,
            "errors": ["receipt_bundle_required"],
            "receipt_count": 0,
            "receipt_kinds": [],
        }

    _unknown_fields(receipt_bundle, allowed=RECEIPT_BUNDLE_KEYS, label="receipt_bundle", errors=errors)
    if receipt_bundle.get("schema") != RECEIPT_BUNDLE_SCHEMA:
        errors.append("receipt_bundle_schema_mismatch")
    if receipt_bundle.get("policy_id") != policy.get("policy_id"):
        errors.append("receipt_bundle_policy_id_mismatch")
    if receipt_bundle.get("policy_name") != policy.get("policy_name"):
        errors.append("receipt_bundle_policy_name_mismatch")
    registry_id = _registry_id(registry)
    if receipt_bundle.get("registry_manifest_id") != registry_id:
        errors.append("receipt_bundle_registry_manifest_id_mismatch")
    chain_id = receipt_bundle.get("chain_id")
    if not isinstance(chain_id, str) or not chain_id.strip():
        errors.append("receipt_bundle_chain_id_required")
    observed_block_number = receipt_bundle.get("observed_block_number")
    if not isinstance(observed_block_number, int) or isinstance(observed_block_number, bool) or observed_block_number <= 0:
        errors.append("observed_block_number_must_be_positive_int")
        observed_block_number = 0
    if not _is_sha(receipt_bundle.get("observed_block_hash")):
        errors.append("observed_block_hash_must_be_sha256")

    not_claimed = receipt_bundle.get("not_claimed")
    if not isinstance(not_claimed, list):
        errors.append("receipt_bundle_not_claimed_must_be_list")
    else:
        values = {str(item) for item in not_claimed if isinstance(item, str)}
        errors.extend(f"missing_receipt_not_claim:{item}" for item in sorted(RECEIPT_NOT_CLAIMS - values))

    raw_receipts = receipt_bundle.get("receipts")
    if not isinstance(raw_receipts, list):
        errors.append("receipts_must_be_list")
        raw_receipts = []

    governance = policy.get("governance") if isinstance(policy.get("governance"), Mapping) else {}
    code_signing = policy.get("code_signing") if isinstance(policy.get("code_signing"), Mapping) else {}
    sandbox = policy.get("sandbox") if isinstance(policy.get("sandbox"), Mapping) else {}
    revocation = policy.get("revocation") if isinstance(policy.get("revocation"), Mapping) else {}
    verifier_policy = policy.get("verifier_policy") if isinstance(policy.get("verifier_policy"), Mapping) else {}
    static_hash = policy_static_hash(policy)
    governance_contract = governance.get("contract_address")
    expected_receipt_id_by_kind = {
        "governance_approval": governance.get("governance_approval_receipt"),
        "governance_execution": governance.get("governance_execution_receipt"),
        "revocation_list": revocation.get("revocation_list_receipt"),
        "revocation_drill": revocation.get("revocation_drill_receipt"),
    }
    by_kind: dict[str, Mapping[str, Any]] = {}

    for idx, receipt in enumerate(raw_receipts):
        if not isinstance(receipt, Mapping):
            errors.append(f"receipt_{idx}_must_be_object")
            continue
        _unknown_fields(receipt, allowed=RECEIPT_KEYS, label=f"receipt_{idx}", errors=errors)
        if receipt.get("schema") != RECEIPT_SCHEMA:
            errors.append(f"receipt_{idx}_schema_mismatch")
        kind = receipt.get("kind")
        if not isinstance(kind, str) or kind not in REQUIRED_RECEIPT_KINDS:
            errors.append(f"receipt_{idx}_kind_invalid")
            continue
        if kind in by_kind:
            errors.append(f"duplicate_receipt_kind:{kind}")
        else:
            by_kind[kind] = receipt
        if receipt.get("receipt_id") != receipt_content_hash(receipt):
            errors.append(f"receipt_id_mismatch:{kind}")
        expected_receipt_id = expected_receipt_id_by_kind.get(kind)
        if expected_receipt_id is not None and receipt.get("receipt_id") != expected_receipt_id:
            errors.append(f"policy_receipt_id_mismatch:{kind}")
        if receipt.get("chain_id") != chain_id:
            errors.append(f"receipt_chain_id_mismatch:{kind}")
        if receipt.get("contract_address") != governance_contract:
            errors.append(f"receipt_contract_mismatch:{kind}")
        if not _is_tx(receipt.get("tx_hash")):
            errors.append(f"receipt_tx_hash_invalid:{kind}")
        if not _is_sha(receipt.get("block_hash")):
            errors.append(f"receipt_block_hash_invalid:{kind}")
        block_number = receipt.get("block_number")
        if not isinstance(block_number, int) or isinstance(block_number, bool) or block_number <= 0:
            errors.append(f"receipt_block_number_invalid:{kind}")
        elif isinstance(observed_block_number, int) and observed_block_number > 0 and block_number > observed_block_number:
            errors.append(f"receipt_after_observed_block:{kind}")
        log_index = receipt.get("log_index")
        if not isinstance(log_index, int) or isinstance(log_index, bool) or log_index < 0:
            errors.append(f"receipt_log_index_invalid:{kind}")
        payload = receipt.get("payload")
        if not isinstance(payload, Mapping):
            errors.append(f"receipt_payload_must_be_object:{kind}")
            continue
        if payload.get("policy_name") != policy.get("policy_name"):
            errors.append(f"receipt_policy_name_mismatch:{kind}")
        if payload.get("policy_static_hash") != static_hash:
            errors.append(f"receipt_policy_static_hash_mismatch:{kind}")
        if payload.get("registry_manifest_id") != registry_id:
            errors.append(f"receipt_registry_manifest_id_mismatch:{kind}")
        if payload.get("policy_epoch") != governance.get("policy_epoch"):
            errors.append(f"receipt_policy_epoch_mismatch:{kind}")

    for kind in sorted(REQUIRED_RECEIPT_KINDS - set(by_kind)):
        errors.append(f"missing_receipt_kind:{kind}")

    approval_payload = (
        by_kind["governance_approval"].get("payload")
        if "governance_approval" in by_kind and isinstance(by_kind["governance_approval"].get("payload"), Mapping)
        else {}
    )
    execution_payload = (
        by_kind["governance_execution"].get("payload")
        if "governance_execution" in by_kind and isinstance(by_kind["governance_execution"].get("payload"), Mapping)
        else {}
    )
    revocation_list_payload = (
        by_kind["revocation_list"].get("payload")
        if "revocation_list" in by_kind and isinstance(by_kind["revocation_list"].get("payload"), Mapping)
        else {}
    )
    revocation_drill_payload = (
        by_kind["revocation_drill"].get("payload")
        if "revocation_drill" in by_kind and isinstance(by_kind["revocation_drill"].get("payload"), Mapping)
        else {}
    )
    code_signing_payload = (
        by_kind["code_signing_attestation"].get("payload")
        if "code_signing_attestation" in by_kind and isinstance(by_kind["code_signing_attestation"].get("payload"), Mapping)
        else {}
    )
    transparency_log_payload = (
        by_kind["verifier_release_transparency_log"].get("payload")
        if "verifier_release_transparency_log" in by_kind
        and isinstance(by_kind["verifier_release_transparency_log"].get("payload"), Mapping)
        else {}
    )
    sandbox_payload = (
        by_kind["sandbox_attestation"].get("payload")
        if "sandbox_attestation" in by_kind and isinstance(by_kind["sandbox_attestation"].get("payload"), Mapping)
        else {}
    )

    def _receipt_position(kind: str) -> tuple[int, int] | None:
        receipt = by_kind.get(kind)
        if receipt is None:
            return None
        block_number = receipt.get("block_number")
        log_index = receipt.get("log_index")
        if (
            isinstance(block_number, int)
            and not isinstance(block_number, bool)
            and isinstance(log_index, int)
            and not isinstance(log_index, bool)
        ):
            return (block_number, log_index)
        return None

    def _require_receipt_order(before: str, after: str) -> None:
        before_pos = _receipt_position(before)
        after_pos = _receipt_position(after)
        if before_pos is not None and after_pos is not None and before_pos >= after_pos:
            errors.append(f"receipt_order_invalid:{before}->{after}")

    for before, after in (
        ("governance_approval", "governance_execution"),
        ("governance_execution", "revocation_list"),
        ("governance_execution", "revocation_drill"),
        ("governance_execution", "code_signing_attestation"),
        ("code_signing_attestation", "verifier_release_transparency_log"),
        ("verifier_release_transparency_log", "sandbox_attestation"),
    ):
        _require_receipt_order(before, after)

    timelock_seconds = governance.get("timelock_seconds")
    if approval_payload:
        if approval_payload.get("approved") is not True:
            errors.append("governance_approval_not_true")
        if approval_payload.get("timelock_seconds") != timelock_seconds:
            errors.append("governance_approval_timelock_mismatch")
        queued_at = approval_payload.get("queued_at_timestamp")
        executable_after = approval_payload.get("executable_after_timestamp")
        if (
            isinstance(queued_at, int)
            and not isinstance(queued_at, bool)
            and isinstance(executable_after, int)
            and not isinstance(executable_after, bool)
            and isinstance(timelock_seconds, int)
            and not isinstance(timelock_seconds, bool)
        ):
            if executable_after - queued_at < timelock_seconds:
                errors.append("governance_timelock_not_satisfied")
        else:
            errors.append("governance_approval_timestamps_invalid")
    if execution_payload:
        if execution_payload.get("executed") is not True:
            errors.append("governance_execution_not_true")
        if execution_payload.get("proposal_id") != approval_payload.get("proposal_id"):
            errors.append("governance_execution_proposal_mismatch")
        executed_at = execution_payload.get("executed_at_timestamp")
        executable_after = approval_payload.get("executable_after_timestamp")
        if (
            isinstance(executed_at, int)
            and not isinstance(executed_at, bool)
            and isinstance(executable_after, int)
            and not isinstance(executable_after, bool)
        ):
            if executed_at < executable_after:
                errors.append("governance_execution_before_timelock")
        else:
            errors.append("governance_execution_timestamp_invalid")

    if revocation_list_payload:
        if revocation_list_payload.get("revocation_enabled") is not True:
            errors.append("revocation_list_not_enabled")
        revoked_ids = revocation_list_payload.get("revoked_verifier_ids")
        if not isinstance(revoked_ids, list):
            errors.append("revoked_verifier_ids_must_be_list")
    if revocation_drill_payload:
        if revocation_drill_payload.get("drill_executed") is not True:
            errors.append("revocation_drill_not_executed")
        requested_at = revocation_drill_payload.get("requested_at_timestamp")
        executed_at = revocation_drill_payload.get("executed_at_timestamp")
        max_delay = revocation.get("max_revocation_delay_seconds")
        if (
            isinstance(requested_at, int)
            and not isinstance(requested_at, bool)
            and isinstance(executed_at, int)
            and not isinstance(executed_at, bool)
            and isinstance(max_delay, int)
            and not isinstance(max_delay, bool)
        ):
            if executed_at - requested_at > max_delay:
                errors.append("revocation_drill_exceeds_policy_delay")
        else:
            errors.append("revocation_drill_timestamps_invalid")

    if code_signing_payload:
        if code_signing_payload.get("verified") is not True:
            errors.append("code_signing_attestation_not_verified")
        for key in (
            "artifact_digest_alg",
            "policy_bundle_digest",
            "release_signer_identity",
            "scheme",
            "verifier_release_manifest_digest",
        ):
            if code_signing_payload.get(key) != code_signing.get(key):
                errors.append(f"code_signing_attestation_{key}_mismatch")
        expected_release_manifest = production_verifier_release_manifest(registry, policy)
        if code_signing_payload.get("transparency_log_observed") is not True:
            errors.append("code_signing_attestation_transparency_log_not_observed")
        if code_signing_payload.get("verifier_release_manifest_digest") != expected_release_manifest["manifest_digest"]:
            errors.append("code_signing_attestation_verifier_release_manifest_digest_mismatch")
        if code_signing_payload.get("verifier_release_entries") != expected_release_manifest["verifiers"]:
            errors.append("code_signing_attestation_verifier_release_entries_mismatch")
    if transparency_log_payload:
        if transparency_log_payload.get("verified") is not True:
            errors.append("verifier_release_transparency_log_not_verified")
        if transparency_log_payload.get("transparency_log_observed") is not True:
            errors.append("verifier_release_transparency_log_not_observed")
        expected_release_manifest = production_verifier_release_manifest(registry, policy)
        expected_log_entries = verifier_release_transparency_log_entries(expected_release_manifest)
        if transparency_log_payload.get("verifier_release_manifest_digest") != expected_release_manifest["manifest_digest"]:
            errors.append("verifier_release_transparency_log_manifest_digest_mismatch")
        if transparency_log_payload.get("entries") != expected_log_entries:
            errors.append("verifier_release_transparency_log_entries_mismatch")
        if transparency_log_payload.get("transparency_log_tree_size") != len(expected_log_entries):
            errors.append("verifier_release_transparency_log_tree_size_mismatch")
        expected_log_root = verifier_release_transparency_log_root(expected_release_manifest)
        if transparency_log_payload.get("transparency_log_root") != expected_log_root:
            errors.append("verifier_release_transparency_log_root_mismatch")
        indices = [entry.get("transparency_log_index") for entry in expected_log_entries]
        if indices != list(range(1, len(expected_log_entries) + 1)):
            errors.append("verifier_release_transparency_log_indices_not_contiguous")
    if sandbox_payload:
        if sandbox_payload.get("verified") is not True:
            errors.append("sandbox_attestation_not_verified")
        for key in (
            "deterministic_worker_image_digest",
            "filesystem_readonly",
            "max_input_bytes",
            "max_timeout_ms",
            "network_disabled",
            "seccomp_profile_digest",
        ):
            if sandbox_payload.get(key) != sandbox.get(key):
                errors.append(f"sandbox_attestation_{key}_mismatch")

    production_enabled_ids = verifier_policy.get("production_enabled_verifier_ids")
    if isinstance(production_enabled_ids, list) and len(production_enabled_ids) == 0:
        errors.append("receipt_bundle_no_production_verifiers")

    status = "accepted" if not errors else "rejected"
    return {
        "schema": RECEIPT_BUNDLE_SCHEMA,
        "ok": status == "accepted",
        "status": status,
        "error_count": len(errors),
        "errors": errors,
        "receipt_count": len(raw_receipts),
        "receipt_kinds": sorted(by_kind),
    }


def check_policy(
    policy: Mapping[str, Any],
    registry: Mapping[str, Any],
    reward_payout_status: Mapping[str, Any] | None = None,
    receipt_bundle: Mapping[str, Any] | None = None,
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
        if not _is_sha(code_signing.get("verifier_release_manifest_digest")):
            errors.append("verifier_release_manifest_digest_must_be_sha256")

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
                if path_lookup_mode == "disabled":
                    errors.append(f"production_verifier_path_lookup_enabled:{verifier_id}")
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

    release_manifest = production_verifier_release_manifest(registry, policy)
    if code_signing and _is_sha(code_signing.get("verifier_release_manifest_digest")):
        if code_signing.get("verifier_release_manifest_digest") != release_manifest["manifest_digest"]:
            errors.append("verifier_release_manifest_digest_mismatch")

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

    receipt_result = check_receipt_bundle(policy, registry, receipt_bundle)
    if receipt_result["status"] != "accepted":
        errors.append("receipt_bundle_rejected")
        errors.extend(f"receipt:{error}" for error in receipt_result.get("errors", []))

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
        "receipt_bundle_status": receipt_result["status"],
        "receipt_bundle_kind_count": len(receipt_result.get("receipt_kinds", [])),
        "production_enabled_verifier_count": len(production_enabled_ids),
        "devnet_only_verifier_count": len(devnet_only_ids),
        "distinct_proof_kind_count": len(distinct_proof_kinds),
        "verifier_release_entry_count": len(release_manifest["verifiers"]),
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
    parser.add_argument("--receipts", type=Path, help="receipt bundle JSON; required when policy/registry is custom")
    parser.add_argument("--sample-policy", action="store_true", help="emit the built-in sample policy")
    parser.add_argument("--sample-receipts", action="store_true", help="emit the built-in sample receipt bundle")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--require-live", action="store_true", help="fail if go-live blockers remain")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    registry = _load_json(args.registry)
    if args.sample_policy:
        print(json.dumps(sample_policy(registry), indent=2, sort_keys=True))
        return 0
    if args.sample_receipts:
        policy = _load_json(args.policy) if args.policy else sample_policy(registry)
        print(json.dumps(sample_receipt_bundle(policy, registry), indent=2, sort_keys=True))
        return 0
    policy = _load_json(args.policy) if args.policy else sample_policy(registry)
    if args.receipts:
        receipts: Mapping[str, Any] | None = _load_json(args.receipts)
    elif args.policy is None and args.registry == DEFAULT_REGISTRY:
        receipts = sample_receipt_bundle(policy, registry)
    else:
        receipts = None
    result = check_policy(policy, registry, receipt_bundle=receipts)
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
        print(f"receipt_bundle_status = {result['receipt_bundle_status']}")
        print(f"go_live_blocker_count = {len(result['go_live_blockers'])}")
        print(f"production_enabled_verifier_count = {result['production_enabled_verifier_count']}")
        print(f"distinct_proof_kind_count = {result['distinct_proof_kind_count']}")
        print(f"production_verifier_path_lookup_count = {result['production_verifier_path_lookup_count']}")
        print(f"policy_id = {result['policy_id']}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
