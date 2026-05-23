"""Adapter-neutral Tau export packets for ZenoLedger checkpoints."""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_ledger_profile import validate_checkpoint_admission_v0
from src.integration.zeno_ledger_v0 import (
    canonical_body_root_v0,
    hash_v0,
    validate_checkpoint_header_binding_v0,
    validate_header_body_roots_v0,
)
from src.state.canonical import canonical_hex_fixed_allow_0x


TAU_EXPORT_PACKET_SCHEMA_V0 = "zenodex/zeno_ledger/tau_export_packet/v0"
TAU_EXPORT_PACKET_KIND_V0 = "zenoledger_checkpoint_for_tau"
TAU_EXPORT_ADAPTER_CONTRACT_V0 = "zenoledger_tau_adapter_v0"
TAU_RULE_COMMITMENT_SCHEMA_V0 = "zenodex/zeno_ledger/tau_rule_commitment/v0"


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _tau_rule_commitment_hash_v0(commitment: Mapping[str, Any]) -> str:
    body = {key: value for key, value in dict(commitment).items() if key != "tau_rule_commitment_hash"}
    return hash_v0("tau_rule_commitment_v0", body)


def build_tau_rule_commitment_v0(
    *,
    tau_network_id: str,
    tau_adapter_ref: str,
    tau_language_semantics_ref: str,
    semantic_contracts: Mapping[str, Any],
    supported_runtime_contract: Mapping[str, Any],
    spec_profiles: Mapping[str, Any],
    active_spec_inventory: Mapping[str, Any],
) -> dict[str, Any]:
    """Build a hash-bound Tau semantics/runtime commitment.

    The commitment is deliberately adapter-neutral. It binds the local Tau
    network, adapter reference, language semantics reference, and the hashes of
    the rule artifacts that a ZenoLedger operator expects peers to enforce.
    """

    body = {
        "schema": TAU_RULE_COMMITMENT_SCHEMA_V0,
        "tau_network_id": _require_str(tau_network_id, name="tau_network_id"),
        "tau_adapter_ref": _require_str(tau_adapter_ref, name="tau_adapter_ref"),
        "tau_language_semantics_ref": _require_str(
            tau_language_semantics_ref,
            name="tau_language_semantics_ref",
        ),
        "semantic_contracts_hash": hash_v0("tau_rule_semantic_contracts_v0", dict(semantic_contracts)),
        "supported_runtime_contract_hash": hash_v0(
            "tau_rule_supported_runtime_contract_v0",
            dict(supported_runtime_contract),
        ),
        "spec_profiles_hash": hash_v0("tau_rule_spec_profiles_v0", dict(spec_profiles)),
        "active_spec_inventory_hash": hash_v0(
            "tau_rule_active_spec_inventory_v0",
            dict(active_spec_inventory),
        ),
    }
    return {**body, "tau_rule_commitment_hash": _tau_rule_commitment_hash_v0(body)}


def validate_tau_rule_commitment_v0(
    commitment: Mapping[str, Any],
    *,
    expected_tau_network_id: str,
    expected_tau_adapter_ref: str,
    expected_tau_rule_commitment_hash: str,
) -> None:
    if not isinstance(commitment, Mapping):
        raise TypeError("tau_rule_commitment must be a JSON object")
    obj = dict(commitment)
    expected_keys = {
        "schema",
        "tau_network_id",
        "tau_adapter_ref",
        "tau_language_semantics_ref",
        "semantic_contracts_hash",
        "supported_runtime_contract_hash",
        "spec_profiles_hash",
        "active_spec_inventory_hash",
        "tau_rule_commitment_hash",
    }
    if set(obj.keys()) != expected_keys:
        raise ValueError("tau_rule_commitment_keys_mismatch")
    if obj.get("schema") != TAU_RULE_COMMITMENT_SCHEMA_V0:
        raise ValueError("tau_rule_commitment_schema_mismatch")
    if obj.get("tau_network_id") != expected_tau_network_id:
        raise ValueError("tau_rule_commitment_tau_network_id_mismatch")
    if obj.get("tau_adapter_ref") != expected_tau_adapter_ref:
        raise ValueError("tau_rule_commitment_tau_adapter_ref_mismatch")
    _require_str(obj.get("tau_language_semantics_ref"), name="tau_language_semantics_ref")
    for key in (
        "semantic_contracts_hash",
        "supported_runtime_contract_hash",
        "spec_profiles_hash",
        "active_spec_inventory_hash",
        "tau_rule_commitment_hash",
    ):
        _require_root(obj.get(key), name=key)
    if obj["tau_rule_commitment_hash"] != _tau_rule_commitment_hash_v0(obj):
        raise ValueError("tau_rule_commitment_hash_mismatch")
    if obj["tau_rule_commitment_hash"] != _require_root(
        expected_tau_rule_commitment_hash,
        name="expected_tau_rule_commitment_hash",
    ):
        raise ValueError("tau_rule_commitment_hash_mismatch")


def build_tau_export_packet_v0(
    *,
    checkpoint: Mapping[str, Any],
    header: Mapping[str, Any],
    body: Mapping[str, Any],
    profile: Mapping[str, Any],
    tau_network_id: str,
    tau_adapter_ref: str,
) -> dict[str, Any]:
    """Build a deterministic Tau-facing export packet.

    The packet is a handoff contract. It binds ZenoLedger roots to a named Tau
    network and adapter reference without assuming Tau has accepted any plugin.
    """

    checkpoint_obj = dict(checkpoint)
    header_obj = dict(header)
    body_obj = dict(body)
    profile_obj = dict(profile)
    validate_header_body_roots_v0(header_obj, body_obj)
    validate_checkpoint_header_binding_v0(checkpoint_obj, header_obj)
    validate_checkpoint_admission_v0(checkpoint=checkpoint_obj, profile=profile_obj)

    if not isinstance(tau_network_id, str) or tau_network_id == "":
        raise ValueError("tau_network_id must be a non-empty string")
    if not isinstance(tau_adapter_ref, str) or tau_adapter_ref == "":
        raise ValueError("tau_adapter_ref must be a non-empty string")

    packet_body = {
        "schema": TAU_EXPORT_PACKET_SCHEMA_V0,
        "packet_kind": TAU_EXPORT_PACKET_KIND_V0,
        "adapter_contract": TAU_EXPORT_ADAPTER_CONTRACT_V0,
        "tau_network_id": tau_network_id,
        "tau_adapter_ref": tau_adapter_ref,
        "profile_id": profile_obj["profile_id"],
        "deployment_mode": profile_obj["deployment_mode"],
        "chain_id": checkpoint_obj["chain_id"],
        "height": checkpoint_obj["height"],
        "header_hash": checkpoint_obj["header_hash"],
        "app_hash": checkpoint_obj["app_hash"],
        "post_state_root": checkpoint_obj["post_state_root"],
        "body_root": checkpoint_obj["body_root"],
        "evidence_root": checkpoint_obj["evidence_root"],
        "config_digest": checkpoint_obj["config_digest"],
        "proof_journal_hash": checkpoint_obj["proof_journal_hash"],
        "body_payload_root": canonical_body_root_v0(body_obj),
        "tau_admission": {
            "status": "handoff_only",
            "requires_tau_adapter_verification": True,
            "requires_tau_plugin_acceptance": True,
            "requires_tau_state_hash_assignment": True,
        },
        "tau_state_proof_hint": {
            "proof_type": "zenoledger.checkpoint.v0",
            "committed_app_hash": checkpoint_obj["app_hash"],
            "committed_body_root": checkpoint_obj["body_root"],
            "committed_header_hash": checkpoint_obj["header_hash"],
            "tau_state_hash_status": "unassigned",
        },
    }
    return {**packet_body, "packet_hash": hash_v0("tau_export_packet_v0", packet_body)}


def validate_tau_export_packet_v0(
    *,
    packet: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    header: Mapping[str, Any],
    body: Mapping[str, Any],
    profile: Mapping[str, Any],
) -> None:
    if not isinstance(packet, Mapping):
        raise TypeError("packet must be a JSON object")
    tau_network_id = packet.get("tau_network_id")
    tau_adapter_ref = packet.get("tau_adapter_ref")
    if not isinstance(tau_network_id, str) or tau_network_id == "":
        raise ValueError("packet tau_network_id must be a non-empty string")
    if not isinstance(tau_adapter_ref, str) or tau_adapter_ref == "":
        raise ValueError("packet tau_adapter_ref must be a non-empty string")
    expected = build_tau_export_packet_v0(
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        tau_network_id=tau_network_id,
        tau_adapter_ref=tau_adapter_ref,
    )
    if dict(packet) != expected:
        raise ValueError("Tau export packet binding mismatch")
