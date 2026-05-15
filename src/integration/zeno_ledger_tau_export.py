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


TAU_EXPORT_PACKET_SCHEMA_V0 = "zenodex/zeno_ledger/tau_export_packet/v0"
TAU_EXPORT_PACKET_KIND_V0 = "zenoledger_checkpoint_for_tau"
TAU_EXPORT_ADAPTER_CONTRACT_V0 = "zenoledger_tau_adapter_v0"


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
