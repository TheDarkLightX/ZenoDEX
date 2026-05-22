#!/usr/bin/env python3
"""Deterministic ZenoLedger adversarial network scenario model."""

from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from dataclasses import dataclass, field
from typing import Any, Iterable

from src.integration.zeno_ledger_tau_export import validate_tau_rule_commitment_v0


GENESIS_HASH = "0x" + "00" * 32
VALID_AUTH_TOKEN = "valid"
RECOVERY_CERTIFICATE_SCHEMA = "zenodex.zeno_ledger.recovery_certificate.v0"
RECOVERY_CERTIFICATE_DOMAIN = "zeno-ledger-recovery-certificate-v0"
RECOVERY_AMOUNT_CAP = 10
RISK_COMPONENTS = (
    "value_loss",
    "replay_exposure",
    "stale_data",
    "authority_drift",
    "liquidity_shock",
    "resource_load",
    "semantic_ambiguity",
)


@dataclass(frozen=True)
class BlockEnvelope:
    envelope_id: str
    height: int
    previous_hash: str
    block_hash: str
    proposer_id: str
    body_root: str
    checkpoint_hash: str
    tx_count: int = 1
    auth_token: str = VALID_AUTH_TOKEN


@dataclass
class NodeModel:
    node_id: str
    network_id: str
    chain_id: str
    height: int = 0
    tip_hash: str = GENESIS_HASH
    peers: set[str] = field(default_factory=set)
    seen_envelopes: set[str] = field(default_factory=set)
    accepted_by_height: dict[int, str] = field(default_factory=dict)
    rejections_by_reason: Counter[str] = field(default_factory=Counter)
    equivocation_events: list[dict[str, Any]] = field(default_factory=list)
    slashing_receipts: list[dict[str, Any]] = field(default_factory=list)
    accepted_blocks: int = 0
    risk_profile: dict[str, int] = field(
        default_factory=lambda: {
            "value_loss": 0,
            "replay_exposure": 0,
            "stale_data": 0,
            "authority_drift": 0,
            "liquidity_shock": 0,
            "resource_load": 0,
            "semantic_ambiguity": 0,
        }
    )
    isolated_peers: set[str] = field(default_factory=set)
    used_recovery_certificate_signatures: set[str] = field(default_factory=set)


class ChaosNetworkModel:
    def __init__(
        self,
        *,
        network_id: str = "zeno-ledger-chaos-v0",
        chain_id: str = "zeno-ledger-chaos-v0",
        validators: Iterable[str] = ("validator-a", "validator-b", "validator-c"),
        peer_cap: int = 4,
        max_tx_count: int = 100,
        checkpoint_quorum: int = 2,
    ) -> None:
        self.network_id = network_id
        self.chain_id = chain_id
        self.validators = tuple(validators)
        if not self.validators:
            raise ValueError("validators must not be empty")
        self.peer_cap = peer_cap
        self.max_tx_count = max_tx_count
        self.checkpoint_quorum = checkpoint_quorum
        self.nodes: dict[str, NodeModel] = {}
        self.metrics: Counter[str] = Counter()

    def add_node(self, node_id: str) -> NodeModel:
        if node_id in self.nodes:
            raise ValueError("duplicate node_id")
        node = NodeModel(node_id=node_id, network_id=self.network_id, chain_id=self.chain_id)
        self.nodes[node_id] = node
        return node

    def node(self, node_id: str) -> NodeModel:
        try:
            return self.nodes[node_id]
        except KeyError as exc:
            raise KeyError(f"unknown node_id: {node_id}") from exc

    def scheduled_proposer(self, height: int) -> str:
        if height <= 0:
            raise ValueError("height must be positive")
        return self.validators[(height - 1) % len(self.validators)]

    def make_block(self, *, node_id: str, height: int | None = None, salt: str = "ok", proposer_id: str | None = None) -> BlockEnvelope:
        node = self.node(node_id)
        next_height = node.height + 1 if height is None else height
        proposer = proposer_id or self.scheduled_proposer(next_height)
        previous = node.tip_hash if next_height == node.height + 1 else f"0x{'ff' * 32}"
        return BlockEnvelope(
            envelope_id=f"{node_id}:{next_height}:{salt}",
            height=next_height,
            previous_hash=previous,
            block_hash=_fake_hash(f"{node_id}:{next_height}:{salt}"),
            proposer_id=proposer,
            body_root=_fake_hash(f"body:{node_id}:{next_height}:{salt}"),
            checkpoint_hash=_fake_hash(f"checkpoint:{node_id}:{next_height}:{salt}"),
        )

    def admit_peer(self, *, node_id: str, peer_id: str, peer_network_id: str | None = None, peer_chain_id: str | None = None) -> dict[str, Any]:
        node = self.node(node_id)
        errors: list[str] = []
        if peer_network_id is not None and peer_network_id != self.network_id:
            errors.append("peer_network_id_mismatch")
        if peer_chain_id is not None and peer_chain_id != self.chain_id:
            errors.append("peer_chain_id_mismatch")
        if peer_id in node.peers:
            errors.append("duplicate_peer")
        if len(node.peers) >= self.peer_cap:
            errors.append("peer_cap_exceeded")
        if errors:
            for error in errors:
                node.rejections_by_reason[error] += 1
                self.metrics[f"peer_rejected:{error}"] += 1
            return {"ok": False, "errors": errors}
        node.peers.add(peer_id)
        self.metrics["peer_admitted"] += 1
        return {"ok": True, "errors": []}

    def submit_block(self, *, node_id: str, envelope: BlockEnvelope) -> dict[str, Any]:
        node = self.node(node_id)
        errors: list[str] = []
        if envelope.envelope_id in node.seen_envelopes:
            errors.append("duplicate_gossip_envelope")
        if envelope.auth_token != VALID_AUTH_TOKEN:
            errors.append("auth_failed")
        if envelope.tx_count > self.max_tx_count:
            errors.append("gossip_oversized_tx_count")
        if envelope.height <= 0:
            errors.append("invalid_height")
        elif envelope.proposer_id != self.scheduled_proposer(envelope.height):
            errors.append("wrong_proposer")
        accepted_hash = node.accepted_by_height.get(envelope.height)
        if accepted_hash is not None and accepted_hash != envelope.block_hash:
            errors.append("same_height_conflict")
            event = {
                "node_id": node_id,
                "height": envelope.height,
                "accepted_hash": accepted_hash,
                "conflicting_hash": envelope.block_hash,
            }
            node.equivocation_events.append(event)
            node.slashing_receipts.append({**event, "reason": "same_height_conflict"})
        if envelope.height != node.height + 1:
            errors.append("non_extending_height")
        if envelope.previous_hash != node.tip_hash:
            errors.append("wrong_previous_hash")
        if not _looks_hash(envelope.body_root):
            errors.append("wrong_body_root")
        if not _looks_hash(envelope.checkpoint_hash):
            errors.append("wrong_checkpoint")

        node.seen_envelopes.add(envelope.envelope_id)
        if errors:
            for error in errors:
                node.rejections_by_reason[error] += 1
                self.metrics[f"block_rejected:{error}"] += 1
            return {"ok": False, "errors": errors}

        node.height = envelope.height
        node.tip_hash = envelope.block_hash
        node.accepted_by_height[envelope.height] = envelope.block_hash
        node.accepted_blocks += 1
        self.metrics["block_accepted"] += 1
        return {"ok": True, "errors": []}

    def checkpoint_quorum_check(self, *, node_id: str, payload_hash: str, signers: Iterable[str]) -> dict[str, Any]:
        node = self.node(node_id)
        signer_list = list(signers)
        errors: list[str] = []
        if len(signer_list) != len(set(signer_list)):
            errors.append("duplicate_checkpoint_signer")
        unknown = sorted(set(signer_list) - set(self.validators))
        if unknown:
            errors.append("unknown_checkpoint_signer")
        if len(set(signer_list) & set(self.validators)) < self.checkpoint_quorum:
            errors.append("checkpoint_quorum_missing")
        if not _looks_hash(payload_hash):
            errors.append("checkpoint_payload_hash_invalid")
        if errors:
            for error in errors:
                node.rejections_by_reason[error] += 1
                self.metrics[f"checkpoint_rejected:{error}"] += 1
            return {"ok": False, "errors": errors}
        self.metrics["checkpoint_accepted"] += 1
        return {"ok": True, "errors": []}

    def build_recovery_certificate(
        self,
        *,
        node_id: str,
        next_risk: dict[str, int],
        expiration_epoch: int,
        recovery_amount: int,
    ) -> dict[str, Any]:
        self.node(node_id)
        certificate = {
            "schema": RECOVERY_CERTIFICATE_SCHEMA,
            "network_id": self.network_id,
            "chain_id": self.chain_id,
            "node_id": node_id,
            "next_risk": _normalize_risk_profile(next_risk),
            "expiration_epoch": expiration_epoch,
            "recovery_amount": recovery_amount,
        }
        certificate["signature"] = _model_signature(certificate)
        return certificate

    def validate_risk_transition(
        self,
        *,
        node_id: str,
        next_risk: dict[str, int],
        certificate: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        node = self.node(node_id)
        errors: list[str] = []
        cert_errors: list[str] = []
        normalized_next_risk: dict[str, int] = {}
        risk_delta_total = 0
        risk_increased = False

        for component, val in next_risk.items():
            if component not in node.risk_profile:
                errors.append("risk_component_unknown")
                continue
            if not isinstance(val, int) or isinstance(val, bool) or val < 0:
                errors.append("risk_value_invalid")
                continue
            current_val = node.risk_profile[component]
            normalized_next_risk[component] = val
            if val > current_val:
                risk_increased = True
                risk_delta_total += val - current_val

        cert_ok = False
        if certificate is not None:
            if certificate.get("schema") != RECOVERY_CERTIFICATE_SCHEMA:
                cert_errors.append("invalid_certificate_schema")
            if certificate.get("network_id") != self.network_id:
                cert_errors.append("certificate_network_mismatch")
            if certificate.get("chain_id") != self.chain_id:
                cert_errors.append("certificate_chain_mismatch")
            if certificate.get("node_id") != node_id:
                cert_errors.append("certificate_node_mismatch")
            if certificate.get("next_risk") != normalized_next_risk:
                cert_errors.append("certificate_risk_mismatch")
            expiration_epoch = certificate.get("expiration_epoch")
            if (
                not isinstance(expiration_epoch, int)
                or isinstance(expiration_epoch, bool)
                or expiration_epoch <= node.height
            ):
                cert_errors.append("certificate_expired")
            recovery_amount = certificate.get("recovery_amount")
            if not isinstance(recovery_amount, int) or isinstance(recovery_amount, bool) or recovery_amount < 0:
                cert_errors.append("recovery_amount_invalid")
            elif recovery_amount > RECOVERY_AMOUNT_CAP:
                cert_errors.append("recovery_cap_exceeded")
            elif risk_delta_total > 0 and recovery_amount < risk_delta_total:
                cert_errors.append("recovery_amount_insufficient")
            signature = certificate.get("signature")
            if signature != _model_signature(certificate):
                cert_errors.append("invalid_certificate_signature")
            elif signature in node.used_recovery_certificate_signatures:
                cert_errors.append("certificate_replay")
            cert_ok = not cert_errors

        if risk_increased and not cert_ok:
            if not cert_errors:
                errors.append("risk_increased_without_certificate")
        errors.extend(cert_errors)

        if errors:
            for error in errors:
                node.rejections_by_reason[error] += 1
                self.metrics[f"risk_transition_rejected:{error}"] += 1
            return {"ok": False, "errors": errors}

        for component, val in normalized_next_risk.items():
            node.risk_profile[component] = val
        if certificate is not None:
            node.used_recovery_certificate_signatures.add(str(certificate["signature"]))
        self.metrics["risk_transition_accepted"] += 1
        return {"ok": True, "errors": []}

    def validate_tau_rule_commitment(
        self,
        *,
        node_id: str,
        commitment: dict[str, Any],
        expected_tau_network_id: str,
        expected_tau_adapter_ref: str,
        expected_tau_rule_commitment_hash: str,
    ) -> dict[str, Any]:
        node = self.node(node_id)
        try:
            validate_tau_rule_commitment_v0(
                commitment,
                expected_tau_network_id=expected_tau_network_id,
                expected_tau_adapter_ref=expected_tau_adapter_ref,
                expected_tau_rule_commitment_hash=expected_tau_rule_commitment_hash,
            )
        except Exception as exc:
            reason = _stable_reason(str(exc))
            node.rejections_by_reason[reason] += 1
            self.metrics[f"tau_rule_rejected:{reason}"] += 1
            return {"ok": False, "errors": [reason]}
        self.metrics["tau_rule_accepted"] += 1
        return {"ok": True, "errors": []}

    def partition_node(self, *, node_id: str, peer_id: str) -> None:
        node = self.node(node_id)
        peer = self.node(peer_id)
        node.isolated_peers.add(peer_id)
        peer.isolated_peers.add(node_id)
        self.metrics["network_partitioned"] += 1

    def heal_partition(self, *, node_id: str, peer_id: str) -> None:
        node = self.node(node_id)
        peer = self.node(peer_id)
        node.isolated_peers.discard(peer_id)
        peer.isolated_peers.discard(node_id)
        self.metrics["network_healed"] += 1

    def reconcile_after_heal(self, *, node_id: str, peer_id: str) -> dict[str, Any]:
        node = self.node(node_id)
        peer = self.node(peer_id)
        if peer_id in node.isolated_peers or node_id in peer.isolated_peers:
            node.rejections_by_reason["peer_still_partitioned"] += 1
            self.metrics["network_reconciled:peer_still_partitioned"] += 1
            return {"ok": False, "errors": ["peer_still_partitioned"]}
        if node.height == peer.height and node.tip_hash == peer.tip_hash:
            self.metrics["network_reconciled:same_tip"] += 1
            return {"ok": True, "errors": []}
        if node.height == peer.height:
            event = {
                "node_id": node_id,
                "peer_id": peer_id,
                "height": node.height,
                "local_tip_hash": node.tip_hash,
                "peer_tip_hash": peer.tip_hash,
                "reason": "partition_same_height_conflict",
            }
            node.equivocation_events.append(event)
            peer.equivocation_events.append({**event, "node_id": peer_id, "peer_id": node_id})
            node.slashing_receipts.append(event)
            peer.slashing_receipts.append({**event, "node_id": peer_id, "peer_id": node_id})
            self.metrics["network_reconciled:fork_evidence"] += 1
            return {"ok": True, "errors": [], "evidence": "partition_fork_evidence"}
        self.metrics["network_reconciled:height_divergence"] += 1
        return {"ok": False, "errors": ["partition_height_divergence"]}

    def report(self) -> dict[str, Any]:
        nodes = {
            node_id: {
                "height": node.height,
                "tip_hash": node.tip_hash,
                "peer_count": len(node.peers),
                "seen_envelope_count": len(node.seen_envelopes),
                "accepted_blocks": node.accepted_blocks,
                "rejections_by_reason": dict(sorted(node.rejections_by_reason.items())),
                "equivocation_event_count": len(node.equivocation_events),
                "slashing_receipt_count": len(node.slashing_receipts),
                "risk_profile": dict(node.risk_profile),
                "isolated_peers": sorted(node.isolated_peers),
                "used_recovery_certificate_count": len(node.used_recovery_certificate_signatures),
            }
            for node_id, node in sorted(self.nodes.items())
        }
        return {
            "schema": "zenodex.zeno_ledger.chaos_network_model_report.v0",
            "network_id": self.network_id,
            "chain_id": self.chain_id,
            "metrics": dict(sorted(self.metrics.items())),
            "nodes": nodes,
        }


def _looks_hash(value: str) -> bool:
    return (
        isinstance(value, str)
        and value.startswith("0x")
        and len(value) == 66
        and all(char in "0123456789abcdef" for char in value[2:])
    )


def _fake_hash(seed: str) -> str:
    return "0x" + hashlib.sha256(seed.encode("utf-8")).hexdigest()


def _normalize_risk_profile(risk_profile: dict[str, int]) -> dict[str, int]:
    normalized: dict[str, int] = {}
    for component, val in risk_profile.items():
        if component not in RISK_COMPONENTS:
            raise ValueError(f"unknown risk component: {component}")
        if not isinstance(val, int) or isinstance(val, bool) or val < 0:
            raise ValueError(f"invalid risk value for {component}")
        normalized[component] = val
    return dict(sorted(normalized.items()))


def _model_signature(certificate: dict[str, Any]) -> str:
    unsigned = {key: value for key, value in certificate.items() if key != "signature"}
    payload = {
        "domain": RECOVERY_CERTIFICATE_DOMAIN,
        "certificate": unsigned,
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return "model-sig:" + hashlib.sha256(encoded).hexdigest()


def _stable_reason(error: str) -> str:
    raw = str(error).strip().lower() or "unknown"
    return re.sub(r"[^a-z0-9_]+", "_", raw).strip("_")[:160] or "unknown"
