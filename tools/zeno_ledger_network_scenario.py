#!/usr/bin/env python3
"""Deterministic ZenoLedger adversarial network scenario model."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from typing import Any, Iterable


GENESIS_HASH = "0x" + "00" * 32
VALID_AUTH_TOKEN = "valid"


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
    return isinstance(value, str) and value.startswith("0x") and len(value) == 66


def _fake_hash(seed: str) -> str:
    import hashlib

    return "0x" + hashlib.sha256(seed.encode("utf-8")).hexdigest()
