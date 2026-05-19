"""Hash-bound block gossip envelopes for ZenoLedger public nodes."""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_ledger_v0 import (
    canonical_body_root_v0,
    canonical_header_hash_v0,
    hash_v0,
    validate_body_v0,
    validate_checkpoint_header_binding_v0,
    validate_header_v0,
)


BLOCK_GOSSIP_ENVELOPE_SCHEMA_V0 = "zenodex/zeno_ledger/block_gossip_envelope/v0"


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or (value == "" and not allow_empty):
        requirement = "a str" if allow_empty else "a non-empty str"
        raise ValueError(f"{name} must be {requirement}")
    return value


def _artifact_hash(domain: str, value: Mapping[str, Any]) -> str:
    return hash_v0(domain, dict(value))


def _block_gossip_envelope_hash_v0(envelope: Mapping[str, Any]) -> str:
    body = {key: value for key, value in dict(envelope).items() if key != "envelope_hash"}
    return hash_v0("zeno_ledger_block_gossip_envelope_v0", body)


def build_block_gossip_envelope_v0(
    *,
    header: Mapping[str, Any],
    body: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    source_node_id: str,
    source_peer_url: str = "",
) -> dict[str, Any]:
    """Build a canonical block-gossip envelope over one header/body/checkpoint."""

    header_obj = dict(_require_mapping(header, name="header"))
    body_obj = dict(_require_mapping(body, name="body"))
    checkpoint_obj = dict(_require_mapping(checkpoint, name="checkpoint"))
    validate_header_v0(header_obj)
    validate_body_v0(body_obj)
    validate_checkpoint_header_binding_v0(checkpoint_obj, header_obj)
    if header_obj["chain_id"] != body_obj["chain_id"]:
        raise ValueError("gossip header chain_id does not match body")
    if int(header_obj["height"]) != int(body_obj["height"]):
        raise ValueError("gossip header height does not match body")
    body_root = canonical_body_root_v0(body_obj)
    if header_obj["body_root"] != body_root:
        raise ValueError("gossip header body_root does not match body")
    header_hash = canonical_header_hash_v0(header_obj)
    envelope = {
        "schema": BLOCK_GOSSIP_ENVELOPE_SCHEMA_V0,
        "ok": True,
        "status": "accepted",
        "source_node_id": _require_str(source_node_id, name="source_node_id"),
        "source_peer_url": _require_str(source_peer_url, name="source_peer_url", allow_empty=True),
        "chain_id": header_obj["chain_id"],
        "height": int(header_obj["height"]),
        "header_hash": header_hash,
        "body_root": body_root,
        "header_artifact_hash": _artifact_hash("zeno_ledger_gossip_header_v0", header_obj),
        "body_artifact_hash": _artifact_hash("zeno_ledger_gossip_body_v0", body_obj),
        "checkpoint_artifact_hash": _artifact_hash("zeno_ledger_gossip_checkpoint_v0", checkpoint_obj),
        "header": header_obj,
        "body": body_obj,
        "checkpoint": checkpoint_obj,
    }
    return {**envelope, "envelope_hash": _block_gossip_envelope_hash_v0(envelope)}


def validate_block_gossip_envelope_v0(envelope: Mapping[str, Any]) -> None:
    """Validate block-gossip envelope shape, artifact binding, and hash binding."""

    obj = dict(_require_mapping(envelope, name="block_gossip_envelope"))
    if obj.get("schema") != BLOCK_GOSSIP_ENVELOPE_SCHEMA_V0:
        raise ValueError("block gossip envelope schema mismatch")
    if obj.get("ok") is not True or obj.get("status") != "accepted":
        raise ValueError("block gossip envelope status mismatch")
    expected = build_block_gossip_envelope_v0(
        header=_require_mapping(obj.get("header"), name="block_gossip_envelope.header"),
        body=_require_mapping(obj.get("body"), name="block_gossip_envelope.body"),
        checkpoint=_require_mapping(obj.get("checkpoint"), name="block_gossip_envelope.checkpoint"),
        source_node_id=_require_str(obj.get("source_node_id"), name="block_gossip_envelope.source_node_id"),
        source_peer_url=_require_str(
            obj.get("source_peer_url"),
            name="block_gossip_envelope.source_peer_url",
            allow_empty=True,
        ),
    )
    if obj != expected:
        raise ValueError("block gossip envelope binding mismatch")
