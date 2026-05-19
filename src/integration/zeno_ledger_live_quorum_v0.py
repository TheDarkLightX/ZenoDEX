"""Live checkpoint quorum admission for ZenoLedger v0."""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_signer_registry import verify_signature_quorum_v0
from src.integration.zeno_ledger_v0 import (
    canonical_header_hash_v0,
    hash_v0,
    validate_checkpoint_header_binding_v0,
)


LIVE_CHECKPOINT_QUORUM_ADMISSION_SCHEMA_V0 = "zenodex/zeno_ledger/live_checkpoint_quorum_admission/v0"


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_sequence(value: object, *, name: str) -> Sequence[object]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence")
    return value


def build_live_checkpoint_quorum_admission_v0(
    *,
    header: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    registry: Mapping[str, Any],
    envelopes: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    """Admit a live checkpoint only when its header hash has signer quorum."""

    header_obj = dict(_require_mapping(header, name="header"))
    checkpoint_obj = dict(_require_mapping(checkpoint, name="checkpoint"))
    validate_checkpoint_header_binding_v0(checkpoint_obj, header_obj)
    header_hash = canonical_header_hash_v0(header_obj)
    if checkpoint_obj["header_hash"] != header_hash:
        raise ValueError("checkpoint header_hash mismatch")
    envelope_items = [
        _require_mapping(envelope, name=f"envelopes[{index}]")
        for index, envelope in enumerate(_require_sequence(envelopes, name="envelopes"))
    ]
    quorum_report = verify_signature_quorum_v0(
        registry=_require_mapping(registry, name="registry"),
        payload_kind="checkpoint",
        payload_hash=header_hash,
        envelopes=envelope_items,
    )
    body = {
        "schema": LIVE_CHECKPOINT_QUORUM_ADMISSION_SCHEMA_V0,
        "ok": True,
        "status": "accepted",
        "chain_id": header_obj["chain_id"],
        "height": header_obj["height"],
        "header_hash": header_hash,
        "checkpoint_header_hash": checkpoint_obj["header_hash"],
        "registry_hash": quorum_report["registry_hash"],
        "threshold": quorum_report["threshold"],
        "accepted_weight": quorum_report["accepted_weight"],
        "accepted_signature_count": len(quorum_report["accepted_signatures"]),
        "quorum_report_hash": quorum_report["quorum_report_hash"],
        "quorum_report": quorum_report,
    }
    return {**body, "admission_hash": hash_v0("live_checkpoint_quorum_admission_v0", body)}


def validate_live_checkpoint_quorum_admission_v0(
    *,
    admission: Mapping[str, Any],
    header: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    registry: Mapping[str, Any],
    envelopes: Sequence[Mapping[str, Any]],
) -> None:
    obj = _require_mapping(admission, name="admission")
    if obj.get("schema") != LIVE_CHECKPOINT_QUORUM_ADMISSION_SCHEMA_V0:
        raise ValueError("live checkpoint quorum admission schema mismatch")
    expected = build_live_checkpoint_quorum_admission_v0(
        header=header,
        checkpoint=checkpoint,
        registry=registry,
        envelopes=envelopes,
    )
    if dict(obj) != expected:
        raise ValueError("live checkpoint quorum admission binding mismatch")
