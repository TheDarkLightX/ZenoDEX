from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Mapping

from src.fire.verifier.settlement_v1 import (
    FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
    FireSettlementPacket,
    verify_fire_settlement_authority_packet,
    verify_fire_settlement_packet,
)


FIRE_APPLY_RECEIPT_SCHEMA = "zenodex/fire-apply-receipt/v1"


def _require_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_sha256_prefixed(name: str, value: object) -> str:
    if not isinstance(value, str) or not value.startswith("sha256:"):
        raise ValueError(f"{name} must be a sha256:... string")
    digest = value.removeprefix("sha256:")
    if len(digest) != 64:
        raise ValueError(f"{name} must be a sha256:... string")
    try:
        int(digest, 16)
    except ValueError as exc:
        raise ValueError(f"{name} must be a sha256:... string") from exc
    return value


def _canonical_json_bytes(payload: Mapping[str, object]) -> bytes:
    return json.dumps(dict(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


@dataclass(frozen=True)
class FireApplyReceipt:
    packet_hash: str
    holder_balance_before: int
    writer_balance_before: int
    holder_balance_after: int
    writer_balance_after: int
    receipt_hash: str
    schema: str = FIRE_APPLY_RECEIPT_SCHEMA

    def __post_init__(self) -> None:
        object.__setattr__(self, "packet_hash", _require_sha256_prefixed("packet_hash", self.packet_hash))
        object.__setattr__(self, "holder_balance_before", _require_int("holder_balance_before", self.holder_balance_before))
        object.__setattr__(self, "writer_balance_before", _require_int("writer_balance_before", self.writer_balance_before))
        object.__setattr__(self, "holder_balance_after", _require_int("holder_balance_after", self.holder_balance_after))
        object.__setattr__(self, "writer_balance_after", _require_int("writer_balance_after", self.writer_balance_after))
        object.__setattr__(self, "receipt_hash", _require_sha256_prefixed("receipt_hash", self.receipt_hash))
        if self.schema != FIRE_APPLY_RECEIPT_SCHEMA:
            raise ValueError(f"unsupported apply receipt schema: {self.schema}")

    def payload_without_hash(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "packet_hash": self.packet_hash,
            "holder_balance_before": self.holder_balance_before,
            "writer_balance_before": self.writer_balance_before,
            "holder_balance_after": self.holder_balance_after,
            "writer_balance_after": self.writer_balance_after,
        }

    def to_dict(self) -> dict[str, object]:
        payload = self.payload_without_hash()
        payload["receipt_hash"] = self.receipt_hash
        return payload

    @classmethod
    def build(
        cls,
        *,
        packet_hash: str,
        holder_balance_before: int,
        writer_balance_before: int,
        holder_balance_after: int,
        writer_balance_after: int,
    ) -> "FireApplyReceipt":
        payload_without_hash: dict[str, object] = {
            "schema": FIRE_APPLY_RECEIPT_SCHEMA,
            "packet_hash": _require_sha256_prefixed("packet_hash", packet_hash),
            "holder_balance_before": _require_int("holder_balance_before", holder_balance_before),
            "writer_balance_before": _require_int("writer_balance_before", writer_balance_before),
            "holder_balance_after": _require_int("holder_balance_after", holder_balance_after),
            "writer_balance_after": _require_int("writer_balance_after", writer_balance_after),
        }
        return cls(
            packet_hash=packet_hash,
            holder_balance_before=holder_balance_before,
            writer_balance_before=writer_balance_before,
            holder_balance_after=holder_balance_after,
            writer_balance_after=writer_balance_after,
            receipt_hash=_sha256_bytes(_canonical_json_bytes(payload_without_hash)),
        )

    @classmethod
    def from_dict(cls, payload: object) -> "FireApplyReceipt":
        if not isinstance(payload, Mapping):
            raise TypeError("apply receipt payload must be a mapping")
        return cls(
            schema=payload.get("schema", FIRE_APPLY_RECEIPT_SCHEMA),
            packet_hash=payload.get("packet_hash"),
            holder_balance_before=payload.get("holder_balance_before"),
            writer_balance_before=payload.get("writer_balance_before"),
            holder_balance_after=payload.get("holder_balance_after"),
            writer_balance_after=payload.get("writer_balance_after"),
            receipt_hash=payload.get("receipt_hash"),
        )


def verify_fire_apply_receipt(
    receipt: FireApplyReceipt,
    *,
    packet: FireSettlementPacket,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
    expected_command_tag: str | None = "firev_accept_and_settle",
    require_witness_hash: bool = False,
) -> tuple[bool, str | None]:
    if not isinstance(receipt, FireApplyReceipt):
        raise TypeError("receipt must be a FireApplyReceipt")
    if not isinstance(packet, FireSettlementPacket):
        raise TypeError("packet must be a FireSettlementPacket")
    ok, err = verify_fire_settlement_packet(
        packet,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        expected_command_tag=expected_command_tag,
        require_witness_hash=require_witness_hash,
    )
    if not ok:
        return False, f"packet_{err or 'invalid'}"
    if receipt.packet_hash != packet.packet_hash:
        return False, "packet_hash_mismatch"
    if receipt.holder_balance_after != receipt.holder_balance_before + packet.holder_delta:
        return False, "holder_balance_transition_mismatch"
    if receipt.writer_balance_after != receipt.writer_balance_before + packet.writer_delta:
        return False, "writer_balance_transition_mismatch"
    expected_receipt_hash = _sha256_bytes(_canonical_json_bytes(receipt.payload_without_hash()))
    if receipt.receipt_hash != expected_receipt_hash:
        return False, "receipt_hash_mismatch"
    return True, None


def verify_fire_authority_apply_receipt(
    receipt: FireApplyReceipt,
    *,
    packet: FireSettlementPacket,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
    expected_command_tag: str = FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
) -> tuple[bool, str | None]:
    if not isinstance(receipt, FireApplyReceipt):
        raise TypeError("receipt must be a FireApplyReceipt")
    if not isinstance(packet, FireSettlementPacket):
        raise TypeError("packet must be a FireSettlementPacket")
    ok, err = verify_fire_settlement_authority_packet(
        packet,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        expected_command_tag=expected_command_tag,
    )
    if not ok:
        return False, f"packet_{err or 'invalid'}"
    if receipt.packet_hash != packet.packet_hash:
        return False, "packet_hash_mismatch"
    if receipt.holder_balance_after != receipt.holder_balance_before + packet.holder_delta:
        return False, "holder_balance_transition_mismatch"
    if receipt.writer_balance_after != receipt.writer_balance_before + packet.writer_delta:
        return False, "writer_balance_transition_mismatch"
    expected_receipt_hash = _sha256_bytes(_canonical_json_bytes(receipt.payload_without_hash()))
    if receipt.receipt_hash != expected_receipt_hash:
        return False, "receipt_hash_mismatch"
    return True, None


__all__ = [
    "FIRE_APPLY_RECEIPT_SCHEMA",
    "FireApplyReceipt",
    "verify_fire_authority_apply_receipt",
    "verify_fire_apply_receipt",
]
