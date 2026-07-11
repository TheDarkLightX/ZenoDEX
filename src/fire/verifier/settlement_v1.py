from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Mapping


FIRE_VERIFIER_RECEIPT_SCHEMA = "zenodex/fire-verifier-receipt/v1"
FIRE_SETTLEMENT_DELTA_SCHEMA = "zenodex/fire-settlement-deltas/v1"
FIRE_SETTLEMENT_PACKET_SCHEMA = "zenodex/fire-settlement-packet/v1"
FIRE_WITNESS_BINDING_SCHEMA = "zenodex/fire-witness-binding/v1"
FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG = "firev_accept_and_settle"


def _require_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    return value


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


def _authority_expected_witness_hash_error(expected_witness_hash: str | None) -> str | None:
    # DbC precondition: funds-moving authority checks must be bound to a
    # caller-derived witness hash; a self-declared receipt witness is not authority.
    if expected_witness_hash is None:
        return "expected_witness_hash_missing"
    _require_sha256_prefixed("expected_witness_hash", expected_witness_hash)
    return None


def fire_settlement_delta_hash(*, holder_delta: int, writer_delta: int) -> str:
    payload = {
        "schema": FIRE_SETTLEMENT_DELTA_SCHEMA,
        "holder_delta": _require_int("holder_delta", holder_delta),
        "writer_delta": _require_int("writer_delta", writer_delta),
    }
    return _sha256_bytes(_canonical_json_bytes(payload))


def fire_settlement_deltas_conserve(*, holder_delta: int, writer_delta: int) -> bool:
    return _require_int("holder_delta", holder_delta) + _require_int("writer_delta", writer_delta) == 0


def fire_witness_binding_hash(witness_inputs: Mapping[str, object]) -> str:
    if not isinstance(witness_inputs, Mapping):
        raise TypeError("witness_inputs must be a mapping")
    normalized: dict[str, int] = {}
    for key, value in witness_inputs.items():
        if not isinstance(key, str) or not key:
            raise TypeError("witness input names must be non-empty strings")
        normalized[key] = _require_int(f"witness_inputs[{key}]", value)
    payload: dict[str, object] = {
        "schema": FIRE_WITNESS_BINDING_SCHEMA,
        "witness_inputs": dict(sorted(normalized.items())),
    }
    return _sha256_bytes(_canonical_json_bytes(payload))


@dataclass(frozen=True)
class FireVerifierReceipt:
    object_hash: str
    instance_hash: str
    cert_sha256: str
    delta_hash: str
    holder_delta: int
    writer_delta: int
    command_tag: str
    object_name: str
    object_version: str
    receipt_hash: str
    bundle_hash: str | None = None
    witness_hash: str | None = None
    schema: str = FIRE_VERIFIER_RECEIPT_SCHEMA

    def __post_init__(self) -> None:
        object.__setattr__(self, "object_hash", _require_sha256_prefixed("object_hash", self.object_hash))
        object.__setattr__(self, "instance_hash", _require_sha256_prefixed("instance_hash", self.instance_hash))
        object.__setattr__(self, "cert_sha256", _require_sha256_prefixed("cert_sha256", self.cert_sha256))
        object.__setattr__(self, "delta_hash", _require_sha256_prefixed("delta_hash", self.delta_hash))
        object.__setattr__(self, "receipt_hash", _require_sha256_prefixed("receipt_hash", self.receipt_hash))
        object.__setattr__(self, "holder_delta", _require_int("holder_delta", self.holder_delta))
        object.__setattr__(self, "writer_delta", _require_int("writer_delta", self.writer_delta))
        object.__setattr__(self, "command_tag", _require_nonempty_str("command_tag", self.command_tag))
        object.__setattr__(self, "object_name", _require_nonempty_str("object_name", self.object_name))
        object.__setattr__(self, "object_version", _require_nonempty_str("object_version", self.object_version))
        if self.bundle_hash is not None:
            object.__setattr__(self, "bundle_hash", _require_sha256_prefixed("bundle_hash", self.bundle_hash))
        if self.witness_hash is not None:
            object.__setattr__(self, "witness_hash", _require_sha256_prefixed("witness_hash", self.witness_hash))
        if self.schema != FIRE_VERIFIER_RECEIPT_SCHEMA:
            raise ValueError(f"unsupported verifier receipt schema: {self.schema}")

    def payload_without_hash(self) -> dict[str, object]:
        payload: dict[str, object] = {
            "schema": self.schema,
            "object_hash": self.object_hash,
            "instance_hash": self.instance_hash,
            "cert_sha256": self.cert_sha256,
            "delta_hash": self.delta_hash,
            "holder_delta": self.holder_delta,
            "writer_delta": self.writer_delta,
            "command_tag": self.command_tag,
            "object_name": self.object_name,
            "object_version": self.object_version,
        }
        if self.bundle_hash is not None:
            payload["bundle_hash"] = self.bundle_hash
        if self.witness_hash is not None:
            payload["witness_hash"] = self.witness_hash
        return payload

    def to_dict(self) -> dict[str, object]:
        payload = self.payload_without_hash()
        payload["receipt_hash"] = self.receipt_hash
        return payload

    @classmethod
    def build(
        cls,
        *,
        object_hash: str,
        instance_hash: str,
        cert_sha256: str,
        holder_delta: int,
        writer_delta: int,
        command_tag: str,
        object_name: str,
        object_version: str,
        bundle_hash: str | None = None,
        witness_hash: str | None = None,
    ) -> "FireVerifierReceipt":
        holder_delta_i = _require_int("holder_delta", holder_delta)
        writer_delta_i = _require_int("writer_delta", writer_delta)
        if not fire_settlement_deltas_conserve(holder_delta=holder_delta_i, writer_delta=writer_delta_i):
            raise ValueError("delta_nonzero_sum")
        delta_hash = fire_settlement_delta_hash(holder_delta=holder_delta_i, writer_delta=writer_delta_i)
        payload_without_hash: dict[str, object] = {
            "schema": FIRE_VERIFIER_RECEIPT_SCHEMA,
            "object_hash": _require_sha256_prefixed("object_hash", object_hash),
            "instance_hash": _require_sha256_prefixed("instance_hash", instance_hash),
            "cert_sha256": _require_sha256_prefixed("cert_sha256", cert_sha256),
            "delta_hash": delta_hash,
            "holder_delta": holder_delta_i,
            "writer_delta": writer_delta_i,
            "command_tag": _require_nonempty_str("command_tag", command_tag),
            "object_name": _require_nonempty_str("object_name", object_name),
            "object_version": _require_nonempty_str("object_version", object_version),
        }
        if bundle_hash is not None:
            payload_without_hash["bundle_hash"] = _require_sha256_prefixed("bundle_hash", bundle_hash)
        if witness_hash is not None:
            payload_without_hash["witness_hash"] = _require_sha256_prefixed("witness_hash", witness_hash)
        return cls(
            object_hash=object_hash,
            instance_hash=instance_hash,
            cert_sha256=cert_sha256,
            delta_hash=delta_hash,
            holder_delta=holder_delta,
            writer_delta=writer_delta,
            command_tag=command_tag,
            object_name=object_name,
            object_version=object_version,
            bundle_hash=bundle_hash,
            witness_hash=witness_hash,
            receipt_hash=_sha256_bytes(_canonical_json_bytes(payload_without_hash)),
        )

    @classmethod
    def from_dict(cls, payload: object) -> "FireVerifierReceipt":
        if not isinstance(payload, Mapping):
            raise TypeError("verifier receipt payload must be a mapping")
        return cls(
            schema=payload.get("schema", FIRE_VERIFIER_RECEIPT_SCHEMA),
            object_hash=payload.get("object_hash"),
            instance_hash=payload.get("instance_hash"),
            cert_sha256=payload.get("cert_sha256"),
            delta_hash=payload.get("delta_hash"),
            holder_delta=payload.get("holder_delta"),
            writer_delta=payload.get("writer_delta"),
            command_tag=payload.get("command_tag"),
            object_name=payload.get("object_name"),
            object_version=payload.get("object_version"),
            bundle_hash=payload.get("bundle_hash"),
            witness_hash=payload.get("witness_hash"),
            receipt_hash=payload.get("receipt_hash"),
        )


def verify_fire_verifier_receipt(
    receipt: FireVerifierReceipt,
    *,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_holder_delta: int | None = None,
    expected_writer_delta: int | None = None,
    expected_command_tag: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
    require_witness_hash: bool = False,
) -> tuple[bool, str | None]:
    if not isinstance(receipt, FireVerifierReceipt):
        raise TypeError("receipt must be a FireVerifierReceipt")
    if require_witness_hash and receipt.witness_hash is None:
        return False, "witness_hash_missing"
    if expected_object_hash is not None and receipt.object_hash != expected_object_hash:
        return False, "object_hash_mismatch"
    if expected_instance_hash is not None and receipt.instance_hash != expected_instance_hash:
        return False, "instance_hash_mismatch"
    if expected_cert_sha256 is not None and receipt.cert_sha256 != expected_cert_sha256:
        return False, "cert_sha256_mismatch"
    if expected_holder_delta is not None and receipt.holder_delta != expected_holder_delta:
        return False, "holder_delta_mismatch"
    if expected_writer_delta is not None and receipt.writer_delta != expected_writer_delta:
        return False, "writer_delta_mismatch"
    if expected_command_tag is not None and receipt.command_tag != expected_command_tag:
        return False, "command_tag_mismatch"
    if expected_bundle_hash is not None and receipt.bundle_hash != expected_bundle_hash:
        return False, "bundle_hash_mismatch"
    if expected_witness_hash is not None and receipt.witness_hash != expected_witness_hash:
        return False, "witness_hash_mismatch"
    expected_delta_hash = fire_settlement_delta_hash(
        holder_delta=receipt.holder_delta,
        writer_delta=receipt.writer_delta,
    )
    if receipt.delta_hash != expected_delta_hash:
        return False, "delta_hash_mismatch"
    if not fire_settlement_deltas_conserve(
        holder_delta=receipt.holder_delta,
        writer_delta=receipt.writer_delta,
    ):
        return False, "delta_nonzero_sum"
    expected_receipt_hash = _sha256_bytes(_canonical_json_bytes(receipt.payload_without_hash()))
    if receipt.receipt_hash != expected_receipt_hash:
        return False, "receipt_hash_mismatch"
    return True, None


def verify_fire_settlement_authority_receipt(
    receipt: FireVerifierReceipt,
    *,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_holder_delta: int | None = None,
    expected_writer_delta: int | None = None,
    expected_command_tag: str = FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
) -> tuple[bool, str | None]:
    witness_error = _authority_expected_witness_hash_error(expected_witness_hash)
    if witness_error is not None:
        return False, witness_error
    return verify_fire_verifier_receipt(
        receipt,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_holder_delta=expected_holder_delta,
        expected_writer_delta=expected_writer_delta,
        expected_command_tag=expected_command_tag,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        require_witness_hash=True,
    )


@dataclass(frozen=True)
class FireSettlementPacket:
    receipt: FireVerifierReceipt
    holder_delta: int
    writer_delta: int
    payoff_out: int
    firev_accept: bool
    packet_hash: str
    schema: str = FIRE_SETTLEMENT_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.receipt, FireVerifierReceipt):
            raise TypeError("receipt must be a FireVerifierReceipt")
        object.__setattr__(self, "holder_delta", _require_int("holder_delta", self.holder_delta))
        object.__setattr__(self, "writer_delta", _require_int("writer_delta", self.writer_delta))
        object.__setattr__(self, "payoff_out", _require_int("payoff_out", self.payoff_out))
        object.__setattr__(self, "firev_accept", _require_bool("firev_accept", self.firev_accept))
        object.__setattr__(self, "packet_hash", _require_sha256_prefixed("packet_hash", self.packet_hash))
        if self.schema != FIRE_SETTLEMENT_PACKET_SCHEMA:
            raise ValueError(f"unsupported settlement packet schema: {self.schema}")

    def payload_without_hash(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "receipt": self.receipt.to_dict(),
            "holder_delta": self.holder_delta,
            "writer_delta": self.writer_delta,
            "payoff_out": self.payoff_out,
            "firev_accept": self.firev_accept,
        }

    def to_dict(self) -> dict[str, object]:
        payload = self.payload_without_hash()
        payload["packet_hash"] = self.packet_hash
        return payload

    @classmethod
    def build(
        cls,
        *,
        receipt: FireVerifierReceipt,
        holder_delta: int,
        writer_delta: int,
        payoff_out: int,
        firev_accept: bool,
    ) -> "FireSettlementPacket":
        holder_delta_i = _require_int("holder_delta", holder_delta)
        writer_delta_i = _require_int("writer_delta", writer_delta)
        if not fire_settlement_deltas_conserve(holder_delta=holder_delta_i, writer_delta=writer_delta_i):
            raise ValueError("delta_nonzero_sum")
        payload_without_hash: dict[str, object] = {
            "schema": FIRE_SETTLEMENT_PACKET_SCHEMA,
            "receipt": receipt.to_dict(),
            "holder_delta": holder_delta_i,
            "writer_delta": writer_delta_i,
            "payoff_out": _require_int("payoff_out", payoff_out),
            "firev_accept": _require_bool("firev_accept", firev_accept),
        }
        return cls(
            receipt=receipt,
            holder_delta=holder_delta,
            writer_delta=writer_delta,
            payoff_out=payoff_out,
            firev_accept=firev_accept,
            packet_hash=_sha256_bytes(_canonical_json_bytes(payload_without_hash)),
        )

    @classmethod
    def from_dict(cls, payload: object) -> "FireSettlementPacket":
        if not isinstance(payload, Mapping):
            raise TypeError("settlement packet payload must be a mapping")
        return cls(
            schema=payload.get("schema", FIRE_SETTLEMENT_PACKET_SCHEMA),
            receipt=FireVerifierReceipt.from_dict(payload.get("receipt")),
            holder_delta=payload.get("holder_delta"),
            writer_delta=payload.get("writer_delta"),
            payoff_out=payload.get("payoff_out"),
            firev_accept=payload.get("firev_accept"),
            packet_hash=payload.get("packet_hash"),
        )


def verify_fire_settlement_packet(
    packet: FireSettlementPacket,
    *,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
    expected_command_tag: str | None = None,
    require_witness_hash: bool = False,
) -> tuple[bool, str | None]:
    if not isinstance(packet, FireSettlementPacket):
        raise TypeError("packet must be a FireSettlementPacket")
    if not packet.firev_accept:
        return False, "firev_accept_false"
    if packet.payoff_out != packet.holder_delta:
        return False, "payoff_out_mismatch"
    if not fire_settlement_deltas_conserve(
        holder_delta=packet.holder_delta,
        writer_delta=packet.writer_delta,
    ):
        return False, "delta_nonzero_sum"
    ok, err = verify_fire_verifier_receipt(
        packet.receipt,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_holder_delta=packet.holder_delta,
        expected_writer_delta=packet.writer_delta,
        expected_command_tag=expected_command_tag,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        require_witness_hash=require_witness_hash,
    )
    if not ok:
        return False, f"receipt_{err or 'invalid'}"
    expected_packet_hash = _sha256_bytes(_canonical_json_bytes(packet.payload_without_hash()))
    if packet.packet_hash != expected_packet_hash:
        return False, "packet_hash_mismatch"
    return True, None


def verify_fire_settlement_authority_packet(
    packet: FireSettlementPacket,
    *,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
    expected_command_tag: str = FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
) -> tuple[bool, str | None]:
    witness_error = _authority_expected_witness_hash_error(expected_witness_hash)
    if witness_error is not None:
        return False, witness_error
    return verify_fire_settlement_packet(
        packet,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        expected_command_tag=expected_command_tag,
        require_witness_hash=True,
    )


def extract_verified_fire_settlement_packet(
    effects: Mapping[str, Any],
    *,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
    expected_command_tag: str | None = "firev_accept_and_settle",
    require_witness_hash: bool = False,
) -> tuple[bool, str | None, FireSettlementPacket | None]:
    if not isinstance(effects, Mapping):
        raise TypeError("effects must be a mapping")
    packet_payload = effects.get("settlement_packet")
    if not isinstance(packet_payload, Mapping):
        return False, "settlement_packet_missing", None
    try:
        packet = FireSettlementPacket.from_dict(packet_payload)
    except (TypeError, ValueError, KeyError) as exc:
        return False, f"settlement_packet_invalid:{exc}", None
    if "verifier_receipt" in effects and effects.get("verifier_receipt") != packet.receipt.to_dict():
        return False, "verifier_receipt_mismatch", None
    if "firev_accept" in effects and effects.get("firev_accept") != packet.firev_accept:
        return False, "firev_accept_mismatch", None
    if "payoff_out" in effects and effects.get("payoff_out") != packet.payoff_out:
        return False, "payoff_out_mismatch", None
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
        return False, err or "settlement_packet_invalid", None
    return True, None, packet


def extract_verified_fire_settlement_authority_packet(
    effects: Mapping[str, Any],
    *,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
    expected_command_tag: str = FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
) -> tuple[bool, str | None, FireSettlementPacket | None]:
    witness_error = _authority_expected_witness_hash_error(expected_witness_hash)
    if witness_error is not None:
        return False, witness_error, None
    return extract_verified_fire_settlement_packet(
        effects,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        expected_command_tag=expected_command_tag,
        require_witness_hash=True,
    )


__all__ = [
    "FIRE_SETTLEMENT_DELTA_SCHEMA",
    "FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG",
    "FIRE_SETTLEMENT_PACKET_SCHEMA",
    "FIRE_VERIFIER_RECEIPT_SCHEMA",
    "FIRE_WITNESS_BINDING_SCHEMA",
    "FireSettlementPacket",
    "FireVerifierReceipt",
    "extract_verified_fire_settlement_authority_packet",
    "extract_verified_fire_settlement_packet",
    "fire_settlement_deltas_conserve",
    "fire_settlement_delta_hash",
    "fire_witness_binding_hash",
    "verify_fire_settlement_authority_packet",
    "verify_fire_settlement_authority_receipt",
    "verify_fire_settlement_packet",
    "verify_fire_verifier_receipt",
]
