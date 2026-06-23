from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from src.fire.kernel.apply_receipt_v1 import FireApplyReceipt, verify_fire_authority_apply_receipt
from src.fire.verifier.settlement_v1 import (
    FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
    FireSettlementPacket,
    extract_verified_fire_settlement_authority_packet,
    verify_fire_settlement_authority_packet,
)


def _require_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


@dataclass(frozen=True)
class FireLedgerBalances:
    holder_balance: int
    writer_balance: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "holder_balance", _require_int("holder_balance", self.holder_balance))
        object.__setattr__(self, "writer_balance", _require_int("writer_balance", self.writer_balance))


@dataclass(frozen=True)
class FireLedgerApplyResult:
    balances: FireLedgerBalances
    packet: FireSettlementPacket
    apply_receipt: FireApplyReceipt


def apply_verified_fire_settlement_packet(
    packet: FireSettlementPacket,
    *,
    balances: FireLedgerBalances,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
    expected_command_tag: str = FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
) -> tuple[bool, str | None, FireLedgerApplyResult | None]:
    if not isinstance(packet, FireSettlementPacket):
        raise TypeError("packet must be a FireSettlementPacket")
    if not isinstance(balances, FireLedgerBalances):
        raise TypeError("balances must be a FireLedgerBalances")
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
        return False, err or "settlement_packet_invalid", None
    next_balances = FireLedgerBalances(
        holder_balance=balances.holder_balance + packet.holder_delta,
        writer_balance=balances.writer_balance + packet.writer_delta,
    )
    apply_receipt = FireApplyReceipt.build(
        packet_hash=packet.packet_hash,
        holder_balance_before=balances.holder_balance,
        writer_balance_before=balances.writer_balance,
        holder_balance_after=next_balances.holder_balance,
        writer_balance_after=next_balances.writer_balance,
    )
    ok, err = verify_fire_authority_apply_receipt(
        apply_receipt,
        packet=packet,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        expected_command_tag=expected_command_tag,
    )
    if not ok:
        return False, err or "apply_receipt_invalid", None
    return True, None, FireLedgerApplyResult(
        balances=next_balances,
        packet=packet,
        apply_receipt=apply_receipt,
    )


def apply_verified_fire_settlement_effects(
    effects: Mapping[str, Any],
    *,
    balances: FireLedgerBalances,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
    expected_command_tag: str = FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
) -> tuple[bool, str | None, FireLedgerApplyResult | None]:
    ok, err, packet = extract_verified_fire_settlement_authority_packet(
        effects,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        expected_command_tag=expected_command_tag,
    )
    if not ok or packet is None:
        return False, err or "settlement_packet_invalid", None
    return apply_verified_fire_settlement_packet(
        packet,
        balances=balances,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        expected_command_tag=expected_command_tag,
    )


__all__ = [
    "FireLedgerApplyResult",
    "FireLedgerBalances",
    "apply_verified_fire_settlement_effects",
    "apply_verified_fire_settlement_packet",
]
