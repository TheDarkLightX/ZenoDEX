from __future__ import annotations

from src.fire.kernel.apply_receipt_v1 import FireApplyReceipt, verify_fire_apply_receipt
from src.fire.verifier.settlement_v1 import FireSettlementPacket, FireVerifierReceipt, fire_witness_binding_hash


def test_fire_apply_receipt_round_trip_and_balance_transition() -> None:
    witness_hash = fire_witness_binding_hash({"witness_final": 7})
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
        bundle_hash="sha256:" + "4" * 64,
        witness_hash=witness_hash,
    )
    packet = FireSettlementPacket.build(
        receipt=receipt,
        holder_delta=30,
        writer_delta=-30,
        payoff_out=30,
        firev_accept=True,
    )
    apply_receipt = FireApplyReceipt.build(
        packet_hash=packet.packet_hash,
        holder_balance_before=100,
        writer_balance_before=250,
        holder_balance_after=130,
        writer_balance_after=220,
    )
    parsed = FireApplyReceipt.from_dict(apply_receipt.to_dict())
    assert verify_fire_apply_receipt(
        parsed,
        packet=packet,
        expected_bundle_hash=receipt.bundle_hash,
        expected_witness_hash=witness_hash,
        expected_command_tag="firev_accept_and_settle",
    ) == (True, None)


def test_fire_apply_receipt_rejects_tampered_balance_transition() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
        bundle_hash="sha256:" + "4" * 64,
    )
    packet = FireSettlementPacket.build(
        receipt=receipt,
        holder_delta=30,
        writer_delta=-30,
        payoff_out=30,
        firev_accept=True,
    )
    apply_receipt = FireApplyReceipt.build(
        packet_hash=packet.packet_hash,
        holder_balance_before=100,
        writer_balance_before=250,
        holder_balance_after=130,
        writer_balance_after=220,
    )
    tampered = FireApplyReceipt.from_dict(
        {
            **apply_receipt.to_dict(),
            "holder_balance_after": 131,
        }
    )
    assert verify_fire_apply_receipt(tampered, packet=packet) == (False, "holder_balance_transition_mismatch")


def test_fire_apply_receipt_can_require_packet_receipt_witness_hash() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
        bundle_hash="sha256:" + "4" * 64,
    )
    packet = FireSettlementPacket.build(
        receipt=receipt,
        holder_delta=30,
        writer_delta=-30,
        payoff_out=30,
        firev_accept=True,
    )
    apply_receipt = FireApplyReceipt.build(
        packet_hash=packet.packet_hash,
        holder_balance_before=100,
        writer_balance_before=250,
        holder_balance_after=130,
        writer_balance_after=220,
    )
    assert verify_fire_apply_receipt(apply_receipt, packet=packet) == (True, None)
    assert verify_fire_apply_receipt(apply_receipt, packet=packet, require_witness_hash=True) == (
        False,
        "packet_receipt_witness_hash_missing",
    )
