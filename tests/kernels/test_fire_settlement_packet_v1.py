from __future__ import annotations

from dataclasses import replace

import pytest

from src.fire.verifier.settlement_v1 import (
    FireSettlementPacket,
    FireVerifierReceipt,
    extract_verified_fire_settlement_authority_packet,
    fire_witness_binding_hash,
    verify_fire_settlement_authority_packet,
    verify_fire_settlement_packet,
    verify_fire_settlement_authority_receipt,
)


def test_fire_settlement_packet_round_trip_and_receipt_binding() -> None:
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
    round_trip = FireSettlementPacket.from_dict(packet.to_dict())
    assert verify_fire_settlement_packet(
        round_trip,
        expected_object_hash=receipt.object_hash,
        expected_instance_hash=receipt.instance_hash,
        expected_cert_sha256=receipt.cert_sha256,
        expected_bundle_hash=receipt.bundle_hash,
        expected_witness_hash=witness_hash,
        expected_command_tag="firev_accept_and_settle",
    ) == (True, None)


def test_fire_settlement_packet_rejects_delta_tamper() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
    )
    packet = FireSettlementPacket.build(
        receipt=receipt,
        holder_delta=30,
        writer_delta=-30,
        payoff_out=30,
        firev_accept=True,
    )
    tampered = replace(packet, payoff_out=29)
    assert verify_fire_settlement_packet(tampered) == (False, "payoff_out_mismatch")


def test_fire_settlement_packet_builder_rejects_nonconserving_deltas() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
    )

    with pytest.raises(ValueError, match="delta_nonzero_sum"):
        FireSettlementPacket.build(
            receipt=receipt,
            holder_delta=30,
            writer_delta=-29,
            payoff_out=30,
            firev_accept=True,
        )


def test_fire_settlement_packet_can_require_receipt_witness_hash() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
    )
    packet = FireSettlementPacket.build(
        receipt=receipt,
        holder_delta=30,
        writer_delta=-30,
        payoff_out=30,
        firev_accept=True,
    )
    assert verify_fire_settlement_packet(packet) == (True, None)
    assert verify_fire_settlement_packet(packet, require_witness_hash=True) == (
        False,
        "receipt_witness_hash_missing",
    )


def test_fire_settlement_authority_packet_requires_witness_hash_and_command_tag() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
    )
    packet = FireSettlementPacket.build(
        receipt=receipt,
        holder_delta=30,
        writer_delta=-30,
        payoff_out=30,
        firev_accept=True,
    )

    assert verify_fire_settlement_packet(packet) == (True, None)
    assert verify_fire_settlement_authority_receipt(receipt) == (False, "expected_witness_hash_missing")
    assert verify_fire_settlement_authority_packet(packet) == (False, "expected_witness_hash_missing")

    witness_hash = fire_witness_binding_hash({"witness_final": 30})
    bound_receipt = FireVerifierReceipt.build(
        object_hash=receipt.object_hash,
        instance_hash=receipt.instance_hash,
        cert_sha256=receipt.cert_sha256,
        holder_delta=30,
        writer_delta=-30,
        command_tag="advisory_only",
        object_name=receipt.object_name,
        object_version=receipt.object_version,
        witness_hash=witness_hash,
    )
    bound_packet = FireSettlementPacket.build(
        receipt=bound_receipt,
        holder_delta=30,
        writer_delta=-30,
        payoff_out=30,
        firev_accept=True,
    )
    assert verify_fire_settlement_packet(bound_packet, require_witness_hash=True) == (True, None)
    assert verify_fire_settlement_authority_packet(bound_packet) == (False, "expected_witness_hash_missing")
    assert verify_fire_settlement_authority_packet(
        bound_packet, expected_witness_hash=witness_hash
    ) == (False, "receipt_command_tag_mismatch")


def test_fire_settlement_authority_packet_rejects_self_bound_forgery_without_expected_witness() -> None:
    forged_witness_hash = fire_witness_binding_hash({"witness_final": 777000})
    forged_receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=777000,
        writer_delta=-777000,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
        bundle_hash="sha256:" + "4" * 64,
        witness_hash=forged_witness_hash,
    )
    forged_packet = FireSettlementPacket.build(
        receipt=forged_receipt,
        holder_delta=777000,
        writer_delta=-777000,
        payoff_out=777000,
        firev_accept=True,
    )

    assert verify_fire_settlement_packet(forged_packet, require_witness_hash=True) == (True, None)
    assert verify_fire_settlement_authority_packet(forged_packet) == (False, "expected_witness_hash_missing")
    assert verify_fire_settlement_authority_packet(
        forged_packet,
        expected_witness_hash=fire_witness_binding_hash({"witness_final": 30}),
    ) == (False, "receipt_witness_hash_mismatch")

def test_extract_verified_fire_settlement_authority_packet_uses_authority_gate() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
    )
    packet = FireSettlementPacket.build(
        receipt=receipt,
        holder_delta=30,
        writer_delta=-30,
        payoff_out=30,
        firev_accept=True,
    )

    ok, err, parsed = extract_verified_fire_settlement_authority_packet(
        {
            "settlement_packet": packet.to_dict(),
            "verifier_receipt": receipt.to_dict(),
        }
    )

    assert ok is False
    assert err == "expected_witness_hash_missing"
    assert parsed is None
