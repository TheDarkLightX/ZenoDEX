from __future__ import annotations

from src.fire.kernel.apply_receipt_v1 import FireApplyReceipt, verify_fire_apply_receipt
from src.fire.verifier.settlement_apply_report_v1 import (
    build_fire_settlement_apply_report,
    verify_fire_settlement_apply_report,
)
from src.fire.verifier.settlement_v1 import (
    FireSettlementPacket,
    FireVerifierReceipt,
    extract_verified_fire_settlement_packet,
    fire_settlement_delta_hash,
    fire_witness_binding_hash,
    verify_fire_settlement_packet,
    verify_fire_verifier_receipt,
)


def _build_receipt_and_packet() -> tuple[FireVerifierReceipt, FireSettlementPacket]:
    witness_hash = fire_witness_binding_hash({"witness_final": 7})
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=7,
        writer_delta=-7,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="v1",
        bundle_hash="sha256:" + "4" * 64,
        witness_hash=witness_hash,
    )
    packet = FireSettlementPacket.build(
        receipt=receipt,
        holder_delta=7,
        writer_delta=-7,
        payoff_out=7,
        firev_accept=True,
    )
    return receipt, packet


def test_src_fire_settlement_receipt_and_packet_roundtrip() -> None:
    receipt, packet = _build_receipt_and_packet()

    assert receipt.delta_hash == fire_settlement_delta_hash(holder_delta=7, writer_delta=-7)
    assert verify_fire_verifier_receipt(receipt) == (True, None)
    assert verify_fire_settlement_packet(packet) == (True, None)


def test_src_fire_extract_verified_settlement_packet_rejects_receipt_mismatch() -> None:
    receipt, packet = _build_receipt_and_packet()
    mismatched_receipt = FireVerifierReceipt.build(
        object_hash=receipt.object_hash,
        instance_hash=receipt.instance_hash,
        cert_sha256=receipt.cert_sha256,
        holder_delta=8,
        writer_delta=-8,
        command_tag=receipt.command_tag,
        object_name=receipt.object_name,
        object_version=receipt.object_version,
        bundle_hash=receipt.bundle_hash,
        witness_hash=receipt.witness_hash,
    )

    ok, err, parsed = extract_verified_fire_settlement_packet(
        {
            "settlement_packet": packet.to_dict(),
            "verifier_receipt": mismatched_receipt.to_dict(),
        }
    )

    assert ok is False
    assert err == "verifier_receipt_mismatch"
    assert parsed is None


def test_src_fire_apply_receipt_and_report_verify_without_bundle_dir() -> None:
    receipt, packet = _build_receipt_and_packet()
    apply_receipt = FireApplyReceipt.build(
        packet_hash=packet.packet_hash,
        holder_balance_before=100,
        writer_balance_before=250,
        holder_balance_after=107,
        writer_balance_after=243,
    )
    assert verify_fire_apply_receipt(apply_receipt, packet=packet) == (True, None)

    report = build_fire_settlement_apply_report(
        {
            "schema": "zenodex/fire-settlement-apply-report/v1",
            "ok": True,
            "object_name": receipt.object_name,
            "object_version": receipt.object_version,
            "object_family": "capped_index_call",
            "bundle_dir": "/tmp/example",
            "bundle_file_sha256": "sha256:" + "5" * 64,
            "bundle_hash": receipt.bundle_hash,
            "object_hash": receipt.object_hash,
            "instance_hash": receipt.instance_hash,
            "cert_sha256": receipt.cert_sha256,
            "witness_hash": receipt.witness_hash,
            "holder_delta": packet.holder_delta,
            "writer_delta": packet.writer_delta,
            "payoff_out": packet.payoff_out,
            "holder_balance_before": apply_receipt.holder_balance_before,
            "writer_balance_before": apply_receipt.writer_balance_before,
            "holder_balance_after": apply_receipt.holder_balance_after,
            "writer_balance_after": apply_receipt.writer_balance_after,
            "verifier_receipt": receipt.to_dict(),
            "settlement_packet": packet.to_dict(),
            "apply_receipt": apply_receipt.to_dict(),
        }
    )

    assert verify_fire_settlement_apply_report(
        report,
        expected_witness_hash=receipt.witness_hash,
    ) == (True, None)
