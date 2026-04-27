from __future__ import annotations

from src.fire.verifier.settlement_v1 import (
    FireSettlementPacket,
    FireVerifierReceipt,
    extract_verified_fire_settlement_packet,
)


def _packet_dict() -> dict[str, object]:
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
    return {
        "firev_accept": True,
        "payoff_out": 30,
        "verifier_receipt": receipt.to_dict(),
        "settlement_packet": packet.to_dict(),
    }


def test_extract_verified_fire_settlement_packet_accepts_bound_effects() -> None:
    effects = _packet_dict()
    ok, err, packet = extract_verified_fire_settlement_packet(
        effects,
        expected_bundle_hash="sha256:" + "4" * 64,
    )
    assert ok is True
    assert err is None
    assert packet is not None
    assert packet.holder_delta == 30


def test_extract_verified_fire_settlement_packet_rejects_receipt_mismatch() -> None:
    effects = _packet_dict()
    effects["verifier_receipt"] = dict(effects["verifier_receipt"])
    effects["verifier_receipt"]["holder_delta"] = 29
    ok, err, packet = extract_verified_fire_settlement_packet(effects)
    assert ok is False
    assert err == "verifier_receipt_mismatch"
    assert packet is None
