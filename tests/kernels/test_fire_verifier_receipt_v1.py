from __future__ import annotations

from src.fire.verifier.settlement_v1 import (
    FireVerifierReceipt,
    fire_settlement_delta_hash,
    fire_witness_binding_hash,
    verify_fire_verifier_receipt,
)


def test_fire_verifier_receipt_round_trip_and_sound_hashes() -> None:
    witness_hash = fire_witness_binding_hash({"witness_final": 7})
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + ("11" * 32),
        instance_hash="sha256:" + ("22" * 32),
        cert_sha256="sha256:" + ("33" * 32),
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="v1",
        bundle_hash="sha256:" + ("44" * 32),
        witness_hash=witness_hash,
    )

    restored = FireVerifierReceipt.from_dict(receipt.to_dict())

    assert restored == receipt
    assert receipt.delta_hash == fire_settlement_delta_hash(holder_delta=30, writer_delta=-30)
    assert receipt.witness_hash == witness_hash
    assert verify_fire_verifier_receipt(
        receipt,
        expected_object_hash="sha256:" + ("11" * 32),
        expected_instance_hash="sha256:" + ("22" * 32),
        expected_cert_sha256="sha256:" + ("33" * 32),
        expected_holder_delta=30,
        expected_writer_delta=-30,
        expected_command_tag="firev_accept_and_settle",
        expected_bundle_hash="sha256:" + ("44" * 32),
        expected_witness_hash=witness_hash,
    ) == (True, None)


def test_fire_verifier_receipt_rejects_delta_tamper() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + ("11" * 32),
        instance_hash="sha256:" + ("22" * 32),
        cert_sha256="sha256:" + ("33" * 32),
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="v1",
    )
    tampered = FireVerifierReceipt.from_dict({**receipt.to_dict(), "holder_delta": 29})

    assert verify_fire_verifier_receipt(tampered) == (False, "delta_hash_mismatch")


def test_fire_verifier_receipt_rejects_balanced_hash_with_nonconserving_deltas() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + ("11" * 32),
        instance_hash="sha256:" + ("22" * 32),
        cert_sha256="sha256:" + ("33" * 32),
        holder_delta=30,
        writer_delta=-29,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="v1",
    )

    assert verify_fire_verifier_receipt(receipt) == (False, "delta_nonzero_sum")


def test_fire_verifier_receipt_rejects_witness_binding_mismatch() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + ("11" * 32),
        instance_hash="sha256:" + ("22" * 32),
        cert_sha256="sha256:" + ("33" * 32),
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="v1",
        witness_hash=fire_witness_binding_hash({"witness_final": 7}),
    )

    assert verify_fire_verifier_receipt(
        receipt,
        expected_witness_hash=fire_witness_binding_hash({"witness_final": 8}),
    ) == (False, "witness_hash_mismatch")


def test_fire_verifier_receipt_can_require_witness_hash() -> None:
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + ("11" * 32),
        instance_hash="sha256:" + ("22" * 32),
        cert_sha256="sha256:" + ("33" * 32),
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="v1",
    )

    assert verify_fire_verifier_receipt(receipt) == (True, None)
    assert verify_fire_verifier_receipt(receipt, require_witness_hash=True) == (False, "witness_hash_missing")
