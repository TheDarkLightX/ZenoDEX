from __future__ import annotations

from pathlib import Path

from src.fire.kernel.apply_receipt_v1 import FireApplyReceipt
from src.fire.compiler.compiler_registry_v1 import compile_fire_object
from src.fire.compiler.fmos_v1 import build_fmos_manifest, render_fmos_object_card
from src.fire.registry.bundle_v1 import load_fire_registry_bundle, write_fire_registry_bundle
from src.fire.verifier.settlement_apply_report_v1 import (
    FIRE_SETTLEMENT_APPLY_REPORT_SCHEMA,
    build_fire_settlement_apply_report,
    fire_settlement_apply_report_hash,
    settlement_apply_report_payload_without_hash,
    verify_fire_settlement_apply_report,
)
from src.fire.verifier.settlement_v1 import FireSettlementPacket, FireVerifierReceipt, fire_witness_binding_hash


def _report_payload(*, include_witness_hash: bool = True) -> dict[str, object]:
    witness_hash = fire_witness_binding_hash({"witness_final": 30})
    receipt_kwargs: dict[str, object] = {}
    if include_witness_hash:
        receipt_kwargs["witness_hash"] = witness_hash
    verifier_receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
        bundle_hash="sha256:" + "4" * 64,
        **receipt_kwargs,
    )
    packet = FireSettlementPacket.build(
        receipt=verifier_receipt,
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
    report_without_hash: dict[str, object] = {
        "schema": FIRE_SETTLEMENT_APPLY_REPORT_SCHEMA,
        "ok": True,
        "object_id": "burn_boost_call_v1",
        "object_name": verifier_receipt.object_name,
        "object_version": verifier_receipt.object_version,
        "object_family": "capped_index_call",
        "bundle_dir": "/tmp/bundle",
        "bundle_hash": verifier_receipt.bundle_hash,
        "bundle_file_sha256": "sha256:" + "5" * 64,
        "object_hash": verifier_receipt.object_hash,
        "instance_hash": verifier_receipt.instance_hash,
        "cert_sha256": verifier_receipt.cert_sha256,
        "holder_balance_before": 100,
        "writer_balance_before": 250,
        "holder_balance_after": 130,
        "writer_balance_after": 220,
        "holder_delta": 30,
        "writer_delta": -30,
        "payoff_out": 30,
        "verifier_receipt": verifier_receipt.to_dict(),
        "settlement_packet": packet.to_dict(),
        "apply_receipt": apply_receipt.to_dict(),
    }
    if include_witness_hash:
        report_without_hash["witness_hash"] = witness_hash
    return build_fire_settlement_apply_report(report_without_hash)


def test_verify_fire_settlement_apply_report_accepts_valid_payload() -> None:
    payload = _report_payload()
    assert verify_fire_settlement_apply_report(payload) == (True, None)
    assert verify_fire_settlement_apply_report(payload, expected_witness_hash=payload["witness_hash"]) == (True, None)


def test_verify_fire_settlement_apply_report_rejects_top_level_mismatch() -> None:
    payload = _report_payload()
    payload["holder_balance_after"] = 131
    payload = build_fire_settlement_apply_report(settlement_apply_report_payload_without_hash(payload))
    assert verify_fire_settlement_apply_report(payload) == (False, "holder_balance_after_mismatch")


def test_verify_fire_settlement_apply_report_rejects_top_level_witness_hash_mismatch() -> None:
    payload = _report_payload()
    payload["witness_hash"] = fire_witness_binding_hash({"witness_final": 31})
    payload = build_fire_settlement_apply_report(settlement_apply_report_payload_without_hash(payload))
    assert verify_fire_settlement_apply_report(payload) == (False, "witness_hash_mismatch")


def test_verify_fire_settlement_apply_report_rejects_missing_top_level_witness_hash() -> None:
    payload = _report_payload()
    payload.pop("witness_hash")
    payload = build_fire_settlement_apply_report(settlement_apply_report_payload_without_hash(payload))
    assert verify_fire_settlement_apply_report(payload) == (False, "witness_hash_mismatch")


def test_verify_fire_settlement_apply_report_rejects_missing_receipt_witness_hash() -> None:
    payload = _report_payload(include_witness_hash=False)
    assert verify_fire_settlement_apply_report(payload) == (False, "settlement_packet_receipt_witness_hash_missing")


def test_verify_fire_settlement_apply_report_rejects_top_level_verifier_receipt_drift() -> None:
    payload = _report_payload()
    receipt_payload = dict(payload["verifier_receipt"])
    receipt_payload["witness_hash"] = fire_witness_binding_hash({"witness_final": 31})
    payload["verifier_receipt"] = receipt_payload
    payload = build_fire_settlement_apply_report(settlement_apply_report_payload_without_hash(payload))
    assert verify_fire_settlement_apply_report(payload) == (False, "verifier_receipt_mismatch")


def test_verify_fire_settlement_apply_report_rejects_expected_witness_hash_mismatch() -> None:
    payload = _report_payload()
    expected_witness_hash = fire_witness_binding_hash({"witness_final": 31})
    assert verify_fire_settlement_apply_report(
        payload,
        expected_witness_hash=expected_witness_hash,
    ) == (False, "settlement_packet_receipt_witness_hash_mismatch")


def test_verify_fire_settlement_apply_report_rejects_report_hash_tamper() -> None:
    payload = _report_payload()
    payload["report_hash"] = "sha256:" + "9" * 64
    assert verify_fire_settlement_apply_report(payload) == (False, "report_hash_mismatch")


def test_verify_fire_settlement_apply_report_rejects_non_string_mapping_key() -> None:
    payload = _report_payload()
    payload[123] = "unexpected"
    payload["report_hash"] = fire_settlement_apply_report_hash(
        {str(key): value for key, value in payload.items() if key != "report_hash"}
    )

    ok, err = verify_fire_settlement_apply_report(payload)

    assert ok is False
    assert err is not None
    assert err.startswith("report_key_invalid:")


def test_verify_fire_settlement_apply_report_matches_expected_bundle_dir(tmp_path: Path) -> None:
    compiled = compile_fire_object(
        "burn_boost_call_v1",
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
    )
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=compiled.artifact,
        build_manifest=lambda artifact: build_fmos_manifest(compiled.spec, artifact),
        render_object_card=lambda artifact: render_fmos_object_card(compiled.spec, artifact),
    )
    _bundle_manifest, _bundle_file_sha256, object_manifest, object_instance, _object_lock = load_fire_registry_bundle(bundle_dir)
    witness_hash = fire_witness_binding_hash({"witness_final": 30})
    verifier_receipt = FireVerifierReceipt.build(
        object_hash=object_manifest.manifest_hash,
        instance_hash=object_instance.instance_hash,
        cert_sha256=object_manifest.cert_sha256,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name=object_manifest.object_name,
        object_version=object_manifest.object_version,
        bundle_hash=bundle_manifest.bundle_hash,
        witness_hash=witness_hash,
    )
    settlement_packet = FireSettlementPacket.build(
        receipt=verifier_receipt,
        holder_delta=30,
        writer_delta=-30,
        payoff_out=30,
        firev_accept=True,
    )
    apply_receipt = FireApplyReceipt.build(
        packet_hash=settlement_packet.packet_hash,
        holder_balance_before=100,
        writer_balance_before=250,
        holder_balance_after=130,
        writer_balance_after=220,
    )
    payload = build_fire_settlement_apply_report({
        "schema": FIRE_SETTLEMENT_APPLY_REPORT_SCHEMA,
        "ok": True,
        "object_id": "burn_boost_call_v1",
        "object_name": object_manifest.object_name,
        "object_version": object_manifest.object_version,
        "object_family": object_manifest.object_family,
        "bundle_dir": str(bundle_dir.resolve()),
        "bundle_hash": bundle_manifest.bundle_hash,
        "bundle_file_sha256": bundle_file_sha256,
        "object_hash": object_manifest.manifest_hash,
        "instance_hash": object_instance.instance_hash,
        "cert_sha256": object_manifest.cert_sha256,
        "witness_hash": witness_hash,
        "holder_balance_before": 100,
        "writer_balance_before": 250,
        "holder_balance_after": 130,
        "writer_balance_after": 220,
        "holder_delta": 30,
        "writer_delta": -30,
        "payoff_out": 30,
        "verifier_receipt": verifier_receipt.to_dict(),
        "settlement_packet": settlement_packet.to_dict(),
        "apply_receipt": apply_receipt.to_dict(),
    })
    assert verify_fire_settlement_apply_report(payload, expected_bundle_dir=bundle_dir) == (True, None)
