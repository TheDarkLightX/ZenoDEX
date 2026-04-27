from __future__ import annotations

import hashlib
import json
from pathlib import Path

from src.fire.compiler.compiler_registry_v1 import compile_fire_object
from src.fire.compiler.fmos_v1 import build_fmos_manifest, render_fmos_object_card
from src.fire.registry.bundle_v1 import load_fire_registry_bundle, write_fire_registry_bundle
from src.fire.verifier.settlement_apply_artifact_v1 import (
    build_fire_settlement_apply_artifact_receipt,
    check_fire_settlement_apply_artifact_receipt,
    write_fire_settlement_apply_artifact_receipt,
)
from src.fire.verifier.settlement_apply_report_v1 import build_fire_settlement_apply_report
from src.fire.verifier.settlement_v1 import FireSettlementPacket, FireVerifierReceipt, fire_witness_binding_hash
from src.fire.kernel.apply_receipt_v1 import FireApplyReceipt


def _receipt_hash(payload: dict[str, object]) -> str:
    without_hash = {key: value for key, value in payload.items() if key != "receipt_sha256"}
    encoded = json.dumps(without_hash, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def _write_bundle_and_report(tmp_path: Path) -> tuple[Path, Path]:
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
    report = build_fire_settlement_apply_report(
        {
            "schema": "zenodex/fire-settlement-apply-report/v1",
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
        }
    )
    report_path = tmp_path / "apply_report.json"
    report_path.write_text(json.dumps(report, sort_keys=True, indent=2), encoding="utf-8")
    return bundle_dir, report_path


def test_fire_settlement_apply_artifact_receipt_roundtrip(tmp_path: Path) -> None:
    bundle_dir, report_path = _write_bundle_and_report(tmp_path)
    receipt_path = tmp_path / "apply_artifact_receipt.json"
    receipt = write_fire_settlement_apply_artifact_receipt(receipt_path, report_path, bundle_dir)
    expected_witness_hash = fire_witness_binding_hash({"witness_final": 30})
    assert receipt["report_hash"].startswith("sha256:")
    assert receipt["witness_hash"] == expected_witness_hash
    check = check_fire_settlement_apply_artifact_receipt(receipt_path)
    assert check["accepted"] is True
    assert check["violated_checks"] == []
    assert check["witness_hash"] == expected_witness_hash


def test_fire_settlement_apply_artifact_receipt_detects_tamper(tmp_path: Path) -> None:
    bundle_dir, report_path = _write_bundle_and_report(tmp_path)
    receipt_path = tmp_path / "apply_artifact_receipt.json"
    write_fire_settlement_apply_artifact_receipt(receipt_path, report_path, bundle_dir)
    payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    payload["report_hash"] = "sha256:" + "9" * 64
    receipt_path.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")
    check = check_fire_settlement_apply_artifact_receipt(receipt_path)
    assert check["accepted"] is False
    assert "receipt_hash_mismatch" in check["violated_checks"]


def test_fire_settlement_apply_artifact_receipt_detects_witness_hash_drift(tmp_path: Path) -> None:
    bundle_dir, report_path = _write_bundle_and_report(tmp_path)
    receipt_path = tmp_path / "apply_artifact_receipt.json"
    write_fire_settlement_apply_artifact_receipt(receipt_path, report_path, bundle_dir)
    payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    payload["witness_hash"] = fire_witness_binding_hash({"witness_final": 31})
    payload["receipt_sha256"] = _receipt_hash(payload)
    receipt_path.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")
    check = check_fire_settlement_apply_artifact_receipt(receipt_path)
    assert check["accepted"] is False
    assert "witness_hash_mismatch" in check["violated_checks"]


def test_fire_settlement_apply_artifact_receipt_enforces_expected_identity(tmp_path: Path) -> None:
    bundle_dir, report_path = _write_bundle_and_report(tmp_path)
    receipt_path = tmp_path / "apply_artifact_receipt.json"
    receipt = write_fire_settlement_apply_artifact_receipt(receipt_path, report_path, bundle_dir)
    ok_check = check_fire_settlement_apply_artifact_receipt(
        receipt_path,
        expected_bundle_dir=bundle_dir,
        expected_bundle_hash=receipt["bundle_hash"],
        expected_object_hash=receipt["object_hash"],
        expected_instance_hash=receipt["instance_hash"],
        expected_cert_sha256=receipt["cert_sha256"],
        expected_witness_hash=receipt["witness_hash"],
        expected_report_hash=receipt["report_hash"],
    )
    assert ok_check["accepted"] is True

    bad_check = check_fire_settlement_apply_artifact_receipt(
        receipt_path,
        expected_object_hash="sha256:" + "7" * 64,
    )
    assert bad_check["accepted"] is False
    assert "expected_object_hash_mismatch" in bad_check["violated_checks"]

    bad_witness_check = check_fire_settlement_apply_artifact_receipt(
        receipt_path,
        expected_witness_hash=fire_witness_binding_hash({"witness_final": 31}),
    )
    assert bad_witness_check["accepted"] is False
    assert "expected_witness_hash_mismatch" in bad_witness_check["violated_checks"]


def test_fire_settlement_apply_artifact_receipt_expected_bundle_dir_derives_identity(tmp_path: Path) -> None:
    bundle_dir, report_path = _write_bundle_and_report(tmp_path)
    receipt_path = tmp_path / "apply_artifact_receipt.json"
    write_fire_settlement_apply_artifact_receipt(receipt_path, report_path, bundle_dir)

    other_root = tmp_path / "other"
    other_root.mkdir()
    other_bundle_dir, _other_report_path = _write_bundle_and_report(other_root)
    check = check_fire_settlement_apply_artifact_receipt(
        receipt_path,
        expected_bundle_dir=other_bundle_dir,
    )
    assert check["accepted"] is False
    assert "expected_bundle_dir_mismatch" in check["violated_checks"]
