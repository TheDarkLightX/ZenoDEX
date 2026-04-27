from __future__ import annotations

import hashlib
import json
from dataclasses import replace

from src.fire.registry.bundle_v1 import (
    FireBundleContractReceipt,
    fire_registry_bundle_file_sha256,
    fire_registry_bundle_sha256,
    load_fire_registry_bundle,
    verify_fire_registry_bundle,
    write_fire_registry_bundle,
)
from src.fire.registry.instance_v1 import (
    fire_object_instance_sha256,
    verify_fire_object_instance_against_manifest,
)
from src.fire.runtime.burn_boost_call_v1 import BurnBoostCallTerms, build_manifest, compile_terms, render_object_card
from src.fire.verifier.cert_v1 import FireIntervalCertificate


def test_fire_registry_bundle_write_load_and_verify(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"

    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    loaded_bundle_manifest, loaded_bundle_file_sha256, loaded_object_manifest, loaded_instance_manifest, loaded_object_lock = load_fire_registry_bundle(bundle_dir)
    ok, err, verified_bundle_manifest, verified_object_manifest, verified_instance_manifest, verified_object_lock = verify_fire_registry_bundle(
        bundle_dir,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_bundle_file_sha256=bundle_file_sha256,
    )

    assert loaded_bundle_manifest == bundle_manifest
    assert loaded_bundle_file_sha256 == bundle_file_sha256 == fire_registry_bundle_file_sha256(bundle_manifest)
    assert loaded_object_manifest == build_manifest(artifact)
    assert [item.name for item in loaded_object_manifest.parameters] == [
        "n_notional",
        "strike_index",
        "cap_index",
        "source_upper",
    ]
    assert loaded_instance_manifest.object_hash == loaded_object_manifest.manifest_hash
    assert loaded_object_lock.object_hash == loaded_object_manifest.manifest_hash
    assert ok is True
    assert err is None
    assert verified_bundle_manifest == bundle_manifest
    assert verified_object_manifest == build_manifest(artifact)
    assert verified_instance_manifest == loaded_instance_manifest
    assert verified_object_lock == loaded_object_lock
    gate_ok, gate_err, gate_report = verify_fire_object_instance_against_manifest(
        verified_instance_manifest,
        object_manifest=verified_object_manifest,
    )
    assert gate_ok is True, gate_err
    assert gate_report.ok is True
    certificate_payload = json.loads((bundle_dir / bundle_manifest.certificate_path).read_text(encoding="utf-8"))
    certificate = FireIntervalCertificate.from_dict(certificate_payload)
    assert certificate.instance_gate_claims is not None
    assert certificate.instance_gate_claims.param_ok == "implemented"
    assert bundle_manifest.contract_receipts == (
        FireBundleContractReceipt(
            name="burn_contract",
            roles=("import:burn_index_v1.burn_final", "witness:BurnCertificate[TDEX]"),
            use_sites=("import:burn_final", "witness:BurnCertificate[TDEX]"),
        ),
    )
    assert bundle_manifest.compile_receipt_path == "compile_receipt.json"
    assert bundle_manifest.compile_receipt_sha256 is not None
    assert bundle_manifest.kernel_receipt_path == "kernel_receipt.json"
    assert bundle_manifest.kernel_receipt_sha256 is not None
    assert bundle_manifest.kernel_eval_receipt_path == "kernel_eval_receipt.json"
    assert bundle_manifest.kernel_eval_receipt_sha256 is not None
    assert bundle_manifest.kernel_settlement_receipt_path == "kernel_settlement_receipt.json"
    assert bundle_manifest.kernel_settlement_receipt_sha256 is not None
    assert bundle_manifest.kernel_replay_receipt_path == "kernel_replay_receipt.json"
    assert bundle_manifest.kernel_replay_receipt_sha256 is not None
    assert bundle_manifest.proof_tree_certificate_path is None


def test_fire_registry_bundle_can_emit_optional_proof_tree_certificate(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle_proof_tree"

    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    ok, err, verified_bundle_manifest, verified_object_manifest, verified_instance_manifest, verified_object_lock = verify_fire_registry_bundle(
        bundle_dir,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_bundle_file_sha256=bundle_file_sha256,
    )

    assert ok is True, err
    assert verified_bundle_manifest is not None
    assert verified_object_manifest is not None
    assert verified_instance_manifest is not None
    assert verified_object_lock is not None
    assert verified_bundle_manifest.compile_receipt_path == "compile_receipt.json"
    assert verified_bundle_manifest.compile_receipt_sha256 is not None
    assert verified_bundle_manifest.kernel_receipt_path == "kernel_receipt.json"
    assert verified_bundle_manifest.kernel_receipt_sha256 is not None
    assert verified_bundle_manifest.kernel_eval_receipt_path == "kernel_eval_receipt.json"
    assert verified_bundle_manifest.kernel_eval_receipt_sha256 is not None
    assert verified_bundle_manifest.kernel_settlement_receipt_path == "kernel_settlement_receipt.json"
    assert verified_bundle_manifest.kernel_settlement_receipt_sha256 is not None
    assert verified_bundle_manifest.kernel_replay_receipt_path == "kernel_replay_receipt.json"
    assert verified_bundle_manifest.kernel_replay_receipt_sha256 is not None
    assert verified_bundle_manifest.proof_tree_certificate_path == "proof_tree_certificate.json"
    assert verified_bundle_manifest.proof_tree_certificate_sha256 is not None
    assert (bundle_dir / "proof_tree_certificate.json").exists()


def test_fire_registry_bundle_detects_contract_receipt_tamper(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"

    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    tampered = replace(
        bundle_manifest,
        contract_receipts=(
            FireBundleContractReceipt(
                name="drifted_contract",
                roles=("import:burn_index_v1.burn_final",),
                use_sites=("import:burn_final",),
            ),
        ),
    )
    tampered = replace(tampered, bundle_hash=fire_registry_bundle_sha256(tampered.payload_without_hash()))
    (bundle_dir / "bundle_manifest.json").write_text(
        json.dumps(tampered.to_dict(), sort_keys=True, separators=(",", ":"), ensure_ascii=True),
        encoding="utf-8",
    )

    ok, err, _, _, _, _ = verify_fire_registry_bundle(bundle_dir)

    assert ok is False
    assert err == "bundle_contract_receipts_mismatch"


def test_fire_registry_bundle_detects_instance_gate_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"

    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    instance_path = bundle_dir / bundle_manifest.object_instance_path
    payload = json.loads(instance_path.read_text(encoding="utf-8"))
    for item in payload["parameters"]:
        if item["name"] == "n_notional":
            item["value"] = 1001
    payload["instance_hash"] = fire_object_instance_sha256(
        {key: value for key, value in payload.items() if key != "instance_hash"}
    )
    instance_path.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True), encoding="utf-8")
    bundle_manifest_path = bundle_dir / "bundle_manifest.json"
    bundle_payload = json.loads(bundle_manifest_path.read_text(encoding="utf-8"))
    bundle_payload["artifacts"]["object_instance"]["sha256"] = "sha256:" + hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    ).hexdigest()
    bundle_payload["bundle_hash"] = fire_registry_bundle_sha256(
        {
            "schema": bundle_payload["schema"],
            "object_name": bundle_payload["object_name"],
            "object_version": bundle_payload["object_version"],
            "object_family": bundle_payload["object_family"],
            "artifacts": bundle_payload["artifacts"],
            "contracts": bundle_payload.get("contracts", []),
        }
    )
    bundle_manifest_path.write_text(
        json.dumps(bundle_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True),
        encoding="utf-8",
    )

    ok, err, _, _, _, _ = verify_fire_registry_bundle(bundle_dir)

    assert ok is False
    assert err == "object_instance_gate_invalid:param_out_of_range:n_notional"
