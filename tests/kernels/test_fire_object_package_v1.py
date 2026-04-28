from __future__ import annotations

import hashlib
import json

from src.fire.pathing_v1 import (
    fire_cert_schema_path,
    fire_cert_rules_schema_path,
    fire_compile_receipt_schema_path,
    fire_instance_schema_path,
    fire_ir_schema_path,
    fire_kernel_eval_receipt_schema_path,
    fire_kernel_replay_receipt_schema_path,
    fire_kernel_receipt_schema_path,
    fire_kernel_settlement_receipt_schema_path,
    fire_lock_schema_path,
    fire_object_package_schema_path,
    fire_replay_input_schema_path,
)
from src.fire.registry.bundle_v1 import FireRegistryBundleManifest, write_fire_registry_bundle
from src.fire.verifier.object_package_v1 import verify_fire_object_package
from src.fire.runtime.burn_boost_call_v1 import BurnBoostCallTerms, build_manifest, compile_terms, render_object_card


def _rewrite_bundle_manifest_with_proof_tree_sha(
    bundle_dir,
    bundle_manifest: FireRegistryBundleManifest,
    proof_tree_sha256: str,
) -> None:
    rewritten_bundle_manifest = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=None,
        kernel_replay_receipt_sha256=None,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=proof_tree_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    (bundle_dir / "bundle_manifest.json").write_text(
        json.dumps(rewritten_bundle_manifest.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )


def test_fire_object_package_verify_accepts_current_bundle(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_bundle_file_sha256=bundle_file_sha256,
    )

    assert ok is True, err
    assert verification is not None
    report = verification.to_report_dict()
    assert report["schema"] == "zenodex/fire-object-package-check-report/v1"
    assert report["artifact_schemas_valid"] is True
    assert report["replay_input_present"] is True
    assert report["bundle_hash"] == bundle_manifest.bundle_hash
    assert report["expected_certificate_instance_gate_claims"]["authorization_ok"] == "implemented"
    assert report["schema_files"] == {
        "object_manifest_schema": str(fire_ir_schema_path().resolve()),
        "object_instance_schema": str(fire_instance_schema_path().resolve()),
        "object_lock_schema": str(fire_lock_schema_path().resolve()),
        "certificate_schema": str(fire_cert_schema_path().resolve()),
        "compile_receipt_schema": str(fire_compile_receipt_schema_path().resolve()),
        "kernel_receipt_schema": str(fire_kernel_receipt_schema_path().resolve()),
        "kernel_eval_receipt_schema": str(fire_kernel_eval_receipt_schema_path().resolve()),
        "kernel_replay_receipt_schema": str(fire_kernel_replay_receipt_schema_path().resolve()),
        "kernel_settlement_receipt_schema": str(fire_kernel_settlement_receipt_schema_path().resolve()),
        "proof_tree_certificate_schema": str(fire_cert_rules_schema_path().resolve()),
        "replay_input_schema": str(fire_replay_input_schema_path().resolve()),
        "object_package_schema": str(fire_object_package_schema_path().resolve()),
    }
    assert report["compile_receipt_present"] is True
    assert report["kernel_receipt_present"] is True
    assert report["kernel_eval_receipt_present"] is True
    assert report["kernel_replay_receipt_present"] is True
    assert report["kernel_settlement_receipt_present"] is True
    assert report["proof_tree_cert_present"] is False


def test_fire_object_package_verify_rejects_schema_drift_in_bundle_manifest(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    bundle_manifest_path = bundle_dir / "bundle_manifest.json"
    bundle_payload = json.loads(bundle_manifest_path.read_text(encoding="utf-8"))
    bundle_payload["unexpected"] = True
    bundle_manifest_path.write_text(
        json.dumps(bundle_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True),
        encoding="utf-8",
    )

    ok, err, verification = verify_fire_object_package(bundle_dir)

    assert ok is False
    assert verification is None
    assert err is not None
    assert err.startswith("object_package_schema_invalid:")


def test_fire_object_package_verify_requires_replay_input_when_requested(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    replay_input_path = bundle_dir / "replay_input.json"
    replay_input_path.unlink()
    bundle_manifest_path = bundle_dir / "bundle_manifest.json"
    bundle_without_replay = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=None,
        kernel_replay_receipt_sha256=None,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    bundle_manifest_path.write_text(json.dumps(bundle_without_replay.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_replay_input=True,
    )

    assert bundle_manifest.replay_input_path == "replay_input.json"
    assert ok is False
    assert verification is None
    assert err == "replay_input_missing"


def test_fire_object_package_verify_requires_compile_receipt_when_requested(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    compile_receipt = bundle_dir / "compile_receipt.json"
    compile_receipt.unlink()
    bundle_manifest_path = bundle_dir / "bundle_manifest.json"
    payload = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=None,
        compile_receipt_sha256=None,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=bundle_manifest.kernel_replay_receipt_path,
        kernel_replay_receipt_sha256=bundle_manifest.kernel_replay_receipt_sha256,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=bundle_manifest.proof_tree_certificate_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    bundle_manifest_path.write_text(json.dumps(payload.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    ok, err, verification = verify_fire_object_package(bundle_dir, require_compile_receipt=True)

    assert ok is False
    assert verification is None
    assert err == "compile_receipt_missing"


def test_fire_object_package_verify_requires_kernel_receipt_when_requested(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    kernel_receipt = bundle_dir / "kernel_receipt.json"
    kernel_receipt.unlink()
    bundle_manifest_path = bundle_dir / "bundle_manifest.json"
    payload = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
        kernel_receipt_path=None,
        kernel_receipt_sha256=None,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=bundle_manifest.kernel_replay_receipt_path,
        kernel_replay_receipt_sha256=bundle_manifest.kernel_replay_receipt_sha256,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=bundle_manifest.proof_tree_certificate_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    bundle_manifest_path.write_text(json.dumps(payload.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    ok, err, verification = verify_fire_object_package(bundle_dir, require_kernel_receipt=True)

    assert ok is False
    assert verification is None
    assert err == "kernel_receipt_missing"


def test_fire_object_package_verify_requires_kernel_eval_receipt_when_requested(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    kernel_eval_receipt = bundle_dir / "kernel_eval_receipt.json"
    kernel_eval_receipt.unlink()
    bundle_manifest_path = bundle_dir / "bundle_manifest.json"
    payload = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        kernel_eval_receipt_path=None,
        kernel_eval_receipt_sha256=None,
        kernel_replay_receipt_path=bundle_manifest.kernel_replay_receipt_path,
        kernel_replay_receipt_sha256=bundle_manifest.kernel_replay_receipt_sha256,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=bundle_manifest.proof_tree_certificate_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    bundle_manifest_path.write_text(json.dumps(payload.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    ok, err, verification = verify_fire_object_package(bundle_dir, require_kernel_eval_receipt=True)

    assert ok is False
    assert verification is None
    assert err == "kernel_eval_receipt_missing"


def test_fire_object_package_verify_requires_kernel_settlement_receipt_when_requested(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    kernel_settlement_receipt = bundle_dir / "kernel_settlement_receipt.json"
    kernel_settlement_receipt.unlink()
    bundle_manifest_path = bundle_dir / "bundle_manifest.json"
    payload = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=bundle_manifest.kernel_replay_receipt_path,
        kernel_replay_receipt_sha256=bundle_manifest.kernel_replay_receipt_sha256,
        kernel_settlement_receipt_path=None,
        kernel_settlement_receipt_sha256=None,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=bundle_manifest.proof_tree_certificate_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    bundle_manifest_path.write_text(json.dumps(payload.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    ok, err, verification = verify_fire_object_package(bundle_dir, require_kernel_settlement_receipt=True)

    assert ok is False
    assert verification is None
    assert err == "kernel_settlement_receipt_missing"


def test_fire_object_package_verify_requires_kernel_replay_receipt_when_requested(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    kernel_replay_receipt = bundle_dir / "kernel_replay_receipt.json"
    kernel_replay_receipt.unlink()
    bundle_manifest_path = bundle_dir / "bundle_manifest.json"
    payload = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=None,
        kernel_replay_receipt_sha256=None,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=bundle_manifest.proof_tree_certificate_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    bundle_manifest_path.write_text(json.dumps(payload.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    ok, err, verification = verify_fire_object_package(bundle_dir, require_kernel_replay_receipt=True)

    assert ok is False
    assert verification is None
    assert err == "kernel_replay_receipt_missing"


def test_fire_object_package_verify_accepts_optional_proof_tree_cert(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_bundle_file_sha256=bundle_file_sha256,
        require_proof_tree_cert=True,
    )

    assert ok is True, err
    assert verification is not None
    report = verification.to_report_dict()
    assert report["proof_tree_cert_present"] is True


def test_fire_object_package_verify_requires_proof_tree_cert_when_requested(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_certificate_missing"


def test_fire_object_package_verify_rejects_proof_tree_cert_drift_from_runtime_cert(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree_payload["certificate_sha256"] = "sha256:" + ("9" * 64)
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()

    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_certificate_sha256_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_runtime_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    summary = proof_tree_payload["runtime_certificate_summary"]
    assert isinstance(summary, dict)
    root_interval = summary["root_interval"]
    assert isinstance(root_interval, dict)
    root_interval["upper"] = 31
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()

    bundle_manifest_path = bundle_dir / "bundle_manifest.json"
    bundle_manifest = FireRegistryBundleManifest.from_dict(json.loads(bundle_manifest_path.read_text(encoding="utf-8")))
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_runtime_certificate_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_replay_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    replay_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_replay")
    assert isinstance(replay_node, dict)
    claim = replay_node["claim"]
    assert isinstance(claim, dict)
    claim["holder_balance"] = 999
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_replay_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_integer_eval_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    integer_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_integer_eval")
    assert isinstance(integer_node, dict)
    claim = integer_node["claim"]
    assert isinstance(claim, dict)
    claim["runtime_node_count"] = 999
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_integer_eval_summary_mismatch"


def test_fire_object_package_verify_rejects_compile_receipt_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    compile_receipt_path = bundle_dir / "compile_receipt.json"
    compile_receipt_payload = json.loads(compile_receipt_path.read_text(encoding="utf-8"))
    compile_receipt_payload["object_hash"] = "sha256:" + ("6" * 64)
    compile_receipt_text = json.dumps(compile_receipt_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    compile_receipt_path.write_text(compile_receipt_text, encoding="utf-8")
    compile_receipt_sha256 = "sha256:" + hashlib.sha256(compile_receipt_text.encode("utf-8")).hexdigest()
    rewritten_bundle_manifest = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=compile_receipt_sha256,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=bundle_manifest.proof_tree_certificate_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    (bundle_dir / "bundle_manifest.json").write_text(
        json.dumps(rewritten_bundle_manifest.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    ok, err, verification = verify_fire_object_package(bundle_dir)

    assert ok is False
    assert verification is None
    assert err == "compile_receipt_mismatch"


def test_fire_object_package_verify_rejects_kernel_receipt_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    kernel_receipt_path = bundle_dir / "kernel_receipt.json"
    kernel_receipt_payload = json.loads(kernel_receipt_path.read_text(encoding="utf-8"))
    kernel_receipt_payload["kernel_model_id"] = "fire_drifted_kernel"
    kernel_receipt_text = json.dumps(kernel_receipt_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    kernel_receipt_path.write_text(kernel_receipt_text, encoding="utf-8")
    kernel_receipt_sha256 = "sha256:" + hashlib.sha256(kernel_receipt_text.encode("utf-8")).hexdigest()
    rewritten_bundle_manifest = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=kernel_receipt_sha256,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=bundle_manifest.proof_tree_certificate_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    (bundle_dir / "bundle_manifest.json").write_text(
        json.dumps(rewritten_bundle_manifest.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    ok, err, verification = verify_fire_object_package(bundle_dir)

    assert ok is False
    assert verification is None
    assert err == "kernel_receipt_mismatch"


def test_fire_object_package_verify_rejects_kernel_eval_receipt_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    kernel_eval_receipt_path = bundle_dir / "kernel_eval_receipt.json"
    kernel_eval_receipt_payload = json.loads(kernel_eval_receipt_path.read_text(encoding="utf-8"))
    kernel_eval_receipt_payload["compiled_artifact_upper"] = 31
    kernel_eval_receipt_text = json.dumps(
        kernel_eval_receipt_payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    )
    kernel_eval_receipt_path.write_text(kernel_eval_receipt_text, encoding="utf-8")
    kernel_eval_receipt_sha256 = "sha256:" + hashlib.sha256(kernel_eval_receipt_text.encode("utf-8")).hexdigest()
    rewritten_bundle_manifest = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=bundle_manifest.kernel_replay_receipt_path,
        kernel_replay_receipt_sha256=bundle_manifest.kernel_replay_receipt_sha256,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=bundle_manifest.proof_tree_certificate_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    (bundle_dir / "bundle_manifest.json").write_text(
        json.dumps(rewritten_bundle_manifest.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    ok, err, verification = verify_fire_object_package(bundle_dir)

    assert ok is False
    assert verification is None
    assert err == "compiled_artifact_upper_mismatch"


def test_fire_object_package_verify_rejects_kernel_replay_receipt_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    kernel_replay_receipt_path = bundle_dir / "kernel_replay_receipt.json"
    kernel_replay_receipt_payload = json.loads(kernel_replay_receipt_path.read_text(encoding="utf-8"))
    kernel_replay_receipt_payload["delta_sha256"] = "sha256:" + ("7" * 64)
    kernel_replay_receipt_text = json.dumps(
        kernel_replay_receipt_payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    )
    kernel_replay_receipt_path.write_text(kernel_replay_receipt_text, encoding="utf-8")
    kernel_replay_receipt_sha256 = "sha256:" + hashlib.sha256(kernel_replay_receipt_text.encode("utf-8")).hexdigest()
    rewritten_bundle_manifest = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=bundle_manifest.kernel_replay_receipt_path,
        kernel_replay_receipt_sha256=kernel_replay_receipt_sha256,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=bundle_manifest.proof_tree_certificate_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    (bundle_dir / "bundle_manifest.json").write_text(
        json.dumps(rewritten_bundle_manifest.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    ok, err, verification = verify_fire_object_package(bundle_dir)

    assert ok is False
    assert verification is None
    assert err == "kernel_replay_receipt_mismatch"


def test_fire_object_package_verify_rejects_kernel_settlement_receipt_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    kernel_settlement_receipt_path = bundle_dir / "kernel_settlement_receipt.json"
    kernel_settlement_receipt_payload = json.loads(kernel_settlement_receipt_path.read_text(encoding="utf-8"))
    kernel_settlement_receipt_payload["payoff_out"] = 1
    kernel_settlement_receipt_text = json.dumps(
        kernel_settlement_receipt_payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    )
    kernel_settlement_receipt_path.write_text(kernel_settlement_receipt_text, encoding="utf-8")
    kernel_settlement_receipt_sha256 = "sha256:" + hashlib.sha256(
        kernel_settlement_receipt_text.encode("utf-8")
    ).hexdigest()
    rewritten_bundle_manifest = FireRegistryBundleManifest.build(
        object_name=bundle_manifest.object_name,
        object_version=bundle_manifest.object_version,
        object_family=bundle_manifest.object_family,
        object_manifest_path=bundle_manifest.object_manifest_path,
        object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
        object_instance_path=bundle_manifest.object_instance_path,
        object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
        object_lock_path=bundle_manifest.object_lock_path,
        object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
        certificate_path=bundle_manifest.certificate_path,
        certificate_file_sha256=bundle_manifest.certificate_file_sha256,
        compile_receipt_path=bundle_manifest.compile_receipt_path,
        compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
        kernel_receipt_path=bundle_manifest.kernel_receipt_path,
        kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        kernel_eval_receipt_path=bundle_manifest.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=bundle_manifest.kernel_replay_receipt_path,
        kernel_replay_receipt_sha256=bundle_manifest.kernel_replay_receipt_sha256,
        kernel_settlement_receipt_path=bundle_manifest.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=kernel_settlement_receipt_sha256,
        proof_tree_certificate_path=bundle_manifest.proof_tree_certificate_path,
        proof_tree_certificate_sha256=bundle_manifest.proof_tree_certificate_sha256,
        replay_input_path=bundle_manifest.replay_input_path,
        replay_input_sha256=bundle_manifest.replay_input_sha256,
        replay_receipt_path=bundle_manifest.replay_receipt_path,
        replay_receipt_sha256=bundle_manifest.replay_receipt_sha256,
        object_card_path=bundle_manifest.object_card_path,
        object_card_sha256=bundle_manifest.object_card_sha256,
        contract_receipts=bundle_manifest.contract_receipts,
    )
    (bundle_dir / "bundle_manifest.json").write_text(
        json.dumps(rewritten_bundle_manifest.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    ok, err, verification = verify_fire_object_package(bundle_dir)

    assert ok is False
    assert verification is None
    assert err == "payoff_out_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_unit_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    unit_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_unit")
    assert isinstance(unit_node, dict)
    claim = unit_node["claim"]
    assert isinstance(claim, dict)
    claim["settlement_asset"] = "badUSD"
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_unit_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_witness_policy_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    witness_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_witness")
    assert isinstance(witness_node, dict)
    claim = witness_node["claim"]
    assert isinstance(claim, dict)
    claim["witness_requirements"] = []
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_witness_policy_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_witness_contract_receipt_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    witness_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_witness")
    assert isinstance(witness_node, dict)
    claim = witness_node["claim"]
    assert isinstance(claim, dict)
    contract_receipts = claim["contract_receipts"]
    assert isinstance(contract_receipts, list)
    first = contract_receipts[0]
    assert isinstance(first, dict)
    first["use_sites"] = ["witness:drifted"]
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_witness_policy_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_param_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    param_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_param")
    assert isinstance(param_node, dict)
    claim = param_node["claim"]
    assert isinstance(claim, dict)
    parameters = claim["parameters"]
    assert isinstance(parameters, list)
    first = parameters[0]
    assert isinstance(first, dict)
    first["value"] = 999
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_param_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_authorization_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    authorization_node = next(
        node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_authorization"
    )
    assert isinstance(authorization_node, dict)
    claim = authorization_node["claim"]
    assert isinstance(claim, dict)
    bound_parties = claim["bound_parties"]
    assert isinstance(bound_parties, list)
    first = bound_parties[0]
    assert isinstance(first, dict)
    first["party_id"] = "role:attacker"
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_authorization_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_nonce_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    nonce_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_nonce")
    assert isinstance(nonce_node, dict)
    claim = nonce_node["claim"]
    assert isinstance(claim, dict)
    claim["nonce"] = "bad:nonce"
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_nonce_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_maturity_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    maturity_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_maturity")
    assert isinstance(maturity_node, dict)
    claim = maturity_node["claim"]
    assert isinstance(claim, dict)
    claim["maturity_present"] = True
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_maturity_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_window_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    window_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_window")
    assert isinstance(window_node, dict)
    claim = window_node["claim"]
    assert isinstance(claim, dict)
    claim["settlement_window_present"] = True
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_window_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_object_bind_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_object_hash")
    assert isinstance(node, dict)
    claim = node["claim"]
    assert isinstance(claim, dict)
    claim["object_manifest_sha256"] = "sha256:" + ("9" * 64)
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_object_bind_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_instance_bind_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_instance_hash")
    assert isinstance(node, dict)
    claim = node["claim"]
    assert isinstance(claim, dict)
    claim["instance_manifest_sha256"] = "sha256:" + ("8" * 64)
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_instance_bind_summary_mismatch"


def test_fire_object_package_verify_rejects_proof_tree_dependency_summary_drift(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, _ = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )

    proof_tree_path = bundle_dir / "proof_tree_certificate.json"
    proof_tree_payload = json.loads(proof_tree_path.read_text(encoding="utf-8"))
    proof_tree = proof_tree_payload["proof_tree"]
    assert isinstance(proof_tree, list)
    node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_dependency_closed")
    assert isinstance(node, dict)
    claim = node["claim"]
    assert isinstance(claim, dict)
    claim["object_lock_sha256"] = "sha256:" + ("7" * 64)
    proof_tree_text = json.dumps(proof_tree_payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    proof_tree_path.write_text(proof_tree_text, encoding="utf-8")
    proof_tree_sha256 = "sha256:" + hashlib.sha256(proof_tree_text.encode("utf-8")).hexdigest()
    _rewrite_bundle_manifest_with_proof_tree_sha(bundle_dir, bundle_manifest, proof_tree_sha256)

    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        require_proof_tree_cert=True,
    )

    assert ok is False
    assert verification is None
    assert err == "proof_tree_cert_dependency_summary_mismatch"
