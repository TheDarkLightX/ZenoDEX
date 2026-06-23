from __future__ import annotations

import json

import pytest

from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.registry.index_v1 import (
    FireRegistryContractReceipt,
    FireRegistryInstanceGateClaimSummary,
    FireRegistryInstanceGateSummary,
    write_fire_registry_index,
)
from src.fire.registry.release_v1 import (
    fire_registry_release_metadata_file_sha256,
    load_fire_registry_release_metadata,
    verify_fire_registry_release,
    verify_fire_registry_release_metadata,
    write_fire_registry_release_metadata,
)
from src.fire.runtime.burn_boost_call_v1 import (
    BurnBoostCallTerms,
    build_manifest,
    compile_terms,
    render_object_card,
)


def test_fire_registry_contract_receipt_rejects_non_string_object_ref() -> None:
    with pytest.raises(TypeError, match=r"registry contract receipt object_refs\[0\] must be a string"):
        FireRegistryContractReceipt.from_dict(
            {
                "name": "oracle_contract",
                "roles": ["import:oracle.price"],
                "object_refs": [1],
                "use_sites": ["BurnBoostCall@v1:import:oracle"],
            }
        )


def test_fire_registry_release_metadata_write_load_and_verify(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    index_path = tmp_path / "fire_registry_index.json"
    index, index_file_sha256 = write_fire_registry_index(index_path, [bundle_dir], signer_privkey="73")
    metadata_path = tmp_path / "release_metadata.json"

    metadata, metadata_file_sha256 = write_fire_registry_release_metadata(
        metadata_path,
        snapshot_name="tmp_snapshot",
        index_path=index_path.name,
        index_hash=index.index_hash,
        index_file_sha256=index_file_sha256,
        require_signature=True,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signer_pubkey=index.signer_pubkey,
    )
    loaded_metadata, loaded_metadata_file_sha256 = load_fire_registry_release_metadata(metadata_path)
    ok, err, verified_metadata = verify_fire_registry_release(
        metadata_path,
        expected_snapshot_name="tmp_snapshot",
        expected_metadata_file_sha256=metadata_file_sha256,
    )

    assert loaded_metadata == metadata
    assert loaded_metadata_file_sha256 == metadata_file_sha256 == fire_registry_release_metadata_file_sha256(metadata)
    assert ok is True, err
    assert verified_metadata == metadata
    assert metadata.instance_gate_summary == index.instance_gate_summary
    assert metadata.certificate_instance_gate_summary == index.certificate_instance_gate_summary


def test_fire_registry_release_metadata_detects_snapshot_name_mismatch(tmp_path) -> None:
    metadata_path = tmp_path / "release_metadata.json"
    write_fire_registry_release_metadata(
        metadata_path,
        snapshot_name="tmp_snapshot",
        index_path="fire_registry_index.json",
        index_hash="sha256:" + "1" * 64,
        index_file_sha256="sha256:" + "2" * 64,
        require_signature=False,
        instance_gate_summary=FireRegistryInstanceGateSummary(
            entry_count=0,
            all_ok=True,
            param_ok_count=0,
            authorization_ok_count=0,
            nonce_ok_count=0,
            maturity_ok_count=0,
            window_ok_count=0,
        ),
        certificate_instance_gate_summary=FireRegistryInstanceGateClaimSummary(
            entry_count=0,
            param_ok="proved",
            authorization_ok="proved",
            nonce_ok="proved",
            maturity_ok="proved",
            window_ok="proved",
        ),
    )

    ok, err, metadata = verify_fire_registry_release_metadata(
        metadata_path,
        expected_snapshot_name="wrong_snapshot",
    )
    assert ok is False
    assert err == "expected_snapshot_name_mismatch"
    assert metadata is None


def test_fire_registry_release_verifier_detects_index_tamper(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    index_path = tmp_path / "fire_registry_index.json"
    index, index_file_sha256 = write_fire_registry_index(index_path, [bundle_dir], signer_privkey="73")
    metadata_path = tmp_path / "release_metadata.json"
    write_fire_registry_release_metadata(
        metadata_path,
        snapshot_name="tmp_snapshot",
        index_path=index_path.name,
        index_hash=index.index_hash,
        index_file_sha256=index_file_sha256,
        require_signature=True,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signer_pubkey=index.signer_pubkey,
    )

    payload = json.loads(index_path.read_text(encoding="utf-8"))
    payload["entries"][0]["object_name"] = "Tampered"
    index_path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    ok, err, metadata = verify_fire_registry_release(
        metadata_path,
        expected_snapshot_name="tmp_snapshot",
    )
    assert ok is False
    assert err == "release_index_invalid:index_hash_mismatch"
    assert metadata is None


def test_fire_registry_release_verifier_detects_contract_summary_tamper(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    index_path = tmp_path / "fire_registry_index.json"
    index, index_file_sha256 = write_fire_registry_index(index_path, [bundle_dir], signer_privkey="73")
    metadata_path = tmp_path / "release_metadata.json"
    write_fire_registry_release_metadata(
        metadata_path,
        snapshot_name="tmp_snapshot",
        index_path=index_path.name,
        index_hash=index.index_hash,
        index_file_sha256=index_file_sha256,
        require_signature=True,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signer_pubkey=index.signer_pubkey,
    )

    payload = json.loads(metadata_path.read_text(encoding="utf-8"))
    payload["contracts"][0]["name"] = "tampered_contract"
    metadata_path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    ok, err, metadata = verify_fire_registry_release(
        metadata_path,
        expected_snapshot_name="tmp_snapshot",
    )
    assert ok is False
    assert err == "release_contract_receipts_mismatch"
    assert metadata is None


def test_fire_registry_release_verifier_detects_instance_gate_summary_tamper(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    index_path = tmp_path / "fire_registry_index.json"
    index, index_file_sha256 = write_fire_registry_index(index_path, [bundle_dir], signer_privkey="73")
    metadata_path = tmp_path / "release_metadata.json"
    write_fire_registry_release_metadata(
        metadata_path,
        snapshot_name="tmp_snapshot",
        index_path=index_path.name,
        index_hash=index.index_hash,
        index_file_sha256=index_file_sha256,
        require_signature=True,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signer_pubkey=index.signer_pubkey,
    )

    payload = json.loads(metadata_path.read_text(encoding="utf-8"))
    payload["instance_gate_summary"]["param_ok_count"] = 0
    metadata_path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    ok, err, metadata = verify_fire_registry_release(
        metadata_path,
        expected_snapshot_name="tmp_snapshot",
    )
    assert ok is False
    assert err == "release_instance_gate_summary_mismatch"
    assert metadata is None


def test_fire_registry_release_verifier_detects_certificate_instance_gate_summary_tamper(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    index_path = tmp_path / "fire_registry_index.json"
    index, index_file_sha256 = write_fire_registry_index(index_path, [bundle_dir], signer_privkey="73")
    metadata_path = tmp_path / "release_metadata.json"
    write_fire_registry_release_metadata(
        metadata_path,
        snapshot_name="tmp_snapshot",
        index_path=index_path.name,
        index_hash=index.index_hash,
        index_file_sha256=index_file_sha256,
        require_signature=True,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signer_pubkey=index.signer_pubkey,
    )

    payload = json.loads(metadata_path.read_text(encoding="utf-8"))
    payload["certificate_instance_gate_summary"]["param_ok"] = "hypothesis"
    metadata_path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    ok, err, metadata = verify_fire_registry_release(
        metadata_path,
        expected_snapshot_name="tmp_snapshot",
    )
    assert ok is False
    assert err == "release_certificate_instance_gate_summary_mismatch"
    assert metadata is None
