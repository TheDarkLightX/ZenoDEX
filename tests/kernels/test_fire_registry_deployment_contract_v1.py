from __future__ import annotations

import json
from pathlib import Path

from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.registry.deployment_contract_v1 import (
    FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA,
    build_fire_registry_deployment_receipt,
    check_fire_registry_deployment_receipt,
    enforce_fire_registry_deployment_contract,
    write_fire_registry_deployment_receipt,
)
from src.fire.registry.index_v1 import write_fire_registry_index
from src.fire.registry.release_v1 import write_fire_registry_release_metadata
from src.fire.runtime.burn_boost_call_v1 import (
    BurnBoostCallTerms,
    build_manifest,
    compile_terms,
    render_object_card,
)


def _write_contract(path: Path, *, snapshot_name: str, signer_pubkey: str, require_signature: bool = True) -> None:
    payload = {
        "schema": FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA,
        "contract_id": f"fire.registry.deploy.{snapshot_name}.v1",
        "snapshot_name": snapshot_name,
        "required_signer_pubkey": signer_pubkey,
        "require_signature": require_signature,
        "description": "Test FIRE registry deployment contract.",
    }
    path.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")


def test_fire_registry_deployment_contract_enforcement_and_receipt(tmp_path: Path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    index_path = tmp_path / "fire_registry_index.json"
    index, index_file_sha256 = write_fire_registry_index(index_path, [bundle_dir], signer_privkey="74")
    metadata_path = tmp_path / "release_metadata.json"
    write_fire_registry_release_metadata(
        metadata_path,
        snapshot_name="release_candidate_v1",
        index_path=index_path.name,
        index_hash=index.index_hash,
        index_file_sha256=index_file_sha256,
        require_signature=True,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signer_pubkey=index.signer_pubkey,
    )
    contract_path = tmp_path / "deployment_contract.json"
    _write_contract(contract_path, snapshot_name="release_candidate_v1", signer_pubkey=index.signer_pubkey)

    ok, err, contract = enforce_fire_registry_deployment_contract(
        contract_path,
        snapshot_name="release_candidate_v1",
        signer_pubkey=index.signer_pubkey,
        require_signature=True,
    )
    assert ok is True, err
    assert contract is not None

    receipt_path = tmp_path / "deployment_receipt.json"
    write_fire_registry_deployment_receipt(receipt_path, contract_path, metadata_path)
    report = check_fire_registry_deployment_receipt(receipt_path, require_current=True)
    assert report["accepted"] is True
    assert report["violated_checks"] == []
    assert [row["name"] for row in report["rebuilt_receipt"]["contracts"]] == ["burn_contract"]


def test_fire_registry_deployment_contract_detects_signer_mismatch(tmp_path: Path) -> None:
    contract_path = tmp_path / "deployment_contract.json"
    _write_contract(
        contract_path,
        snapshot_name="release_candidate_v1",
        signer_pubkey="0x" + ("00" * 48),
    )

    ok, err, contract = enforce_fire_registry_deployment_contract(
        contract_path,
        snapshot_name="release_candidate_v1",
        signer_pubkey="0x" + ("11" * 48),
        require_signature=True,
    )
    assert ok is False
    assert err == "deployment_contract_signer_pubkey_mismatch"
    assert contract is None


def test_fire_registry_deployment_receipt_detects_contract_summary_tamper(tmp_path: Path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    index_path = tmp_path / "fire_registry_index.json"
    index, index_file_sha256 = write_fire_registry_index(index_path, [bundle_dir], signer_privkey="74")
    metadata_path = tmp_path / "release_metadata.json"
    write_fire_registry_release_metadata(
        metadata_path,
        snapshot_name="release_candidate_v1",
        index_path=index_path.name,
        index_hash=index.index_hash,
        index_file_sha256=index_file_sha256,
        require_signature=True,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signer_pubkey=index.signer_pubkey,
    )
    contract_path = tmp_path / "deployment_contract.json"
    _write_contract(contract_path, snapshot_name="release_candidate_v1", signer_pubkey=index.signer_pubkey)

    receipt_path = tmp_path / "deployment_receipt.json"
    write_fire_registry_deployment_receipt(receipt_path, contract_path, metadata_path)
    payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    payload["contracts"][0]["name"] = "tampered_contract"
    payload["receipt_sha256"] = "bad"
    receipt_path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    report = check_fire_registry_deployment_receipt(receipt_path, require_current=True)
    assert report["accepted"] is False
    assert "receipt_hash_mismatch" in report["violated_checks"] or "contracts_mismatch" in report["violated_checks"]


def test_fire_registry_deployment_receipt_detects_contract_policy_mismatch(tmp_path: Path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    index_path = tmp_path / "fire_registry_index.json"
    index, index_file_sha256 = write_fire_registry_index(index_path, [bundle_dir], signer_privkey="74")
    metadata_path = tmp_path / "release_metadata.json"
    write_fire_registry_release_metadata(
        metadata_path,
        snapshot_name="release_candidate_v1",
        index_path=index_path.name,
        index_hash=index.index_hash,
        index_file_sha256=index_file_sha256,
        require_signature=True,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signer_pubkey=index.signer_pubkey,
    )
    contract_path = tmp_path / "deployment_contract.json"
    _write_contract(contract_path, snapshot_name="release_candidate_v1", signer_pubkey=index.signer_pubkey)
    contract_payload = json.loads(contract_path.read_text(encoding="utf-8"))
    contract_payload["contracts"] = [
        {
            "name": "wrong_contract",
            "roles": ["import:burn_index_v1.burn_final"],
            "object_refs": ["BurnBoostCall@v1"],
            "use_sites": ["BurnBoostCall@v1:import:burn_final"],
        }
    ]
    contract_path.write_text(json.dumps(contract_payload, sort_keys=True, indent=2), encoding="utf-8")

    try:
        build_fire_registry_deployment_receipt(contract_path, metadata_path)
    except ValueError as exc:
        assert str(exc) == "release contracts do not match deployment contract"
    else:
        raise AssertionError("expected deployment receipt build to reject mismatched contract policy")
