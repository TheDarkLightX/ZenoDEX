from __future__ import annotations

import copy
import json
import sys
from pathlib import Path

import pytest

from src.integration import zenodex_external_threshold_bls as ext
from src.integration import zenodex_threshold_bls as ref_tbls
from src.integration.zenodex_external_threshold_bls import (
    EXTERNAL_THRESHOLD_BLS_SIGNATURE_RECEIPT_SCHEMA_V0,
    build_external_threshold_bls_backend_descriptor_v0,
    build_external_threshold_bls_evidence_v0,
    build_external_threshold_bls_sign_request_v0,
    build_external_threshold_bls_signature_receipt_v0,
    run_external_threshold_bls_signer_v0,
    sha256_file_for_external_signer_v0,
    validate_external_threshold_bls_evidence_v0,
    validate_external_threshold_bls_sign_request_v0,
    validate_external_threshold_bls_signer_artifact_v0,
    verify_external_threshold_bls_signature_receipt_v0,
)
from src.integration.zenodex_threshold_bls import (
    build_threshold_bls_partial_signature_v0,
    combine_threshold_bls_partial_signatures_v0,
    generate_threshold_bls_key_v0,
)
from tools import zenodex_external_threshold_bls as ext_cli

pytestmark = pytest.mark.skipif(
    not ext._BLS_AVAILABLE or not ref_tbls._BLS_AVAILABLE,
    reason="py_ecc BLS dependency unavailable",
)


ROOT_A = "0x" + "aa" * 32
ROOT_B = "0x" + "bb" * 32
ROOT_C = "0x" + "cc" * 32
PAYLOAD = {
    "domain": "zenodex.ledger.checkpoint.v0",
    "chain_id": "tau-testnet-1",
    "nonce": 11,
    "checkpoint_hash": ROOT_A,
}


def _bundle_partials_and_aggregate() -> tuple[dict[str, object], list[dict[str, object]], dict[str, object]]:
    public_bundle, shares = generate_threshold_bls_key_v0(
        key_id="tau-external-threshold-main",
        threshold=2,
        participant_ids=("operator-a", "operator-b", "operator-c"),
    )
    partials = [
        build_threshold_bls_partial_signature_v0(shares[0], public_bundle=public_bundle, payload=PAYLOAD),
        build_threshold_bls_partial_signature_v0(shares[1], public_bundle=public_bundle, payload=PAYLOAD),
    ]
    aggregate = combine_threshold_bls_partial_signatures_v0(partials, public_bundle=public_bundle, payload=PAYLOAD)
    return public_bundle, partials, aggregate


def _evidence(public_bundle: dict[str, object], *, binary_sha256: str = ROOT_A) -> dict[str, object]:
    participants = [
        {
            "participant_id": item["participant_id"],
            "public_share_key": item["share_public_key"],
            "operator_key_hash": f"0x{index:064x}",
        }
        for index, item in enumerate(public_bundle["participants"], start=1)
    ]
    return build_external_threshold_bls_evidence_v0(
        provider_stack="ssv-dkg-drand-threshold-bls12-381-v1",
        service_id="wallet-threshold-service",
        service_version="1.0.0",
        binary_sha256=binary_sha256,
        public_key=str(public_bundle["public_key"]),
        threshold=int(public_bundle["threshold"]),
        participants=participants,
        dkg_transcript_hash=ROOT_B,
        audit_evidence=[
            {
                "name": "drand-and-ssv-dkg-public-audit-references",
                "report_uri": "https://docs.drand.love/blog/2023/05/26/tlock-security-assessment/",
                "report_hash": ROOT_C,
                "scope": "ssv-dkg-drand-threshold-bls12-381-v1 external threshold BLS stack",
            }
        ],
    )


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def test_external_threshold_bls_evidence_backend_and_signature_receipt_verify() -> None:
    public_bundle, partials, aggregate = _bundle_partials_and_aggregate()
    evidence = _evidence(public_bundle)
    validate_external_threshold_bls_evidence_v0(evidence)

    descriptor = build_external_threshold_bls_backend_descriptor_v0(
        key_id="tau-external-threshold-main",
        backend_id="external-threshold-bls",
        policy_hash=ROOT_C,
        evidence=evidence,
    )
    public_descriptor = descriptor.public_dict()
    assert public_descriptor["backend_kind"] == "threshold-bls-external-service"
    assert public_descriptor["metadata"]["external_threshold_bls_evidence_hash"] == evidence["evidence_hash"]
    assert public_descriptor["metadata"]["dealerless_dkg"] is True

    request = build_external_threshold_bls_sign_request_v0(
        key_id="tau-external-threshold-main",
        evidence_hash=str(evidence["evidence_hash"]),
        payload=PAYLOAD,
    )
    validate_external_threshold_bls_sign_request_v0(request)

    receipt = build_external_threshold_bls_signature_receipt_v0(
        evidence=evidence,
        payload=PAYLOAD,
        participant_ids=[str(item["participant_id"]) for item in partials],
        partial_signature_hashes=[str(item["partial_signature_hash"]) for item in partials],
        signature=str(aggregate["signature"]),
    )
    ok, err = verify_external_threshold_bls_signature_receipt_v0(
        receipt,
        evidence=evidence,
        payload=PAYLOAD,
    )
    assert receipt["schema"] == EXTERNAL_THRESHOLD_BLS_SIGNATURE_RECEIPT_SCHEMA_V0
    assert ok, err


def test_external_threshold_bls_rejects_unapproved_stack_missing_audit_and_bad_signature() -> None:
    public_bundle, partials, aggregate = _bundle_partials_and_aggregate()
    evidence = _evidence(public_bundle)

    bad_stack = {**evidence, "provider_stack": "custom-python-threshold-bls"}
    bad_stack["evidence_hash"] = ext.hash_v0(
        "zenodex_external_threshold_bls_evidence_v0",
        {key: bad_stack[key] for key in sorted(set(bad_stack) - {"evidence_hash"})},
    )
    with pytest.raises(ValueError, match="provider_stack is not approved"):
        validate_external_threshold_bls_evidence_v0(bad_stack)

    missing_audit = {**evidence, "audit_evidence": []}
    missing_audit["evidence_hash"] = ext.hash_v0(
        "zenodex_external_threshold_bls_evidence_v0",
        {key: missing_audit[key] for key in sorted(set(missing_audit) - {"evidence_hash"})},
    )
    with pytest.raises(ValueError, match="audit_evidence is required"):
        validate_external_threshold_bls_evidence_v0(missing_audit)

    receipt = build_external_threshold_bls_signature_receipt_v0(
        evidence=evidence,
        payload=PAYLOAD,
        participant_ids=[str(item["participant_id"]) for item in partials],
        partial_signature_hashes=[str(item["partial_signature_hash"]) for item in partials],
        signature=str(aggregate["signature"]),
    )
    tampered = copy.deepcopy(receipt)
    tampered["signature"] = str(tampered["signature"])[:-1] + (
        "0" if str(tampered["signature"])[-1] != "0" else "1"
    )
    tampered["receipt_hash"] = ext.hash_v0(
        "zenodex_external_threshold_bls_signature_receipt_v0",
        {key: tampered[key] for key in sorted(set(tampered) - {"receipt_hash"})},
    )
    ok, err = verify_external_threshold_bls_signature_receipt_v0(
        tampered,
        evidence=evidence,
        payload=PAYLOAD,
    )
    assert ok is False
    assert err is not None and "aggregate signature invalid" in err


def test_external_threshold_bls_verifier_fails_closed_when_backend_disappears(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    public_bundle, partials, aggregate = _bundle_partials_and_aggregate()
    evidence = _evidence(public_bundle)
    receipt = build_external_threshold_bls_signature_receipt_v0(
        evidence=evidence,
        payload=PAYLOAD,
        participant_ids=[str(item["participant_id"]) for item in partials],
        partial_signature_hashes=[str(item["partial_signature_hash"]) for item in partials],
        signature=str(aggregate["signature"]),
    )

    monkeypatch.setattr(ext, "G2Basic", None)
    ok, err = verify_external_threshold_bls_signature_receipt_v0(
        receipt,
        evidence=evidence,
        payload=PAYLOAD,
    )

    assert ok is False
    assert err is not None
    assert "backend is unavailable" in err


def test_external_threshold_bls_runs_hash_pinned_out_of_process_contract_fixture(tmp_path: Path) -> None:
    public_bundle, shares = generate_threshold_bls_key_v0(
        key_id="tau-external-threshold-main",
        threshold=2,
        participant_ids=("operator-a", "operator-b", "operator-c"),
    )
    fixture_path = Path("tools/zenodex_external_threshold_bls_contract_fixture.py")
    evidence = _evidence(public_bundle, binary_sha256=sha256_file_for_external_signer_v0(fixture_path))
    validate_external_threshold_bls_signer_artifact_v0(evidence=evidence, signer_artifact_path=fixture_path)

    public_path = tmp_path / "public.json"
    evidence_path = tmp_path / "evidence.json"
    share_a_path = tmp_path / "share-a.json"
    share_b_path = tmp_path / "share-b.json"
    _write_json(public_path, public_bundle)
    _write_json(evidence_path, evidence)
    _write_json(share_a_path, shares[0])
    _write_json(share_b_path, shares[1])

    request = build_external_threshold_bls_sign_request_v0(
        key_id="tau-external-threshold-main",
        evidence_hash=str(evidence["evidence_hash"]),
        payload=PAYLOAD,
    )
    receipt = run_external_threshold_bls_signer_v0(
        command=[
            sys.executable,
            str(fixture_path),
            "--contract-test-only",
            "--evidence",
            str(evidence_path),
            "--public-bundle",
            str(public_path),
            "--share",
            str(share_a_path),
            "--share",
            str(share_b_path),
        ],
        request=request,
    )
    encoded = json.dumps(receipt, sort_keys=True)
    assert str(shares[0]["share_secret_hex"]) not in encoded
    assert str(shares[1]["share_secret_hex"]) not in encoded

    ok, err = verify_external_threshold_bls_signature_receipt_v0(receipt, evidence=evidence, payload=PAYLOAD)
    assert ok, err


def test_external_threshold_bls_cli_sign_and_verify_with_hash_pinned_contract_fixture(
    tmp_path: Path,
    capsys,
) -> None:
    public_bundle, shares = generate_threshold_bls_key_v0(
        key_id="tau-external-threshold-main",
        threshold=2,
        participant_ids=("operator-a", "operator-b", "operator-c"),
    )
    fixture_path = Path("tools/zenodex_external_threshold_bls_contract_fixture.py")
    evidence = _evidence(public_bundle, binary_sha256=sha256_file_for_external_signer_v0(fixture_path))
    public_path = tmp_path / "public.json"
    evidence_path = tmp_path / "evidence.json"
    payload_path = tmp_path / "payload.json"
    receipt_path = tmp_path / "receipt.json"
    share_a_path = tmp_path / "share-a.json"
    share_b_path = tmp_path / "share-b.json"
    _write_json(public_path, public_bundle)
    _write_json(evidence_path, evidence)
    _write_json(payload_path, PAYLOAD)
    _write_json(share_a_path, shares[0])
    _write_json(share_b_path, shares[1])

    rc = ext_cli.main(
        [
            "sign",
            "--key-id",
            "tau-external-threshold-main",
            "--evidence",
            str(evidence_path),
            "--payload-json",
            str(payload_path),
            "--signer-artifact",
            str(fixture_path),
            "--out",
            str(receipt_path),
            "--",
            sys.executable,
            str(fixture_path),
            "--contract-test-only",
            "--evidence",
            str(evidence_path),
            "--public-bundle",
            str(public_path),
            "--share",
            str(share_a_path),
            "--share",
            str(share_b_path),
        ]
    )
    assert rc == 0
    assert capsys.readouterr().err == ""
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert receipt["receipt_hash"].startswith("0x")

    rc = ext_cli.main(
        [
            "verify",
            "--evidence",
            str(evidence_path),
            "--payload-json",
            str(payload_path),
            "--receipt",
            str(receipt_path),
        ]
    )
    assert rc == 0
    report = json.loads(capsys.readouterr().out)
    assert report["ok"] is True


def test_external_threshold_bls_cli_rejects_signer_artifact_hash_mismatch(tmp_path: Path, capsys) -> None:
    public_bundle, shares = generate_threshold_bls_key_v0(
        key_id="tau-external-threshold-main",
        threshold=2,
        participant_ids=("operator-a", "operator-b", "operator-c"),
    )
    fixture_path = Path("tools/zenodex_external_threshold_bls_contract_fixture.py")
    evidence = _evidence(public_bundle, binary_sha256=ROOT_A)
    public_path = tmp_path / "public.json"
    evidence_path = tmp_path / "evidence.json"
    payload_path = tmp_path / "payload.json"
    share_a_path = tmp_path / "share-a.json"
    share_b_path = tmp_path / "share-b.json"
    _write_json(public_path, public_bundle)
    _write_json(evidence_path, evidence)
    _write_json(payload_path, PAYLOAD)
    _write_json(share_a_path, shares[0])
    _write_json(share_b_path, shares[1])

    with pytest.raises(ValueError, match="signer artifact hash mismatch"):
        ext_cli.main(
            [
                "sign",
                "--key-id",
                "tau-external-threshold-main",
                "--evidence",
                str(evidence_path),
                "--payload-json",
                str(payload_path),
                "--signer-artifact",
                str(fixture_path),
                "--",
                sys.executable,
                str(fixture_path),
                "--contract-test-only",
                "--evidence",
                str(evidence_path),
                "--public-bundle",
                str(public_path),
                "--share",
                str(share_a_path),
                "--share",
                str(share_b_path),
            ]
        )
    assert capsys.readouterr().out == ""
