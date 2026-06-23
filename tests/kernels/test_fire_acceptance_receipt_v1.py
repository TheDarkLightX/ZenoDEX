from __future__ import annotations

import json
import subprocess
import sys

from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.runtime.burn_boost_call_v1 import BurnBoostCallTerms, build_manifest, compile_terms, render_object_card
from src.fire.verifier.acceptance_receipt_v1 import (
    build_fire_acceptance_receipt_for_bundle,
    verify_fire_acceptance_receipt_file,
    write_fire_acceptance_receipt,
)


STRICT_FLAGS = {
    "require_replay_input": True,
    "require_compile_receipt": True,
    "require_kernel_receipt": True,
    "require_kernel_eval_receipt": True,
    "require_kernel_replay_receipt": True,
    "require_kernel_settlement_receipt": True,
    "require_proof_tree_cert": True,
}


def _write_strict_bundle(tmp_path):
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )
    return bundle_dir, bundle_manifest, bundle_file_sha256


def test_fire_acceptance_receipt_accepts_strict_bundle(tmp_path) -> None:
    bundle_dir, bundle_manifest, bundle_file_sha256 = _write_strict_bundle(tmp_path)
    receipt_path = tmp_path / "fire_acceptance_receipt.json"

    receipt = write_fire_acceptance_receipt(
        receipt_path,
        bundle_dir,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_bundle_file_sha256=bundle_file_sha256,
        **STRICT_FLAGS,
    )

    assert receipt["schema"] == "zenodex/fire-acceptance-receipt/v1"
    assert receipt["bundle_hash"] == bundle_manifest.bundle_hash
    assert receipt["bundle_manifest_sha256"] == bundle_file_sha256
    assert receipt["package_acceptance"]["authorizes_settlement"] is False
    assert receipt["strict_requirements"]["proof_tree_certificate"] is True
    assert receipt["artifacts"]["kernel_replay_receipt"]["sha256"] == bundle_manifest.kernel_replay_receipt_sha256

    ok, err, verification = verify_fire_acceptance_receipt_file(
        receipt_path,
        bundle_dir=bundle_dir,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_bundle_file_sha256=bundle_file_sha256,
        **STRICT_FLAGS,
    )

    assert ok is True, err
    assert verification is not None
    report = verification.to_report_dict()
    assert report["schema"] == "zenodex/fire-acceptance-receipt-check-report/v1"
    assert report["authorizes_settlement"] is False
    assert report["bundle_hash"] == bundle_manifest.bundle_hash


def test_fire_acceptance_receipt_rejects_receipt_drift(tmp_path) -> None:
    bundle_dir, bundle_manifest, bundle_file_sha256 = _write_strict_bundle(tmp_path)
    receipt_path = tmp_path / "fire_acceptance_receipt.json"
    write_fire_acceptance_receipt(
        receipt_path,
        bundle_dir,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_bundle_file_sha256=bundle_file_sha256,
        **STRICT_FLAGS,
    )

    payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    payload["object_hash"] = "sha256:" + ("7" * 64)
    receipt_path.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")

    ok, err, verification = verify_fire_acceptance_receipt_file(
        receipt_path,
        bundle_dir=bundle_dir,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_bundle_file_sha256=bundle_file_sha256,
        **STRICT_FLAGS,
    )

    assert ok is False
    assert err == "acceptance_receipt_hash_mismatch"
    assert verification is None


def test_build_and_check_fire_acceptance_receipt_cli(tmp_path) -> None:
    bundle_dir, bundle_manifest, bundle_file_sha256 = _write_strict_bundle(tmp_path)
    receipt_path = tmp_path / "fire_acceptance_receipt.json"
    strict_args = [
        "--require-replay-input",
        "--require-compile-receipt",
        "--require-kernel-receipt",
        "--require-kernel-eval-receipt",
        "--require-kernel-replay-receipt",
        "--require-kernel-settlement-receipt",
        "--require-proof-tree-cert",
    ]

    build_result = subprocess.run(
        [
            sys.executable,
            "tools/build_fire_acceptance_receipt.py",
            "--bundle-dir",
            str(bundle_dir),
            "--output",
            str(receipt_path),
            "--expected-bundle-hash",
            bundle_manifest.bundle_hash,
            "--expected-bundle-file-sha256",
            bundle_file_sha256,
            *strict_args,
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert build_result.returncode == 0, build_result.stderr
    build_report = json.loads(build_result.stdout)
    assert build_report["ok"] is True
    assert build_report["authorizes_settlement"] is False

    check_result = subprocess.run(
        [
            sys.executable,
            "tools/check_fire_acceptance_receipt.py",
            "--receipt-file",
            str(receipt_path),
            "--bundle-dir",
            str(bundle_dir),
            "--expected-bundle-hash",
            bundle_manifest.bundle_hash,
            "--expected-bundle-file-sha256",
            bundle_file_sha256,
            *strict_args,
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert check_result.returncode == 0, check_result.stderr
    check_report = json.loads(check_result.stdout)
    assert check_report["ok"] is True
    assert check_report["bundle_hash"] == bundle_manifest.bundle_hash


def test_fire_acceptance_receipt_builder_requires_strict_artifact(tmp_path) -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle_without_proof_tree"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=False,
    )

    try:
        build_fire_acceptance_receipt_for_bundle(bundle_dir, **STRICT_FLAGS)
    except ValueError as exc:
        assert str(exc) == "proof_tree_certificate_missing"
    else:
        raise AssertionError("strict acceptance receipt build should reject missing proof_tree_certificate")
