from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_bundle.py"
CHECK_CLI = REPO_ROOT / "tools" / "check_fire_compile_receipt.py"


def _build_burn_bundle(bundle_dir: Path) -> dict[str, object]:
    proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "burn_boost_call_v1",
            "--bundle-dir",
            str(bundle_dir),
            "--n-notional",
            "10",
            "--strike-index",
            "4",
            "--cap-index",
            "3",
            "--source-upper",
            "9",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    return json.loads(proc.stdout)


def test_check_fire_compile_receipt_cli_roundtrip(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    build_report = _build_burn_bundle(bundle_dir)

    receipt_path = bundle_dir / "compile_receipt.json"
    receipt_sha256 = "sha256:" + hashlib.sha256(receipt_path.read_bytes()).hexdigest()

    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--receipt-file",
            str(receipt_path),
            "--object-manifest-file",
            str(bundle_dir / "object_manifest.json"),
            "--instance-manifest-file",
            str(bundle_dir / "instance_manifest.json"),
            "--expected-receipt-sha256",
            receipt_sha256,
            "--expected-object-hash",
            str(build_report["object_hash"]),
            "--expected-instance-hash",
            str(build_report["instance_hash"]),
            "--expected-cert-sha256",
            str(build_report["cert_sha256"]),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["schema"] == "zenodex/fire-compile-receipt-check-report/v1"
    assert payload["ok"] is True
    assert payload["receipt_sha256"] == receipt_sha256
    assert payload["object_hash"] == build_report["object_hash"]
    assert payload["instance_hash"] == build_report["instance_hash"]
    assert payload["cert_sha256"] == build_report["cert_sha256"]

    receipt_payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    bindings = receipt_payload["formal_proof_bindings"]
    assert [item["binding_id"] for item in bindings] == [
        "fire_zpl_language_soundness_v1",
        "fire_cal_core_soundness_v1",
        "fire_zpl_fixed_point_bridge_v1",
    ]
    assert bindings[0]["module"] == "Proofs.ZenoPayoffLanguage"
    assert "compile_correct" in bindings[0]["theorems"]
    assert bindings[1]["module"] == "Proofs.CALCoreSoundness"
    assert "fireV_accept_soundness" in bindings[1]["theorems"]
    assert bindings[2]["module"] == "Proofs.ZenoPayoffPortfolioFixedPointBridge"
    assert "compile_sum_floorDecode_posted_collateral_safe" in bindings[2]["theorems"]
    assert "compile_sum_decodeByMode_posted_collateral_safe" in bindings[2]["theorems"]
    assert "compile_sum_decodeByMode_posted_collateral_safe_and_conserves" in bindings[2]["theorems"]
    assert "int_two_party_delta_receipt_safe_and_conserves" in bindings[2]["theorems"]
    assert "compile_sum_decodeByMode_two_party_delta_conserves" in bindings[2]["theorems"]


def test_check_fire_compile_receipt_cli_rejects_tampered_receipt(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    _build_burn_bundle(bundle_dir)

    receipt_path = bundle_dir / "compile_receipt.json"
    payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    payload["object_hash"] = "sha256:" + ("7" * 64)
    receipt_path.write_text(
        json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--receipt-file",
            str(receipt_path),
            "--object-manifest-file",
            str(bundle_dir / "object_manifest.json"),
            "--instance-manifest-file",
            str(bundle_dir / "instance_manifest.json"),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    error = json.loads(proc.stderr)
    assert error["schema"] == "zenodex/fire-compile-receipt-check-report/v1"
    assert error["ok"] is False
    assert error["error"] == "compile_receipt_mismatch"


def test_check_fire_compile_receipt_cli_rejects_formal_binding_drift(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    _build_burn_bundle(bundle_dir)

    receipt_path = bundle_dir / "compile_receipt.json"
    payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    payload["formal_proof_bindings"][0]["source_files"][0]["sha256"] = "sha256:" + ("1" * 64)
    receipt_path.write_text(
        json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--receipt-file",
            str(receipt_path),
            "--object-manifest-file",
            str(bundle_dir / "object_manifest.json"),
            "--instance-manifest-file",
            str(bundle_dir / "instance_manifest.json"),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    error = json.loads(proc.stderr)
    assert error["schema"] == "zenodex/fire-compile-receipt-check-report/v1"
    assert error["ok"] is False
    assert error["error"] == "compile_receipt_mismatch"
