from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.fire.compiler.compiler_registry_v1 import compile_fire_object
from src.fire.compiler.fmos_v1 import build_fmos_manifest, render_fmos_object_card
from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.verifier.settlement_v1 import fire_witness_binding_hash


REPO_ROOT = Path(__file__).resolve().parents[2]
APPLY_CLI = REPO_ROOT / "tools" / "apply_fire_settlement.py"
BUILD_CLI = REPO_ROOT / "tools" / "build_fire_settlement_apply_artifact_receipt.py"
CHECK_CLI = REPO_ROOT / "tools" / "check_fire_settlement_apply_artifact_receipt.py"


def _write_bundle(tmp_path: Path, object_id: str, raw_terms: dict[str, int]) -> Path:
    compiled = compile_fire_object(object_id, raw_terms)
    bundle_dir = tmp_path / object_id
    write_fire_registry_bundle(
        bundle_dir,
        artifact=compiled.artifact,
        build_manifest=lambda artifact: build_fmos_manifest(compiled.spec, artifact),
        render_object_card=lambda artifact: render_fmos_object_card(compiled.spec, artifact),
    )
    return bundle_dir


def test_fire_settlement_apply_artifact_receipt_cli_roundtrip(tmp_path: Path) -> None:
    expected_witness_hash = fire_witness_binding_hash({"witness_final": 7})
    bundle_dir = _write_bundle(
        tmp_path,
        "burn_boost_call_v1",
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
    )
    apply_proc = subprocess.run(
        [
            sys.executable,
            str(APPLY_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--holder-posted",
            "0",
            "--writer-posted",
            "30",
            "--holder-balance",
            "100",
            "--writer-balance",
            "250",
            "--witness-final",
            "7",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert apply_proc.returncode == 0, apply_proc.stderr
    report_path = tmp_path / "apply_report.json"
    report_path.write_text(apply_proc.stdout, encoding="utf-8")

    receipt_path = tmp_path / "apply_artifact_receipt.json"
    build_proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "--report-file",
            str(report_path),
            "--bundle-dir",
            str(bundle_dir),
            "--output",
            str(receipt_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert build_proc.returncode == 0, build_proc.stderr
    build_report = json.loads(build_proc.stdout)
    assert build_report["ok"] is True
    assert build_report["report_hash"].startswith("sha256:")
    assert build_report["object_hash"].startswith("sha256:")
    assert build_report["instance_hash"].startswith("sha256:")
    assert build_report["cert_sha256"].startswith("sha256:")
    assert build_report["witness_hash"] == expected_witness_hash

    check_proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--receipt-file",
            str(receipt_path),
            "--expected-bundle-dir",
            str(bundle_dir),
            "--expected-witness-hash",
            expected_witness_hash,
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check_proc.returncode == 0, check_proc.stderr
    check_report = json.loads(check_proc.stdout)
    assert check_report["ok"] is True
    assert check_report["report_hash"] == build_report["report_hash"]
    assert check_report["object_hash"] == build_report["object_hash"]
    assert check_report["instance_hash"] == build_report["instance_hash"]
    assert check_report["cert_sha256"] == build_report["cert_sha256"]
    assert check_report["witness_hash"] == expected_witness_hash


def test_fire_settlement_apply_artifact_receipt_cli_rejects_tampered_receipt(tmp_path: Path) -> None:
    bundle_dir = _write_bundle(
        tmp_path,
        "fee_note_v1",
        {
            "n_notional": 10,
            "cap_index": 7,
            "source_upper": 2,
        },
    )
    apply_proc = subprocess.run(
        [
            sys.executable,
            str(APPLY_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--holder-posted",
            "0",
            "--writer-posted",
            "20",
            "--holder-balance",
            "40",
            "--writer-balance",
            "90",
            "--witness-final",
            "2",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert apply_proc.returncode == 0, apply_proc.stderr
    report_path = tmp_path / "apply_report.json"
    report_path.write_text(apply_proc.stdout, encoding="utf-8")
    receipt_path = tmp_path / "apply_artifact_receipt.json"
    subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "--report-file",
            str(report_path),
            "--bundle-dir",
            str(bundle_dir),
            "--output",
            str(receipt_path),
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )
    receipt_payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    receipt_payload["report_hash"] = "sha256:" + "8" * 64
    receipt_path.write_text(json.dumps(receipt_payload, sort_keys=True, indent=2), encoding="utf-8")

    check_proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--receipt-file",
            str(receipt_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check_proc.returncode == 1
    check_report = json.loads(check_proc.stderr)
    assert check_report["ok"] is False
    assert "receipt_hash_mismatch" in check_report["violated_checks"]


def test_fire_settlement_apply_artifact_receipt_cli_rejects_expected_identity_mismatch(tmp_path: Path) -> None:
    bundle_dir = _write_bundle(
        tmp_path,
        "burn_boost_call_v1",
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
    )
    report_path = tmp_path / "apply_report.json"
    apply_proc = subprocess.run(
        [
            sys.executable,
            str(APPLY_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--holder-posted",
            "0",
            "--writer-posted",
            "30",
            "--holder-balance",
            "100",
            "--writer-balance",
            "250",
            "--witness-final",
            "7",
            "--output-report-file",
            str(report_path),
            "--output-artifact-receipt-file",
            str(tmp_path / "receipt_from_apply.json"),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert apply_proc.returncode == 0, apply_proc.stderr
    receipt_path = tmp_path / "receipt_from_apply.json"

    check_proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--receipt-file",
            str(receipt_path),
            "--expected-object-hash",
            "sha256:" + "1" * 64,
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check_proc.returncode == 1
    check_report = json.loads(check_proc.stderr)
    assert check_report["ok"] is False
    assert "expected_object_hash_mismatch" in check_report["violated_checks"]

    witness_check_proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--receipt-file",
            str(receipt_path),
            "--expected-witness-hash",
            fire_witness_binding_hash({"witness_final": 8}),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert witness_check_proc.returncode == 1
    witness_check_report = json.loads(witness_check_proc.stderr)
    assert witness_check_report["ok"] is False
    assert "expected_witness_hash_mismatch" in witness_check_report["violated_checks"]
