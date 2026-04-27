from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_bundle.py"
CHECK_CLI = REPO_ROOT / "tools" / "check_fire_kernel_eval_receipt.py"


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


def test_check_fire_kernel_eval_receipt_cli_roundtrip(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    build_report = _build_burn_bundle(bundle_dir)

    receipt_path = bundle_dir / "kernel_eval_receipt.json"
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
            "--kernel-receipt-file",
            str(bundle_dir / "kernel_receipt.json"),
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
    assert payload["schema"] == "zenodex/fire-kernel-eval-receipt-check-report/v1"
    assert payload["ok"] is True
    assert payload["receipt_sha256"] == receipt_sha256
    assert payload["object_hash"] == build_report["object_hash"]
    assert payload["instance_hash"] == build_report["instance_hash"]
    assert payload["cert_sha256"] == build_report["cert_sha256"]
    assert payload["kernel_receipt_sha256"].startswith("sha256:")
    assert payload["compiled_artifact_lower"] == 0
    assert payload["compiled_artifact_upper"] == 30


def test_check_fire_kernel_eval_receipt_cli_rejects_tampered_receipt(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    _build_burn_bundle(bundle_dir)

    receipt_path = bundle_dir / "kernel_eval_receipt.json"
    payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    payload["compiled_artifact_upper"] = 31
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
            "--kernel-receipt-file",
            str(bundle_dir / "kernel_receipt.json"),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    error = json.loads(proc.stderr)
    assert error["schema"] == "zenodex/fire-kernel-eval-receipt-check-report/v1"
    assert error["ok"] is False
    assert error["error"] == "kernel_eval_receipt_mismatch"
