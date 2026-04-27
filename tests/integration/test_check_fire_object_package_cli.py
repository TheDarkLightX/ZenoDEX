from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.fire.registry.bundle_v1 import FireRegistryBundleManifest

REPO_ROOT = Path(__file__).resolve().parents[2]
BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_bundle.py"
CHECK_CLI = REPO_ROOT / "tools" / "check_fire_object_package.py"


def test_check_fire_object_package_cli_roundtrip(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    build = subprocess.run(
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
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )
    build_report = json.loads(build.stdout)

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--expected-bundle-hash",
            build_report["bundle_hash"],
            "--expected-bundle-file-sha256",
            build_report["bundle_file_sha256"],
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 0, check.stderr
    payload = json.loads(check.stdout)
    assert payload["schema"] == "zenodex/fire-object-package-check-report/v1"
    assert payload["ok"] is True
    assert payload["require_replay_input"] is False
    assert payload["require_compile_receipt"] is False
    assert payload["require_kernel_receipt"] is False
    assert payload["require_kernel_eval_receipt"] is False
    assert payload["require_kernel_replay_receipt"] is False
    assert payload["require_kernel_settlement_receipt"] is False
    assert payload["require_proof_tree_cert"] is False
    assert payload["compile_receipt_present"] is True
    assert payload["kernel_receipt_present"] is True
    assert payload["kernel_eval_receipt_present"] is True
    assert payload["kernel_replay_receipt_present"] is True
    assert payload["kernel_settlement_receipt_present"] is True
    assert payload["proof_tree_cert_present"] is False
    assert payload["replay_input_present"] is True
    assert payload["object_name"] == "BurnBoostCall"
    assert payload["bundle_hash"] == build_report["bundle_hash"]
    assert payload["object_hash"] == build_report["object_hash"]
    assert payload["instance_hash"] == build_report["instance_hash"]
    assert payload["artifact_schemas_valid"] is True
    assert payload["schema_files"]["object_package_schema"].endswith("src/fire/spec/object-package.schema.json")


def test_check_fire_object_package_cli_requires_replay_input(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    subprocess.run(
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
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )
    replay_input = bundle_dir / "replay_input.json"
    replay_input.unlink()
    bundle_manifest = bundle_dir / "bundle_manifest.json"
    payload = json.loads(bundle_manifest.read_text(encoding="utf-8"))
    existing = FireRegistryBundleManifest.from_dict(payload)
    without_replay = FireRegistryBundleManifest.build(
        object_name=existing.object_name,
        object_version=existing.object_version,
        object_family=existing.object_family,
        object_manifest_path=existing.object_manifest_path,
        object_manifest_file_sha256=existing.object_manifest_file_sha256,
        object_instance_path=existing.object_instance_path,
        object_instance_file_sha256=existing.object_instance_file_sha256,
        object_lock_path=existing.object_lock_path,
        object_lock_file_sha256=existing.object_lock_file_sha256,
        certificate_path=existing.certificate_path,
        certificate_file_sha256=existing.certificate_file_sha256,
        compile_receipt_path=existing.compile_receipt_path,
        compile_receipt_sha256=existing.compile_receipt_sha256,
        kernel_receipt_path=existing.kernel_receipt_path,
        kernel_receipt_sha256=existing.kernel_receipt_sha256,
        kernel_eval_receipt_path=existing.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=existing.kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=existing.kernel_replay_receipt_path,
        kernel_replay_receipt_sha256=existing.kernel_replay_receipt_sha256,
        kernel_settlement_receipt_path=existing.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=existing.kernel_settlement_receipt_sha256,
        object_card_path=existing.object_card_path,
        object_card_sha256=existing.object_card_sha256,
        contract_receipts=existing.contract_receipts,
    )
    bundle_manifest.write_text(json.dumps(without_replay.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--require-replay-input",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 1
    error = json.loads(check.stderr)
    assert error["ok"] is False
    assert error["require_replay_input"] is True
    assert error["require_compile_receipt"] is False
    assert error["require_kernel_receipt"] is False
    assert error["require_kernel_eval_receipt"] is False
    assert error["require_kernel_replay_receipt"] is False
    assert error["require_kernel_settlement_receipt"] is False
    assert error["require_proof_tree_cert"] is False
    assert error["error"] == "replay_input_missing"


def test_check_fire_object_package_cli_accepts_compile_receipt_when_required(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    subprocess.run(
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
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--require-compile-receipt",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 0, check.stderr
    payload = json.loads(check.stdout)
    assert payload["require_compile_receipt"] is True
    assert payload["compile_receipt_present"] is True


def test_check_fire_object_package_cli_accepts_kernel_receipt_when_required(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    subprocess.run(
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
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--require-kernel-receipt",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 0, check.stderr
    payload = json.loads(check.stdout)
    assert payload["require_kernel_receipt"] is True
    assert payload["kernel_receipt_present"] is True


def test_check_fire_object_package_cli_accepts_kernel_eval_receipt_when_required(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    subprocess.run(
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
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--require-kernel-eval-receipt",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 0, check.stderr
    payload = json.loads(check.stdout)
    assert payload["require_kernel_eval_receipt"] is True
    assert payload["kernel_eval_receipt_present"] is True


def test_check_fire_object_package_cli_accepts_kernel_replay_receipt_when_required(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    subprocess.run(
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
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--require-kernel-replay-receipt",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 0, check.stderr
    payload = json.loads(check.stdout)
    assert payload["require_kernel_replay_receipt"] is True
    assert payload["kernel_replay_receipt_present"] is True


def test_check_fire_object_package_cli_requires_kernel_replay_receipt_when_missing(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    subprocess.run(
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
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )
    kernel_replay_receipt = bundle_dir / "kernel_replay_receipt.json"
    kernel_replay_receipt.unlink()
    bundle_manifest = bundle_dir / "bundle_manifest.json"
    payload = json.loads(bundle_manifest.read_text(encoding="utf-8"))
    existing = FireRegistryBundleManifest.from_dict(payload)
    without_kernel_replay = FireRegistryBundleManifest.build(
        object_name=existing.object_name,
        object_version=existing.object_version,
        object_family=existing.object_family,
        object_manifest_path=existing.object_manifest_path,
        object_manifest_file_sha256=existing.object_manifest_file_sha256,
        object_instance_path=existing.object_instance_path,
        object_instance_file_sha256=existing.object_instance_file_sha256,
        object_lock_path=existing.object_lock_path,
        object_lock_file_sha256=existing.object_lock_file_sha256,
        certificate_path=existing.certificate_path,
        certificate_file_sha256=existing.certificate_file_sha256,
        compile_receipt_path=existing.compile_receipt_path,
        compile_receipt_sha256=existing.compile_receipt_sha256,
        kernel_receipt_path=existing.kernel_receipt_path,
        kernel_receipt_sha256=existing.kernel_receipt_sha256,
        kernel_eval_receipt_path=existing.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=existing.kernel_eval_receipt_sha256,
        kernel_settlement_receipt_path=existing.kernel_settlement_receipt_path,
        kernel_settlement_receipt_sha256=existing.kernel_settlement_receipt_sha256,
        replay_input_path=existing.replay_input_path,
        replay_input_sha256=existing.replay_input_sha256,
        replay_receipt_path=existing.replay_receipt_path,
        replay_receipt_sha256=existing.replay_receipt_sha256,
        object_card_path=existing.object_card_path,
        object_card_sha256=existing.object_card_sha256,
        contract_receipts=existing.contract_receipts,
    )
    bundle_manifest.write_text(
        json.dumps(without_kernel_replay.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--require-kernel-replay-receipt",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 1
    error = json.loads(check.stderr)
    assert error["ok"] is False
    assert error["require_kernel_replay_receipt"] is True
    assert error["error"] == "kernel_replay_receipt_missing"


def test_check_fire_object_package_cli_accepts_kernel_settlement_receipt_when_required(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    subprocess.run(
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
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--require-kernel-settlement-receipt",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 0, check.stderr
    payload = json.loads(check.stdout)
    assert payload["require_kernel_settlement_receipt"] is True
    assert payload["kernel_settlement_receipt_present"] is True


def test_check_fire_object_package_cli_requires_kernel_settlement_receipt_when_missing(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    subprocess.run(
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
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )
    kernel_settlement_receipt = bundle_dir / "kernel_settlement_receipt.json"
    kernel_settlement_receipt.unlink()
    bundle_manifest = bundle_dir / "bundle_manifest.json"
    payload = json.loads(bundle_manifest.read_text(encoding="utf-8"))
    existing = FireRegistryBundleManifest.from_dict(payload)
    without_kernel_settlement = FireRegistryBundleManifest.build(
        object_name=existing.object_name,
        object_version=existing.object_version,
        object_family=existing.object_family,
        object_manifest_path=existing.object_manifest_path,
        object_manifest_file_sha256=existing.object_manifest_file_sha256,
        object_instance_path=existing.object_instance_path,
        object_instance_file_sha256=existing.object_instance_file_sha256,
        object_lock_path=existing.object_lock_path,
        object_lock_file_sha256=existing.object_lock_file_sha256,
        certificate_path=existing.certificate_path,
        certificate_file_sha256=existing.certificate_file_sha256,
        compile_receipt_path=existing.compile_receipt_path,
        compile_receipt_sha256=existing.compile_receipt_sha256,
        kernel_receipt_path=existing.kernel_receipt_path,
        kernel_receipt_sha256=existing.kernel_receipt_sha256,
        kernel_eval_receipt_path=existing.kernel_eval_receipt_path,
        kernel_eval_receipt_sha256=existing.kernel_eval_receipt_sha256,
        kernel_replay_receipt_path=existing.kernel_replay_receipt_path,
        kernel_replay_receipt_sha256=existing.kernel_replay_receipt_sha256,
        replay_input_path=existing.replay_input_path,
        replay_input_sha256=existing.replay_input_sha256,
        replay_receipt_path=existing.replay_receipt_path,
        replay_receipt_sha256=existing.replay_receipt_sha256,
        object_card_path=existing.object_card_path,
        object_card_sha256=existing.object_card_sha256,
        contract_receipts=existing.contract_receipts,
    )
    bundle_manifest.write_text(
        json.dumps(without_kernel_settlement.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--require-kernel-settlement-receipt",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 1
    error = json.loads(check.stderr)
    assert error["ok"] is False
    assert error["require_kernel_settlement_receipt"] is True
    assert error["error"] == "kernel_settlement_receipt_missing"


def test_check_fire_object_package_cli_accepts_proof_tree_cert_when_required(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle"
    subprocess.run(
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
            "--emit-proof-tree-cert",
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--require-proof-tree-cert",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 0, check.stderr
    payload = json.loads(check.stdout)
    assert payload["require_proof_tree_cert"] is True
    assert payload["proof_tree_cert_present"] is True
