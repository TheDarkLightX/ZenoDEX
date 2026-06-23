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
GATE_CLI = REPO_ROOT / "tools" / "check_fire_settlement_replay_gate.py"


def _write_bundle(
    snapshot_dir: Path,
    object_id: str,
    raw_terms: dict[str, int],
    *,
    emit_proof_tree_certificate: bool = False,
) -> None:
    compiled = compile_fire_object(object_id, raw_terms)
    bundle_dir = snapshot_dir / object_id
    write_fire_registry_bundle(
        bundle_dir,
        artifact=compiled.artifact,
        build_manifest=lambda artifact: build_fmos_manifest(compiled.spec, artifact),
        render_object_card=lambda artifact: render_fmos_object_card(compiled.spec, artifact),
        emit_proof_tree_certificate=emit_proof_tree_certificate,
    )


def _write_snapshot(snapshot_dir: Path, *, emit_proof_tree_certificate: bool = False) -> None:
    _write_bundle(
        snapshot_dir,
        "burn_boost_call_v1",
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
        emit_proof_tree_certificate=emit_proof_tree_certificate,
    )
    _write_bundle(
        snapshot_dir,
        "fee_note_v1",
        {
            "n_notional": 10,
            "cap_index": 7,
            "source_upper": 2,
        },
        emit_proof_tree_certificate=emit_proof_tree_certificate,
    )
    _write_bundle(
        snapshot_dir,
        "lp_loss_cover_v1",
        {
            "n_notional": 10,
            "deductible": 2,
            "cap_amount": 5,
            "hodl_lower": 10,
            "hodl_upper": 20,
            "lpv_lower": 7,
            "lpv_upper": 12,
        },
        emit_proof_tree_certificate=emit_proof_tree_certificate,
    )


def test_check_fire_settlement_replay_gate_cli_roundtrip(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    snapshot_dir.mkdir()
    _write_snapshot(snapshot_dir)
    out_dir = tmp_path / "out"
    proc = subprocess.run(
        [
            sys.executable,
            str(GATE_CLI),
            "--snapshot-dir",
            str(snapshot_dir),
            "--output-dir",
            str(out_dir),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["require_bundle_replay_input"] is False
    assert report["case_count"] == 3
    assert {case["case_id"] for case in report["cases"]} == {
        "burn_boost_call_v1",
        "fee_note_v1",
        "lp_loss_cover_v1",
    }
    for case in report["cases"]:
        assert Path(case["apply_report_path"]).is_file()
        assert Path(case["apply_artifact_receipt_path"]).is_file()
        assert case["package_check_ok"] is True
        assert case["artifact_schemas_valid"] is True
        assert case["replay_input_source"] == "bundle"
        assert isinstance(case["derived_witness_values"], dict)
        expected_witness_hash = fire_witness_binding_hash(case["derived_witness_values"])
        assert case["expected_witness_hash"] == expected_witness_hash
        assert case["witness_hash"] == expected_witness_hash
        if case["case_id"] == "burn_boost_call_v1":
            assert case["derived_witness_values"] == {"witness_final": 0}
        if case["case_id"] == "fee_note_v1":
            assert case["derived_witness_values"] == {"witness_final": 0}
        if case["case_id"] == "lp_loss_cover_v1":
            assert case["derived_witness_values"] == {
                "witness_hodl_final": 10,
                "witness_lpv_final": 7,
            }


def test_check_fire_settlement_replay_gate_cli_requires_bundle_replay_input(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    snapshot_dir.mkdir()
    _write_snapshot(snapshot_dir)
    for object_id in ("burn_boost_call_v1", "fee_note_v1", "lp_loss_cover_v1"):
        replay_input = snapshot_dir / object_id / "replay_input.json"
        replay_input.unlink()
        bundle_manifest = snapshot_dir / object_id / "bundle_manifest.json"
        payload = json.loads(bundle_manifest.read_text(encoding="utf-8"))
        del payload["artifacts"]["replay_input"]
        bundle_manifest.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(GATE_CLI),
            "--snapshot-dir",
            str(snapshot_dir),
            "--output-dir",
            str(tmp_path / "out"),
            "--require-bundle-replay-input",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert report["require_bundle_replay_input"] is True
    assert all(case["ok"] is False for case in report["cases"])
    assert all(case["error"] == "bundle_inputs_unavailable:bundle_replay_input_required" for case in report["cases"])


def test_check_fire_snapshot_packages_cli_roundtrip(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    snapshot_dir.mkdir()
    _write_snapshot(snapshot_dir)
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "tools" / "check_fire_snapshot_packages.py"),
            "--snapshot-dir",
            str(snapshot_dir),
            "--require-replay-input",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["schema"] == "zenodex/fire-snapshot-package-check-report/v1"
    assert report["ok"] is True
    assert report["require_replay_input"] is True
    assert report["require_compile_receipt"] is False
    assert report["require_kernel_receipt"] is False
    assert report["require_kernel_eval_receipt"] is False
    assert report["require_kernel_replay_receipt"] is False
    assert report["require_kernel_settlement_receipt"] is False
    assert report["require_proof_tree_cert"] is False
    assert report["bundle_count"] == 3
    assert all(bundle["artifact_schemas_valid"] is True for bundle in report["bundles"])
    assert all(bundle["compile_receipt_present"] is True for bundle in report["bundles"])
    assert all(bundle["kernel_receipt_present"] is True for bundle in report["bundles"])
    assert all(bundle["kernel_eval_receipt_present"] is True for bundle in report["bundles"])
    assert all(bundle["kernel_replay_receipt_present"] is True for bundle in report["bundles"])
    assert all(bundle["kernel_settlement_receipt_present"] is True for bundle in report["bundles"])
    assert all(bundle["proof_tree_cert_present"] is False for bundle in report["bundles"])
    assert all(bundle["replay_input_present"] is True for bundle in report["bundles"])


def test_check_fire_snapshot_packages_cli_requires_proof_tree_cert(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    snapshot_dir.mkdir()
    _write_snapshot(snapshot_dir, emit_proof_tree_certificate=True)
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "tools" / "check_fire_snapshot_packages.py"),
            "--snapshot-dir",
            str(snapshot_dir),
            "--require-replay-input",
            "--require-proof-tree-cert",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["require_compile_receipt"] is False
    assert report["require_kernel_receipt"] is False
    assert report["require_kernel_eval_receipt"] is False
    assert report["require_kernel_replay_receipt"] is False
    assert report["require_kernel_settlement_receipt"] is False
    assert report["require_proof_tree_cert"] is True
    assert all(bundle["compile_receipt_present"] is True for bundle in report["bundles"])
    assert all(bundle["kernel_receipt_present"] is True for bundle in report["bundles"])
    assert all(bundle["kernel_eval_receipt_present"] is True for bundle in report["bundles"])
    assert all(bundle["kernel_replay_receipt_present"] is True for bundle in report["bundles"])
    assert all(bundle["kernel_settlement_receipt_present"] is True for bundle in report["bundles"])
    assert all(bundle["proof_tree_cert_present"] is True for bundle in report["bundles"])


def test_check_fire_snapshot_packages_cli_requires_compile_receipt(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    snapshot_dir.mkdir()
    _write_snapshot(snapshot_dir)
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "tools" / "check_fire_snapshot_packages.py"),
            "--snapshot-dir",
            str(snapshot_dir),
            "--require-replay-input",
            "--require-compile-receipt",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["require_compile_receipt"] is True
    assert all(bundle["compile_receipt_present"] is True for bundle in report["bundles"])


def test_check_fire_snapshot_packages_cli_requires_kernel_receipt(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    snapshot_dir.mkdir()
    _write_snapshot(snapshot_dir)
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "tools" / "check_fire_snapshot_packages.py"),
            "--snapshot-dir",
            str(snapshot_dir),
            "--require-replay-input",
            "--require-kernel-receipt",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["require_kernel_receipt"] is True
    assert all(bundle["kernel_receipt_present"] is True for bundle in report["bundles"])


def test_check_fire_snapshot_packages_cli_requires_kernel_eval_receipt(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    snapshot_dir.mkdir()
    _write_snapshot(snapshot_dir)
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "tools" / "check_fire_snapshot_packages.py"),
            "--snapshot-dir",
            str(snapshot_dir),
            "--require-replay-input",
            "--require-kernel-eval-receipt",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["require_kernel_eval_receipt"] is True
    assert all(bundle["kernel_eval_receipt_present"] is True for bundle in report["bundles"])


def test_check_fire_snapshot_packages_cli_requires_kernel_replay_receipt(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    snapshot_dir.mkdir()
    _write_snapshot(snapshot_dir)
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "tools" / "check_fire_snapshot_packages.py"),
            "--snapshot-dir",
            str(snapshot_dir),
            "--require-replay-input",
            "--require-kernel-replay-receipt",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["require_kernel_replay_receipt"] is True
    assert all(bundle["kernel_replay_receipt_present"] is True for bundle in report["bundles"])


def test_check_fire_snapshot_packages_cli_requires_kernel_settlement_receipt(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    snapshot_dir.mkdir()
    _write_snapshot(snapshot_dir)
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "tools" / "check_fire_snapshot_packages.py"),
            "--snapshot-dir",
            str(snapshot_dir),
            "--require-replay-input",
            "--require-kernel-settlement-receipt",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["require_kernel_settlement_receipt"] is True
    assert all(bundle["kernel_settlement_receipt_present"] is True for bundle in report["bundles"])


def test_check_fire_settlement_replay_gate_cli_rejects_missing_bundle(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    snapshot_dir.mkdir()
    _write_bundle(
        snapshot_dir,
        "burn_boost_call_v1",
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
    )
    proc = subprocess.run(
        [
            sys.executable,
            str(GATE_CLI),
            "--snapshot-dir",
            str(snapshot_dir),
            "--output-dir",
            str(tmp_path / "out"),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert any(case["ok"] is False for case in report["cases"])
