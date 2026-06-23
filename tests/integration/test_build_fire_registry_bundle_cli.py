from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.fire.registry.bundle_v1 import verify_fire_registry_bundle


REPO_ROOT = Path(__file__).resolve().parents[2]
BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_bundle.py"


def test_build_fire_registry_bundle_cli_roundtrip_all_supported_families(tmp_path: Path) -> None:
    cases = [
        (
            "burn_boost_call_v1",
            [
                "--n-notional",
                "10",
                "--strike-index",
                "4",
                "--cap-index",
                "3",
                "--source-upper",
                "9",
            ],
            "BurnBoostCall",
        ),
        (
            "fee_note_v1",
            [
                "--n-notional",
                "11",
                "--cap-index",
                "7",
                "--source-upper",
                "12",
            ],
            "FeeNote",
        ),
        (
            "lp_loss_cover_v1",
            [
                "--n-notional",
                "2",
                "--deductible",
                "5",
                "--cap-amount",
                "40",
                "--hodl-lower",
                "30",
                "--hodl-upper",
                "80",
                "--lpv-lower",
                "10",
                "--lpv-upper",
                "60",
            ],
            "LPLossCover",
        ),
    ]

    for object_id, object_args, expected_name in cases:
        bundle_dir = tmp_path / object_id
        proc = subprocess.run(
            [
                sys.executable,
                str(BUILD_CLI),
                object_id,
                "--bundle-dir",
                str(bundle_dir),
                *object_args,
                "--pretty",
            ],
            cwd=str(REPO_ROOT),
            check=False,
            capture_output=True,
            text=True,
        )

        assert proc.returncode == 0, proc.stderr
        report = json.loads(proc.stdout)
        assert report["schema"] == "zenodex/fire-registry-bundle-build-report/v1"
        assert report["ok"] is True
        assert report["object_id"] == object_id
        assert report["object_name"] == expected_name
        assert report["compile_receipt_path"] is not None
        assert report["kernel_receipt_path"] is not None
        assert report["kernel_eval_receipt_path"] is not None
        assert report["kernel_settlement_receipt_path"] is not None
        assert report["kernel_replay_receipt_path"] is not None

        ok, err, bundle_manifest, object_manifest, object_instance, object_lock = verify_fire_registry_bundle(
            bundle_dir,
            expected_bundle_hash=report["bundle_hash"],
            expected_bundle_file_sha256=report["bundle_file_sha256"],
        )
        assert ok is True, err
        assert bundle_manifest is not None
        assert object_manifest is not None
        assert object_instance is not None
        assert object_lock is not None
        assert object_manifest.object_name == expected_name
        assert object_manifest.manifest_hash == report["object_hash"] == report["manifest_hash"]
        assert object_instance.instance_hash == report["instance_hash"]
        assert object_lock.lock_hash == report["lock_hash"]
        assert object_manifest.cert_sha256 == report["cert_sha256"]
        assert report["certificate_instance_gate_claims"] == {
            "param_ok": "implemented",
            "authorization_ok": "implemented",
            "nonce_ok": "implemented",
            "maturity_ok": "implemented",
            "window_ok": "implemented",
        }
        assert report["object_card_noncanonical"] is True
        assert "Instance gate claim evidence:" in report["object_card_text"]
        assert "ParamOK: implemented" in report["object_card_text"]
        assert report["replay_input_path"] is not None
        assert object_manifest.artifact_lower == report["artifact_lower"]
        assert object_manifest.artifact_upper == report["artifact_upper"]
        assert report["instance_gates"]["ok"] is True
        assert report["instance_gates"]["param_ok"] is True


def test_build_fire_registry_bundle_cli_includes_replay_receipt(tmp_path: Path) -> None:
    replay_receipt_path = tmp_path / "replay_receipt.input.json"
    replay_receipt_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/fire-replay-receipt/v1",
                "receipt_id": "replay.burn.001",
                "kernel_model_id": "fire_burn_boost_call_v1",
                "ok": True,
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    bundle_dir = tmp_path / "burn_bundle"

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
            "--replay-receipt",
            str(replay_receipt_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["replay_receipt_path"] is not None

    ok, err, bundle_manifest, _object_manifest, object_instance, object_lock = verify_fire_registry_bundle(
        bundle_dir,
        expected_bundle_hash=report["bundle_hash"],
        expected_bundle_file_sha256=report["bundle_file_sha256"],
    )
    assert ok is True, err
    assert bundle_manifest is not None
    assert object_instance is not None
    assert object_lock is not None
    assert bundle_manifest.compile_receipt_path == "compile_receipt.json"
    assert bundle_manifest.kernel_receipt_path == "kernel_receipt.json"
    assert bundle_manifest.kernel_eval_receipt_path == "kernel_eval_receipt.json"
    assert bundle_manifest.kernel_settlement_receipt_path == "kernel_settlement_receipt.json"
    assert bundle_manifest.kernel_replay_receipt_path == "kernel_replay_receipt.json"
    assert bundle_manifest.replay_input_path == "replay_input.json"
    assert bundle_manifest.replay_receipt_path == "replay_receipt.json"
    assert report["instance_manifest_path"].endswith("instance_manifest.json")
    assert report["object_lock_path"].endswith("object_lock.json")


def test_build_fire_registry_bundle_cli_can_emit_proof_tree_sidecar(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle_proof_tree"

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
            "--emit-proof-tree-cert",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["compile_receipt_path"] is not None
    assert report["kernel_receipt_path"] is not None
    assert report["kernel_eval_receipt_path"] is not None
    assert report["kernel_settlement_receipt_path"] is not None
    assert report["kernel_replay_receipt_path"] is not None
    assert report["proof_tree_cert_path"] is not None
    assert report["proof_tree_cert_non_authoritative"] is True

    ok, err, bundle_manifest, _object_manifest, _object_instance, _object_lock = verify_fire_registry_bundle(
        bundle_dir,
        expected_bundle_hash=report["bundle_hash"],
        expected_bundle_file_sha256=report["bundle_file_sha256"],
    )
    assert ok is True, err
    assert bundle_manifest is not None
    assert bundle_manifest.proof_tree_certificate_path == "proof_tree_certificate.json"


def test_build_fire_registry_bundle_cli_accepts_optional_maturity_and_window(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "burn_bundle_windowed"

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
            "--maturity",
            "2026-07-01T00:00:00Z",
            "--settlement-window-start",
            "2026-07-01T00:00:00Z",
            "--settlement-window-end",
            "2026-07-02T00:00:00Z",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["instance_maturity"] == "2026-07-01T00:00:00Z"
    assert report["instance_settlement_window"] == {
        "start": "2026-07-01T00:00:00Z",
        "end": "2026-07-02T00:00:00Z",
    }
    assert report["instance_gates"]["maturity_ok"] is True
    assert report["instance_gates"]["window_ok"] is True


def test_build_fire_registry_bundle_cli_accepts_canonical_zpl_source(tmp_path: Path) -> None:
    zpl_source = REPO_ROOT / "src" / "kernels" / "zpl" / "burn_boost_call_v1.zpl"
    bundle_dir = tmp_path / "burn_bundle_zpl"

    proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "burn_boost_call_v1",
            "--bundle-dir",
            str(bundle_dir),
            "--zpl-source",
            str(zpl_source),
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
    report = json.loads(proc.stdout)
    assert report["object_id"] == "burn_boost_call_v1"
    assert report["zpl_source_file"] == str(zpl_source.resolve())


def test_build_fire_registry_bundle_cli_accepts_semantically_equivalent_zpl_source(tmp_path: Path) -> None:
    equivalent_source = tmp_path / "burn_boost_call_v1_equiv.zpl"
    equivalent_source.write_text(
        (REPO_ROOT / "src" / "kernels" / "zpl" / "burn_boost_call_v1.zpl")
        .read_text(encoding="utf-8")
        .replace(
            "positive_part(sub(source_bound(burn_final), exact_param(strike_index)))",
            "max(sub(source_bound(burn_final), exact_param(strike_index)), const(0))",
        ),
        encoding="utf-8",
    )
    bundle_dir = tmp_path / "burn_bundle_equiv_zpl"

    proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "burn_boost_call_v1",
            "--bundle-dir",
            str(bundle_dir),
            "--zpl-source",
            str(equivalent_source),
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
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr


def test_build_fire_registry_bundle_cli_rejects_drifted_zpl_source(tmp_path: Path) -> None:
    drifted_source = tmp_path / "burn_boost_call_v1_drifted.zpl"
    drifted_source.write_text(
        (REPO_ROOT / "src" / "kernels" / "zpl" / "burn_boost_call_v1.zpl")
        .read_text(encoding="utf-8")
        .replace('summary "N * min(max(BurnIndex_T - K, 0), Cap)";', 'summary "drifted";', 1),
        encoding="utf-8",
    )
    bundle_dir = tmp_path / "burn_bundle_bad_zpl"

    proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "burn_boost_call_v1",
            "--bundle-dir",
            str(bundle_dir),
            "--zpl-source",
            str(drifted_source),
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
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "line 7, col 1" in proc.stderr
    assert "compiled ZPL source is runtime-incompatible for burn_boost_call_v1: static_spec_mismatch:payoff_summary" in proc.stderr


def test_build_fire_registry_bundle_cli_reports_named_contract_drift_at_contract_span(tmp_path: Path) -> None:
    drifted_source = tmp_path / "burn_boost_call_v1_contract_drifted.zpl"
    drifted_source.write_text(
        (REPO_ROOT / "src" / "kernels" / "zpl" / "burn_boost_call_v1.zpl")
        .read_text(encoding="utf-8")
        .replace(
            "contract burn_contract Index const:0 term:source_upper;",
            "contract burn_contract Index const:1 term:source_upper;",
            1,
        ),
        encoding="utf-8",
    )
    bundle_dir = tmp_path / "burn_bundle_contract_drift"

    proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "burn_boost_call_v1",
            "--bundle-dir",
            str(bundle_dir),
            "--zpl-source",
            str(drifted_source),
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
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "line 13, col 1" in proc.stderr
    assert "compiled ZPL source is runtime-incompatible for burn_boost_call_v1: source_requirements_mismatch:contract" in proc.stderr
    assert (
        "[contract burn_contract for import burn_final <- burn_index_v1.burn_final -> "
        "expected producer guarantee burn_index_v1.burn_final for burn_final: Index in [0, 9]]"
    ) in proc.stderr


def test_build_fire_registry_bundle_cli_rejects_invalid_lp_interval(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "lp_bundle"
    proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "lp_loss_cover_v1",
            "--bundle-dir",
            str(bundle_dir),
            "--n-notional",
            "2",
            "--deductible",
            "5",
            "--cap-amount",
            "40",
            "--hodl-lower",
            "80",
            "--hodl-upper",
            "30",
            "--lpv-lower",
            "10",
            "--lpv-upper",
            "60",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "hodl interval out of order" in proc.stderr
