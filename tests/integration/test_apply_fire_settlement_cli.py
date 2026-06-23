from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.fire.compiler.compiler_registry_v1 import compile_fire_object
from src.fire.compiler.fmos_v1 import build_fmos_manifest, render_fmos_object_card
from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.verifier.settlement_apply_artifact_v1 import check_fire_settlement_apply_artifact_receipt


REPO_ROOT = Path(__file__).resolve().parents[2]
APPLY_CLI = REPO_ROOT / "tools" / "apply_fire_settlement.py"


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


def test_apply_fire_settlement_cli_burn_bundle(tmp_path: Path) -> None:
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
    proc = subprocess.run(
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
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["schema"] == "zenodex/fire-settlement-apply-report/v1"
    assert report["ok"] is True
    assert report["report_hash"].startswith("sha256:")
    assert report["object_id"] == "burn_boost_call_v1"
    assert report["holder_delta"] == 30
    assert report["writer_delta"] == -30
    assert report["holder_balance_after"] == 130
    assert report["writer_balance_after"] == 220
    assert report["apply_receipt"]["packet_hash"] == report["settlement_packet"]["packet_hash"]
    assert report["apply_receipt"]["holder_balance_before"] == 100


def test_apply_fire_settlement_cli_lp_bundle(tmp_path: Path) -> None:
    bundle_dir = _write_bundle(
        tmp_path,
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
    )
    proc = subprocess.run(
        [
            sys.executable,
            str(APPLY_CLI),
            "--bundle-dir",
            str(bundle_dir),
            "--holder-posted",
            "0",
            "--writer-posted",
            "50",
            "--holder-balance",
            "80",
            "--writer-balance",
            "200",
            "--witness-hodl-final",
            "20",
            "--witness-lpv-final",
            "7",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["report_hash"].startswith("sha256:")
    assert report["object_id"] == "lp_loss_cover_v1"
    assert report["holder_delta"] == 50
    assert report["writer_delta"] == -50
    assert report["holder_balance_after"] == 130
    assert report["writer_balance_after"] == 150
    assert report["apply_receipt"]["writer_balance_before"] == 200
    assert report["apply_receipt"]["writer_balance_after"] == 150


def test_apply_fire_settlement_cli_writes_report_and_artifact_receipt(tmp_path: Path) -> None:
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
    receipt_path = tmp_path / "apply_artifact_receipt.json"
    proc = subprocess.run(
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
            str(receipt_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    stdout_report = json.loads(proc.stdout)
    file_report = json.loads(report_path.read_text(encoding="utf-8"))
    assert stdout_report["report_hash"] == file_report["report_hash"]
    receipt_report = check_fire_settlement_apply_artifact_receipt(receipt_path)
    assert receipt_report["accepted"] is True
    assert receipt_report["report_hash"] == file_report["report_hash"]


def test_apply_fire_settlement_cli_rejects_wrong_witness_shape(tmp_path: Path) -> None:
    bundle_dir = _write_bundle(
        tmp_path,
        "fee_note_v1",
        {
            "n_notional": 10,
            "cap_index": 7,
            "source_upper": 2,
        },
    )
    proc = subprocess.run(
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
            "--witness-lpv-final",
            "7",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "missing witness inputs: witness_final" in proc.stderr


def test_apply_fire_settlement_cli_requires_report_file_for_artifact_receipt(tmp_path: Path) -> None:
    bundle_dir = _write_bundle(
        tmp_path,
        "fee_note_v1",
        {
            "n_notional": 10,
            "cap_index": 7,
            "source_upper": 2,
        },
    )
    proc = subprocess.run(
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
            "--output-artifact-receipt-file",
            str(tmp_path / "apply_artifact_receipt.json"),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "--output-artifact-receipt-file requires --output-report-file" in proc.stderr
