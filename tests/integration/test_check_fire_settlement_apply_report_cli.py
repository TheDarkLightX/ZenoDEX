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
CHECK_CLI = REPO_ROOT / "tools" / "check_fire_settlement_apply_report.py"


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


def test_check_fire_settlement_apply_report_cli_accepts_generated_report(tmp_path: Path) -> None:
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
    report_file = tmp_path / "apply_report.json"
    report_file.write_text(apply_proc.stdout, encoding="utf-8")

    check_proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--report-file",
            str(report_file),
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
    report = json.loads(check_proc.stdout)
    assert report["accepted"] is True
    assert report["error"] is None
    assert report["report_hash"].startswith("sha256:")
    assert report["witness_hash"] == expected_witness_hash

    bad_check_proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--report-file",
            str(report_file),
            "--expected-witness-hash",
            fire_witness_binding_hash({"witness_final": 8}),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert bad_check_proc.returncode == 1
    bad_report = json.loads(bad_check_proc.stdout)
    assert bad_report["accepted"] is False
    assert bad_report["error"] == "settlement_packet_receipt_witness_hash_mismatch"


def test_check_fire_settlement_apply_report_cli_rejects_tampered_report(tmp_path: Path) -> None:
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
    payload = json.loads(apply_proc.stdout)
    payload["writer_balance_after"] = 71
    report_file = tmp_path / "tampered_apply_report.json"
    report_file.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    check_proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--report-file",
            str(report_file),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check_proc.returncode == 1
    report = json.loads(check_proc.stdout)
    assert report["accepted"] is False
    assert report["error"] == "report_hash_mismatch"
