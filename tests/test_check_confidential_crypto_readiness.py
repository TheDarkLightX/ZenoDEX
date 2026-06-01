from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "check_confidential_crypto_readiness.py"


def test_check_confidential_crypto_readiness_cli_reports_blockers(tmp_path: Path) -> None:
    conf = tmp_path / "conf.json"
    attest = tmp_path / "attest.json"
    sss = tmp_path / "sss.json"
    out = tmp_path / "report.json"
    conf.write_text(
        json.dumps(
            {
                "tee_enabled": True,
                "approved_measurements_count": 1,
                "fhe_alpha_enabled": False,
            }
        ),
        encoding="utf-8",
    )
    attest.write_text(
        json.dumps(
            {
                "external_verifier_enabled": True,
                "external_verifier_configured": True,
                "external_verifier_binding_hash": "0x" + "22" * 32,
            }
        ),
        encoding="utf-8",
    )
    sss.write_text(
        json.dumps(
            {
                "sss_implemented": True,
                "encrypted_sss_backup_ready": True,
                "external_audit_ready": False,
                "live_provider_delivery_ready": False,
                "replay_recovery_ready": True,
                "replay_hostile_tests_ready": True,
                "hostile_share_tests_ready": True,
                "raw_material_absent": True,
                "server_side_reconstitution": False,
            }
        ),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--confidential-status",
            str(conf),
            "--attestation-status",
            str(attest),
            "--encrypted-sss-status",
            str(sss),
            "--out",
            str(out),
        ],
        cwd=ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["production_ready"] is False
    assert any(gap.startswith("tee_attestation:") for gap in report["readiness_gaps"])
    assert any(gap.startswith("sss_backup: external SSS audit evidence") for gap in report["readiness_gaps"])


def test_check_confidential_crypto_readiness_cli_can_fail_closed(tmp_path: Path) -> None:
    conf = tmp_path / "conf.json"
    conf.write_text(json.dumps({"tee_enabled": False, "approved_measurements_count": 0}), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--confidential-status",
            str(conf),
            "--require-production-ready",
        ],
        cwd=ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    assert proc.returncode == 1
    assert "production_ready" in proc.stdout


def test_check_confidential_crypto_readiness_cli_can_require_current_non_production_posture(tmp_path: Path) -> None:
    conf = tmp_path / "conf.json"
    out = tmp_path / "report.json"
    conf.write_text(json.dumps({"tee_enabled": False, "approved_measurements_count": 0}), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--confidential-status",
            str(conf),
            "--require-non-production-ready",
            "--out",
            str(out),
        ],
        cwd=ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["production_ready"] is False
    assert report["host_independent_ready"] is False
