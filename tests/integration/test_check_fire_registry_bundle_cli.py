from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_bundle.py"
CHECK_CLI = REPO_ROOT / "tools" / "check_fire_registry_bundle.py"


def test_check_fire_registry_bundle_cli_roundtrip(tmp_path: Path) -> None:
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
    assert payload["schema"] == "zenodex/fire-registry-bundle-check-report/v1"
    assert payload["ok"] is True
    assert payload["object_name"] == "BurnBoostCall"
    assert payload["bundle_hash"] == build_report["bundle_hash"]
    assert payload["object_hash"] == build_report["object_hash"]
    assert payload["instance_hash"] == build_report["instance_hash"]
    assert payload["lock_hash"] == build_report["lock_hash"]
    assert payload["object_card_noncanonical"] is True
    assert "Instance gate claim evidence:" in payload["object_card_text"]
    assert "AuthorizationOK: implemented" in payload["object_card_text"]
    assert payload["certificate_instance_gate_claims"] == build_report["certificate_instance_gate_claims"]
    assert payload["instance_gates"]["ok"] is True
    assert payload["instance_gates"]["authorization_ok"] is True


def test_check_fire_registry_bundle_cli_fails_on_object_card_tamper(tmp_path: Path) -> None:
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
    (bundle_dir / "object_card.txt").write_text("tampered\n", encoding="utf-8")

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
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert check.returncode == 1
    payload = json.loads(check.stderr)
    assert payload["schema"] == "zenodex/fire-registry-bundle-check-report/v1"
    assert payload["ok"] is False
    assert payload["error"] == "object_card_sha_mismatch"
