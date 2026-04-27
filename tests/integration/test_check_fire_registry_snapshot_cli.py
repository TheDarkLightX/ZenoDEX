from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SNAPSHOT_BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_snapshot.py"
SNAPSHOT_CHECK_CLI = REPO_ROOT / "tools" / "check_fire_registry_snapshot.py"


def test_check_fire_registry_snapshot_cli_roundtrip(tmp_path: Path) -> None:
    out_dir = tmp_path / "snapshot"
    build = subprocess.run(
        [
            sys.executable,
            str(SNAPSHOT_BUILD_CLI),
            "--output-dir",
            str(out_dir),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert build.returncode == 0, build.stderr
    build_payload = json.loads(build.stdout)

    check = subprocess.run(
        [
            sys.executable,
            str(SNAPSHOT_CHECK_CLI),
            "--metadata-file",
            str(out_dir / "release_metadata.json"),
            "--expected-snapshot-name",
            build_payload["snapshot_name"],
            "--expected-metadata-file-sha256",
            build_payload["release_metadata_file_sha256"],
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check.returncode == 0, check.stderr
    check_payload = json.loads(check.stdout)
    assert check_payload["schema"] == "zenodex/fire-registry-snapshot-check-report/v1"
    assert check_payload["ok"] is True
    assert check_payload["snapshot_name"] == build_payload["snapshot_name"]
    assert check_payload["contract_count"] == build_payload["contract_count"]
    assert check_payload["instance_gate_summary"] == build_payload["instance_gate_summary"]
    assert check_payload["certificate_instance_gate_summary"] == build_payload["certificate_instance_gate_summary"]
    assert [row["name"] for row in check_payload["contracts"]] == [row["name"] for row in build_payload["contracts"]]


def test_check_fire_registry_snapshot_cli_rejects_tampered_metadata(tmp_path: Path) -> None:
    out_dir = tmp_path / "snapshot"
    build = subprocess.run(
        [
            sys.executable,
            str(SNAPSHOT_BUILD_CLI),
            "--output-dir",
            str(out_dir),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert build.returncode == 0, build.stderr

    metadata_path = out_dir / "release_metadata.json"
    payload = json.loads(metadata_path.read_text(encoding="utf-8"))
    payload["snapshot_name"] = "tampered"
    metadata_path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    check = subprocess.run(
        [
            sys.executable,
            str(SNAPSHOT_CHECK_CLI),
            "--metadata-file",
            str(metadata_path),
            "--expected-snapshot-name",
            "devnet_v1",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check.returncode == 1
    error_payload = json.loads(check.stderr)
    assert error_payload["schema"] == "zenodex/fire-registry-snapshot-check-report/v1"
    assert error_payload["ok"] is False
    assert error_payload["error"] == "expected_snapshot_name_mismatch"
