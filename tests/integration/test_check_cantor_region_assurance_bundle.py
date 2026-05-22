from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.cantor_region_assurance_bundle import build_default_cantor_region_assurance_bundle
from src.integration.region_ba_backends import resolve_region_ba_backend

def test_check_cantor_region_assurance_bundle_cli_accepts_default_bundle(tmp_path: Path) -> None:
    bundle_path = tmp_path / "bundle.json"
    bundle_path.write_text(
        json.dumps(build_default_cantor_region_assurance_bundle().to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    subprocess.run(
        [
            sys.executable,
            "tools/check_cantor_region_assurance_bundle.py",
            str(bundle_path),
            "--require-current-default",
        ],
        check=True,
    )

def test_check_cantor_region_assurance_bundle_cli_accepts_bdd_backend_bundle(tmp_path: Path) -> None:
    bundle_path = tmp_path / "bdd_bundle.json"
    bundle_path.write_text(
        json.dumps(
            build_default_cantor_region_assurance_bundle(ba=resolve_region_ba_backend("bdd")).to_dict(),
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    subprocess.run(
        [
            sys.executable,
            "tools/check_cantor_region_assurance_bundle.py",
            str(bundle_path),
            "--require-current-backend",
            "bdd",
        ],
        check=True,
    )

def test_check_cantor_region_assurance_bundle_cli_rejects_tampered_bundle(tmp_path: Path) -> None:
    bundle_path = tmp_path / "bundle.json"
    payload = build_default_cantor_region_assurance_bundle().to_dict()
    payload["surfaces"][1]["report"]["partition_total"] = False
    bundle_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_cantor_region_assurance_bundle.py",
            str(bundle_path),
        ],
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "partition failed" in proc.stderr

def test_check_cantor_region_assurance_bundle_cli_rejects_backend_mismatch(tmp_path: Path) -> None:
    bundle_path = tmp_path / "bundle.json"
    payload = build_default_cantor_region_assurance_bundle().to_dict()
    payload["product_receipts"][0]["product_name"] = "tampered"
    bundle_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_cantor_region_assurance_bundle.py",
            str(bundle_path),
            "--require-current-backend",
            "prefix",
        ],
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "bundle payload differs from current backend construction" in proc.stderr
