from __future__ import annotations

import json
import importlib.util
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
BUILDER = ROOT / "tools" / "build_zenodex_oracle_release.py"


def test_build_zenodex_oracle_release_bundle_includes_cli_and_branding(tmp_path: Path) -> None:
    out_dir = tmp_path / "dist"
    proc = subprocess.run(
        [
            sys.executable,
            str(BUILDER),
            "--json",
            "--out-dir",
            str(out_dir),
            "--bundle-name",
            "oracle-test-bundle",
            "--zip",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )

    assert proc.returncode == 0, proc.stderr
    result = json.loads(proc.stdout)
    bundle_dir = Path(result["bundle_dir"])
    manifest_path = Path(result["manifest"])
    archive_path = Path(result["archive"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    by_path = {entry["path"]: entry for entry in manifest["files"]}

    assert result["ok"] is True
    assert result["native_binary"] is None
    assert result["native_binary_sha256"] is None
    assert manifest["schema"] == "zenodex.oracle.release_bundle.v1"
    assert manifest["build_target"] == "python-local-bundle"
    assert manifest["entrypoint"] == "zenodex-oracle"
    assert manifest["native_binary"] is None
    assert manifest["production_authority"] is False
    assert "native_binary" in manifest["not_claimed"]
    assert (bundle_dir / "zenodex-oracle").is_file()
    assert os.access(bundle_dir / "zenodex-oracle", os.X_OK)
    assert (bundle_dir / manifest["official_icon"]).is_file()
    assert archive_path.is_file()
    assert result["archive_sha256"].startswith("sha256:")
    assert by_path["zenodex-oracle"]["executable"] is True
    assert by_path["tools/zenodex_oracle.py"]["sha256"].startswith("sha256:")
    assert by_path["assets/branding/zeno-oracle/zeno_oracle_icon_512.png"]["sha256"].startswith("sha256:")

    version = subprocess.run(
        [str(bundle_dir / "zenodex-oracle"), "--json", "version"],
        cwd=bundle_dir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    version_data = json.loads(version.stdout)

    assert version.returncode == 0, version.stderr
    assert version_data["name"] == "zenodex-oracle"
    assert version_data["build_target"] == "python-local"
    assert version_data["asset_manifest"]["zeno_oracle_icon_512"].startswith("sha256:")


@pytest.mark.skipif(
    shutil.which("pyinstaller") is None and importlib.util.find_spec("PyInstaller") is None,
    reason="PyInstaller is optional for the native ZenoOracle bundle",
)
def test_build_zenodex_oracle_native_release_bundle_reports_native_target(tmp_path: Path) -> None:
    out_dir = tmp_path / "dist"
    proc = subprocess.run(
        [
            sys.executable,
            str(BUILDER),
            "--json",
            "--out-dir",
            str(out_dir),
            "--bundle-name",
            "oracle-native-test-bundle",
            "--native-binary",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )

    assert proc.returncode == 0, proc.stderr
    result = json.loads(proc.stdout)
    bundle_dir = Path(result["bundle_dir"])
    manifest = json.loads(Path(result["manifest"]).read_text(encoding="utf-8"))
    native_binary = bundle_dir / manifest["native_binary"]

    assert result["ok"] is True
    assert result["native_binary"] == str(native_binary)
    assert result["native_binary_sha256"].startswith("sha256:")
    assert manifest["build_target"] == "native-binary-bundle"
    assert manifest["entrypoint"] == "bin/zenodex-oracle"
    assert manifest["native_binary"] == "bin/zenodex-oracle"
    assert "native_binary" not in manifest["not_claimed"]
    assert native_binary.is_file()
    assert os.access(native_binary, os.X_OK)

    version = subprocess.run(
        [str(native_binary), "--json", "version"],
        cwd=bundle_dir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    version_data = json.loads(version.stdout)

    assert version.returncode == 0, version.stderr
    assert version_data["name"] == "zenodex-oracle"
    assert version_data["build_target"] == "native-binary"
    assert version_data["asset_manifest"]["zeno_oracle_icon_512"].startswith("sha256:")
