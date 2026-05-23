from __future__ import annotations

import json
import subprocess
import sys
import tarfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BUILDER = ROOT / "tools" / "build_operator_release_bundle.py"


def test_build_operator_release_bundle_build_and_verify_subcommands(tmp_path: Path) -> None:
    build = subprocess.run(
        [
            sys.executable,
            str(BUILDER),
            "build",
            "--version",
            "test.1",
            "--out-dir",
            str(tmp_path),
            "--json",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )

    assert build.returncode == 0, build.stderr
    payload = json.loads(build.stdout)
    archive = Path(payload["archive"])
    manifest = Path(payload["manifest"])

    assert payload["ok"] is True
    assert archive.name == "zenodex-operator-test.1.tar.gz"
    assert archive.is_file()
    assert manifest.name == "zenodex-operator-test.1.tar.gz.manifest.json"
    assert manifest.is_file()
    assert payload["archive_sha256"].startswith("sha256:")

    with tarfile.open(archive, "r:gz") as handle:
        names = set(handle.getnames())

    assert "bin/zenoctl" in names
    assert "operator_release_manifest.json" in names

    verify = subprocess.run(
        [
            sys.executable,
            str(BUILDER),
            "verify",
            "--manifest",
            str(manifest),
            "--json",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )

    assert verify.returncode == 0, verify.stderr
    verify_payload = json.loads(verify.stdout)
    assert verify_payload["ok"] is True
    assert verify_payload["status"] == "verify"


def test_build_operator_release_bundle_rejects_unsafe_version(tmp_path: Path) -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(BUILDER),
            "build",
            "--version",
            "../bad",
            "--out-dir",
            str(tmp_path),
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )

    assert proc.returncode == 2
    assert "version must be" in proc.stderr
