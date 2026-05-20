from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BUNDLE_CLI = REPO_ROOT / "tools" / "zenograph_autotrader_ranking_review_bundle.py"
VERIFY_CLI = REPO_ROOT / "tools" / "zenograph_autotrader_ranking_review_bundle_verify.py"


def test_zenograph_autotrader_ranking_review_bundle_verify_cli_roundtrip(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "bundle"
    build = subprocess.run(
        [
            sys.executable,
            str(BUNDLE_CLI),
            "--out-dir",
            str(out_dir),
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    manifest_path = Path(json.loads(build.stdout)["manifest_path"])

    verify = subprocess.run(
        [
            sys.executable,
            str(VERIFY_CLI),
            "--manifest-file",
            str(manifest_path),
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    payload = json.loads(verify.stdout)
    assert payload["ok"] is True
    assert payload["missing_artifacts"] == []
    assert payload["sha256_mismatches"] == []


def test_zenograph_autotrader_ranking_review_bundle_verify_cli_fails_on_tamper(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "bundle"
    build = subprocess.run(
        [
            sys.executable,
            str(BUNDLE_CLI),
            "--out-dir",
            str(out_dir),
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    manifest_path = Path(json.loads(build.stdout)["manifest_path"])
    (out_dir / "ranking_review.md").write_text("tampered\n", encoding="utf-8")

    verify = subprocess.run(
        [
            sys.executable,
            str(VERIFY_CLI),
            "--manifest-file",
            str(manifest_path),
        ],
        check=False,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    payload = json.loads(verify.stdout)
    assert verify.returncode == 1
    assert payload["ok"] is False
    assert payload["sha256_mismatches"] == ["summary"]
