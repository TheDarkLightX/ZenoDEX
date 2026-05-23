from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.tau_net_client import bls_pubkey_hex_from_privkey

REPO_ROOT = Path(__file__).resolve().parents[2]
COMPILE_CLI = REPO_ROOT / "tools" / "autotrader_policy_compile.py"
SIGN_CLI = REPO_ROOT / "tools" / "autotrader_policy_sign.py"
VERIFY_CLI = REPO_ROOT / "tools" / "autotrader_policy_verify.py"


def _compile_unsigned(tmp_path: Path, *, privkey: int) -> tuple[Path, Path, Path]:
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    proc = subprocess.run(
        [
            sys.executable,
            str(COMPILE_CLI),
            "--text",
            "dca 100 zUSD into BTC every 4 epochs until epoch 20 max slippage 25 bps "
            "per window max 300 lifetime max 900 backend tau max live orders 2",
            "--owner-pubkey",
            owner_pubkey,
            "--krr-backend",
            "off",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    source_artifact_path = tmp_path / "source_artifact.json"
    source_artifact_path.write_text(json.dumps(report["source_artifact"], indent=2, sort_keys=True), encoding="utf-8")
    artifact_path = tmp_path / "policy_artifact.json"
    artifact_path.write_text(json.dumps(report["policy_artifact"], indent=2, sort_keys=True), encoding="utf-8")
    bundle_path = tmp_path / "tau_policy_bundle.json"
    bundle_path.write_text(json.dumps(report["tau_policy_bundle"], indent=2, sort_keys=True), encoding="utf-8")
    return source_artifact_path, artifact_path, bundle_path


def test_autotrader_policy_sign_and_verify_cli_roundtrip(tmp_path: Path) -> None:
    source_artifact_path, artifact_path, bundle_path = _compile_unsigned(tmp_path, privkey=71)

    sign_proc = subprocess.run(
        [
            sys.executable,
            str(SIGN_CLI),
            "--policy-artifact-file",
            str(artifact_path),
            "--signer-privkey",
            "71",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert sign_proc.returncode == 0, sign_proc.stderr
    signed = json.loads(sign_proc.stdout)
    signed_artifact_path = tmp_path / "signed_policy_artifact.json"
    signed_artifact_path.write_text(
        json.dumps(signed["policy_artifact"], indent=2, sort_keys=True),
        encoding="utf-8",
    )

    verify_proc = subprocess.run(
        [
            sys.executable,
            str(VERIFY_CLI),
            "--source-artifact-file",
            str(source_artifact_path),
            "--policy-artifact-file",
            str(signed_artifact_path),
            "--tau-policy-bundle-file",
            str(bundle_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify_proc.returncode == 0, verify_proc.stderr
    report = json.loads(verify_proc.stdout)
    assert report["ok"] is True
    assert report["signature_ok"] is True
    assert report["source_artifact_hash_ok"] is True
    assert report["tau_policy_bundle_contract"]["ok"] is True
    assert report["policy_artifact_contract"]["ok"] is True
    assert report["compilation_witness_contract"]["ok"] is True
    assert report["compilation_witness_receipt_ok"] is True


def test_autotrader_policy_verify_cli_rejects_unsigned_artifact(tmp_path: Path) -> None:
    source_artifact_path, artifact_path, bundle_path = _compile_unsigned(tmp_path, privkey=72)
    verify_proc = subprocess.run(
        [
            sys.executable,
            str(VERIFY_CLI),
            "--source-artifact-file",
            str(source_artifact_path),
            "--policy-artifact-file",
            str(artifact_path),
            "--tau-policy-bundle-file",
            str(bundle_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify_proc.returncode == 1
    report = json.loads(verify_proc.stderr)
    assert report["ok"] is False
    assert report["signature_ok"] is False
