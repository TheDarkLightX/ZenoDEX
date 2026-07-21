from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.tau_net_client import bls_pubkey_hex_from_privkey

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "zusd_tau_wallet.py"


def test_zusd_tau_wallet_cli_transfer_roundtrip(tmp_path: Path) -> None:
    privkey = 51
    sender = "0x" + bls_pubkey_hex_from_privkey(privkey)
    recipient = "0x" + bls_pubkey_hex_from_privkey(52)
    telemetry_path = tmp_path / "wallet_report.json"

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "transfer",
            "--sender-pubkey",
            sender,
            "--recipient-pubkey",
            recipient,
            "--sender-balance-before",
            "400",
            "--recipient-balance-before",
            "50",
            "--amount",
            "100",
            "--deadline",
            "99",
            "--last-used-nonce",
            "0",
            "--total-supply-before",
            "1000",
            "--signer-privkey",
            str(privkey),
            "--tx-sequence-number",
            "7",
            "--tx-expiration-time",
            "999",
            "--telemetry-out",
            str(telemetry_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["action"] == "transfer"
    assert report["nonce_after"] == 1
    assert report["operations"]["9"][0]["sender_pubkey"] == sender
    assert report["tau_tx_payload"]["sequence_number"] == 7
    persisted = json.loads(telemetry_path.read_text(encoding="utf-8"))
    assert persisted["asset_id"] == report["asset_id"]


def test_zusd_tau_wallet_cli_rejects_generic_canonical_mint() -> None:
    operator = "0x" + bls_pubkey_hex_from_privkey(53)
    recipient = "0x" + bls_pubkey_hex_from_privkey(54)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "mint",
            "--operator-pubkey",
            operator,
            "--recipient-pubkey",
            recipient,
            "--recipient-balance-before",
            "10",
            "--amount",
            "5",
            "--deadline",
            "99",
            "--last-used-nonce",
            "3",
            "--total-supply-before",
            "100",
            "--signer-privkey",
            "53",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "canonical_zusd_mint_requires_monetary_authority" in report["error"]


def test_zusd_tau_wallet_cli_signer_mismatch_fails() -> None:
    sender = "0x" + bls_pubkey_hex_from_privkey(55)
    recipient = "0x" + bls_pubkey_hex_from_privkey(56)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "transfer",
            "--sender-pubkey",
            sender,
            "--recipient-pubkey",
            recipient,
            "--sender-balance-before",
            "10",
            "--recipient-balance-before",
            "0",
            "--amount",
            "1",
            "--deadline",
            "99",
            "--last-used-nonce",
            "0",
            "--total-supply-before",
            "10",
            "--signer-privkey",
            "57",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "signer_privkey does not match" in report["error"]
    assert report["derived_asset_id"].startswith("0x")
