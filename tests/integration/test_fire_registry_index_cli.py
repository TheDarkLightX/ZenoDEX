from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
BUNDLE_BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_bundle.py"
INDEX_BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_index.py"
INDEX_CHECK_CLI = REPO_ROOT / "tools" / "check_fire_registry_index.py"


def _build_bundle(tmp_path: Path, object_id: str, extra_args: list[str]) -> Path:
    bundle_dir = tmp_path / object_id
    proc = subprocess.run(
        [
            sys.executable,
            str(BUNDLE_BUILD_CLI),
            object_id,
            "--bundle-dir",
            str(bundle_dir),
            *extra_args,
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    return bundle_dir


def test_fire_registry_index_cli_roundtrip(tmp_path: Path) -> None:
    burn_dir = _build_bundle(
        tmp_path,
        "burn_boost_call_v1",
        ["--n-notional", "10", "--strike-index", "4", "--cap-index", "3", "--source-upper", "9"],
    )
    fee_dir = _build_bundle(
        tmp_path,
        "fee_note_v1",
        ["--n-notional", "11", "--cap-index", "7", "--source-upper", "12"],
    )
    index_path = tmp_path / "fire_registry_index.json"

    build = subprocess.run(
        [
            sys.executable,
            str(INDEX_BUILD_CLI),
            "--bundle-dir",
            str(fee_dir),
            "--bundle-dir",
            str(burn_dir),
            "--output",
            str(index_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert build.returncode == 0, build.stderr
    build_payload = json.loads(build.stdout)
    assert build_payload["schema"] == "zenodex/fire-registry-index-build-report/v1"
    assert build_payload["ok"] is True
    assert build_payload["entry_count"] == 2
    assert build_payload["contract_count"] == 2
    assert build_payload["instance_gate_summary"] == {
        "entry_count": 2,
        "all_ok": True,
        "param_ok_count": 2,
        "authorization_ok_count": 2,
        "nonce_ok_count": 2,
        "maturity_ok_count": 2,
        "window_ok_count": 2,
    }
    assert build_payload["certificate_instance_gate_summary"] == {
        "entry_count": 2,
        "param_ok": "implemented",
        "authorization_ok": "implemented",
        "nonce_ok": "implemented",
        "maturity_ok": "implemented",
        "window_ok": "implemented",
    }
    assert [row["name"] for row in build_payload["contracts"]] == ["burn_contract", "fee_contract"]
    assert all("object_hash" in row and "instance_hash" in row and "lock_hash" in row for row in build_payload["objects"])
    assert all(row["instance_gates"]["ok"] is True for row in build_payload["objects"])
    assert all(
        row["certificate_instance_gate_claims"]
        == {
            "param_ok": "implemented",
            "authorization_ok": "implemented",
            "nonce_ok": "implemented",
            "maturity_ok": "implemented",
            "window_ok": "implemented",
        }
        for row in build_payload["objects"]
    )

    check = subprocess.run(
        [
            sys.executable,
            str(INDEX_CHECK_CLI),
            "--index-file",
            str(index_path),
            "--expected-index-hash",
            build_payload["index_hash"],
            "--expected-index-file-sha256",
            build_payload["index_file_sha256"],
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check.returncode == 0, check.stderr
    check_payload = json.loads(check.stdout)
    assert check_payload["schema"] == "zenodex/fire-registry-index-check-report/v1"
    assert check_payload["ok"] is True
    assert [row["object_name"] for row in check_payload["objects"]] == ["BurnBoostCall", "FeeNote"]
    assert all("object_hash" in row and "instance_hash" in row and "lock_hash" in row for row in check_payload["objects"])
    assert check_payload["instance_gate_summary"] == build_payload["instance_gate_summary"]
    assert check_payload["certificate_instance_gate_summary"] == build_payload["certificate_instance_gate_summary"]
    assert all(row["instance_gates"]["ok"] is True for row in check_payload["objects"])
    assert all(
        row["certificate_instance_gate_claims"] == build_payload["objects"][idx]["certificate_instance_gate_claims"]
        for idx, row in enumerate(check_payload["objects"])
    )
    assert check_payload["contract_count"] == 2
    assert [row["name"] for row in check_payload["contracts"]] == ["burn_contract", "fee_contract"]
    assert check_payload["signature_present"] is False


def test_fire_registry_index_cli_signed_roundtrip(tmp_path: Path) -> None:
    burn_dir = _build_bundle(
        tmp_path,
        "burn_boost_call_v1",
        ["--n-notional", "10", "--strike-index", "4", "--cap-index", "3", "--source-upper", "9"],
    )
    fee_dir = _build_bundle(
        tmp_path,
        "fee_note_v1",
        ["--n-notional", "11", "--cap-index", "7", "--source-upper", "12"],
    )
    index_path = tmp_path / "fire_registry_index.signed.json"

    build = subprocess.run(
        [
            sys.executable,
            str(INDEX_BUILD_CLI),
            "--bundle-dir",
            str(fee_dir),
            "--bundle-dir",
            str(burn_dir),
            "--output",
            str(index_path),
            "--signer-privkey",
            "73",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert build.returncode == 0, build.stderr
    build_payload = json.loads(build.stdout)
    assert build_payload["signature_present"] is True
    assert build_payload["signer_pubkey"].startswith("0x")

    check = subprocess.run(
        [
            sys.executable,
            str(INDEX_CHECK_CLI),
            "--index-file",
            str(index_path),
            "--expected-index-hash",
            build_payload["index_hash"],
            "--expected-index-file-sha256",
            build_payload["index_file_sha256"],
            "--expected-signer-pubkey",
            build_payload["signer_pubkey"],
            "--require-signature",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check.returncode == 0, check.stderr
    check_payload = json.loads(check.stdout)
    assert check_payload["ok"] is True
    assert check_payload["signature_present"] is True
    assert check_payload["signer_pubkey"] == build_payload["signer_pubkey"]
    assert check_payload["instance_gate_summary"] == build_payload["instance_gate_summary"]
    assert check_payload["certificate_instance_gate_summary"] == build_payload["certificate_instance_gate_summary"]
    assert check_payload["contract_count"] == 2
    assert [row["name"] for row in check_payload["contracts"]] == ["burn_contract", "fee_contract"]


def test_fire_registry_index_cli_fails_on_bundle_tamper(tmp_path: Path) -> None:
    burn_dir = _build_bundle(
        tmp_path,
        "burn_boost_call_v1",
        ["--n-notional", "10", "--strike-index", "4", "--cap-index", "3", "--source-upper", "9"],
    )
    fee_dir = _build_bundle(
        tmp_path,
        "fee_note_v1",
        ["--n-notional", "11", "--cap-index", "7", "--source-upper", "12"],
    )
    index_path = tmp_path / "fire_registry_index.json"

    build = subprocess.run(
        [
            sys.executable,
            str(INDEX_BUILD_CLI),
            "--bundle-dir",
            str(burn_dir),
            "--bundle-dir",
            str(fee_dir),
            "--output",
            str(index_path),
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )
    build_payload = json.loads(build.stdout)

    (fee_dir / "object_card.txt").write_text("tampered\n", encoding="utf-8")

    check = subprocess.run(
        [
            sys.executable,
            str(INDEX_CHECK_CLI),
            "--index-file",
            str(index_path),
            "--expected-index-hash",
            build_payload["index_hash"],
            "--expected-index-file-sha256",
            build_payload["index_file_sha256"],
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check.returncode == 1
    payload = json.loads(check.stderr)
    assert payload["schema"] == "zenodex/fire-registry-index-check-report/v1"
    assert payload["ok"] is False
    assert "object_card_sha_mismatch" in payload["error"]


def test_fire_registry_index_cli_require_signature_rejects_unsigned_index(tmp_path: Path) -> None:
    burn_dir = _build_bundle(
        tmp_path,
        "burn_boost_call_v1",
        ["--n-notional", "10", "--strike-index", "4", "--cap-index", "3", "--source-upper", "9"],
    )
    fee_dir = _build_bundle(
        tmp_path,
        "fee_note_v1",
        ["--n-notional", "11", "--cap-index", "7", "--source-upper", "12"],
    )
    index_path = tmp_path / "fire_registry_index.json"

    build = subprocess.run(
        [
            sys.executable,
            str(INDEX_BUILD_CLI),
            "--bundle-dir",
            str(burn_dir),
            "--bundle-dir",
            str(fee_dir),
            "--output",
            str(index_path),
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )
    build_payload = json.loads(build.stdout)
    wrong_signer_pubkey = "0x" + ("00" * 48)

    check = subprocess.run(
        [
            sys.executable,
            str(INDEX_CHECK_CLI),
            "--index-file",
            str(index_path),
            "--expected-index-hash",
            build_payload["index_hash"],
            "--expected-index-file-sha256",
            build_payload["index_file_sha256"],
            "--require-signature",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check.returncode == 1
    payload = json.loads(check.stderr)
    assert payload["schema"] == "zenodex/fire-registry-index-check-report/v1"
    assert payload["ok"] is False
    assert payload["error"] == "index_signature_missing"


def test_fire_registry_index_cli_rejects_unexpected_signer_pubkey(tmp_path: Path) -> None:
    burn_dir = _build_bundle(
        tmp_path,
        "burn_boost_call_v1",
        ["--n-notional", "10", "--strike-index", "4", "--cap-index", "3", "--source-upper", "9"],
    )
    fee_dir = _build_bundle(
        tmp_path,
        "fee_note_v1",
        ["--n-notional", "11", "--cap-index", "7", "--source-upper", "12"],
    )
    index_path = tmp_path / "fire_registry_index.signed.json"

    build = subprocess.run(
        [
            sys.executable,
            str(INDEX_BUILD_CLI),
            "--bundle-dir",
            str(burn_dir),
            "--bundle-dir",
            str(fee_dir),
            "--output",
            str(index_path),
            "--signer-privkey",
            "73",
        ],
        cwd=str(REPO_ROOT),
        check=True,
        capture_output=True,
        text=True,
    )
    build_payload = json.loads(build.stdout)
    wrong_signer_pubkey = "0x" + ("00" * 48)

    check = subprocess.run(
        [
            sys.executable,
            str(INDEX_CHECK_CLI),
            "--index-file",
            str(index_path),
            "--expected-index-hash",
            build_payload["index_hash"],
            "--expected-index-file-sha256",
            build_payload["index_file_sha256"],
            "--expected-signer-pubkey",
            wrong_signer_pubkey,
            "--require-signature",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check.returncode == 1
    payload = json.loads(check.stderr)
    assert payload["schema"] == "zenodex/fire-registry-index-check-report/v1"
    assert payload["ok"] is False
    assert payload["error"] == "expected_signer_pubkey_mismatch"
