from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.zeno_ledger_tau_export import (
    TAU_EXPORT_ADAPTER_CONTRACT_V0,
    build_tau_export_packet_v0,
    validate_tau_export_packet_v0,
)


ROOT = Path(__file__).resolve().parents[2]
MAKE_BUNDLE_SCRIPT = ROOT / "tools" / "zeno_ledger_make_testnet_bundle.py"
RUN_MANIFEST_SCRIPT = ROOT / "tools" / "zeno_ledger_run_manifest.py"
EXPORT_SCRIPT = ROOT / "tools" / "zeno_ledger_export_tau_packet.py"


def _run_script(script: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(script), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _load_json(path: Path) -> dict[str, object]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(obj, dict)
    return obj


def _executed_bundle(tmp_path: Path) -> dict[str, object]:
    bundle = _run_script(MAKE_BUNDLE_SCRIPT, "--out-dir", str(tmp_path / "bundle"))
    assert bundle.returncode == 0, bundle.stderr
    bundle_report = json.loads(bundle.stdout)
    manifest_path = str(bundle_report["manifest_path"])
    executed = _run_script(RUN_MANIFEST_SCRIPT, "--manifest", manifest_path, "--cwd", str(ROOT))
    assert executed.returncode == 0, executed.stderr
    return _load_json(Path(manifest_path))


def test_tau_export_packet_binds_profile_checkpoint_header_and_body(tmp_path: Path) -> None:
    manifest = _executed_bundle(tmp_path)
    ledger = Path(str(manifest["ledger_out_dir"]))
    profile = _load_json(Path(str(manifest["profile_path"])))
    checkpoint = _load_json(ledger / "checkpoints" / "5.json")
    header = _load_json(ledger / "headers" / "5.json")
    body = _load_json(ledger / "bodies" / "5.json")

    packet = build_tau_export_packet_v0(
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        tau_network_id="tau-testnet-alpha",
        tau_adapter_ref="zenodex-local-app-bridge-v0",
    )

    assert packet["adapter_contract"] == TAU_EXPORT_ADAPTER_CONTRACT_V0
    assert packet["deployment_mode"] == "zeno_sovereign_testnet"
    assert packet["chain_id"] == checkpoint["chain_id"]
    assert packet["height"] == 5
    assert packet["header_hash"] == checkpoint["header_hash"]
    assert packet["app_hash"] == checkpoint["app_hash"]
    assert packet["tau_state_proof_hint"]["committed_app_hash"] == checkpoint["app_hash"]
    assert packet["tau_state_proof_hint"]["proof_type"] == "zenoledger.checkpoint.v0"
    validate_tau_export_packet_v0(
        packet=packet,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
    )

    tampered = dict(packet)
    tampered["height"] = 4
    with pytest.raises(ValueError, match="binding mismatch"):
        validate_tau_export_packet_v0(
            packet=tampered,
            checkpoint=checkpoint,
            header=header,
            body=body,
            profile=profile,
        )


def test_tau_export_packet_cli_writes_verified_packet(tmp_path: Path) -> None:
    manifest = _executed_bundle(tmp_path)
    ledger = Path(str(manifest["ledger_out_dir"]))
    out_path = tmp_path / "tau_export_packet.json"

    proc = _run_script(
        EXPORT_SCRIPT,
        "--checkpoint",
        str(ledger / "checkpoints" / "5.json"),
        "--header",
        str(ledger / "headers" / "5.json"),
        "--body",
        str(ledger / "bodies" / "5.json"),
        "--profile",
        str(manifest["profile_path"]),
        "--tau-network-id",
        "tau-testnet-alpha",
        "--tau-adapter-ref",
        "zenodex-local-app-bridge-v0",
        "--out",
        str(out_path),
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["packet_path"] == str(out_path)
    packet = _load_json(out_path)
    assert packet["packet_hash"] == report["packet"]["packet_hash"]


def test_tau_export_packet_cli_rejects_body_tampering(tmp_path: Path) -> None:
    manifest = _executed_bundle(tmp_path)
    ledger = Path(str(manifest["ledger_out_dir"]))
    tampered_body_path = tmp_path / "tampered_body.json"
    body = _load_json(ledger / "bodies" / "5.json")
    body["transactions"] = [{"bad": "tx"}]
    tampered_body_path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    proc = _run_script(
        EXPORT_SCRIPT,
        "--checkpoint",
        str(ledger / "checkpoints" / "5.json"),
        "--header",
        str(ledger / "headers" / "5.json"),
        "--body",
        str(tampered_body_path),
        "--profile",
        str(manifest["profile_path"]),
        "--tau-network-id",
        "tau-testnet-alpha",
        "--tau-adapter-ref",
        "zenodex-local-app-bridge-v0",
    )

    assert proc.returncode == 1
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert "header" in report["errors"][0]
    assert "mismatch" in report["errors"][0]
