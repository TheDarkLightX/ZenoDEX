from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.zeno_ledger_tau_export import (
    FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1,
    TAU_EXPORT_ACCEPTANCE_RECEIPT_SCHEMA_V0,
    TAU_EXPORT_ACCEPTANCE_STATUS_ASSIGNED_V0,
    TAU_EXPORT_ADAPTER_CONTRACT_V0,
    build_tau_export_acceptance_receipt_v0,
    build_tau_export_packet_v0,
    validate_tau_export_acceptance_receipt_v0,
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


def _manifest_relative_path(manifest_path: Path, value: object) -> Path:
    path = Path(str(value))
    return path if path.is_absolute() else manifest_path.parent / path


def _executed_bundle(tmp_path: Path) -> tuple[Path, dict[str, object]]:
    bundle = _run_script(MAKE_BUNDLE_SCRIPT, "--out-dir", str(tmp_path / "bundle"))
    assert bundle.returncode == 0, bundle.stderr
    bundle_report = json.loads(bundle.stdout)
    manifest_path = Path(str(bundle_report["manifest_path"]))
    executed = _run_script(RUN_MANIFEST_SCRIPT, "--manifest", str(manifest_path), "--cwd", str(ROOT))
    assert executed.returncode == 0, executed.stderr
    return manifest_path, _load_json(manifest_path)


def test_tau_export_packet_binds_profile_checkpoint_header_and_body(tmp_path: Path) -> None:
    manifest_path, manifest = _executed_bundle(tmp_path)
    ledger = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile = _load_json(_manifest_relative_path(manifest_path, manifest["profile_path"]))
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
    manifest_path, manifest = _executed_bundle(tmp_path)
    ledger = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile_path = _manifest_relative_path(manifest_path, manifest["profile_path"])
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
        str(profile_path),
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
    manifest_path, manifest = _executed_bundle(tmp_path)
    ledger = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile_path = _manifest_relative_path(manifest_path, manifest["profile_path"])
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
        str(profile_path),
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


def test_tau_export_acceptance_receipt_binds_state_hash_assignment(tmp_path: Path) -> None:
    manifest_path, manifest = _executed_bundle(tmp_path)
    ledger = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile = _load_json(_manifest_relative_path(manifest_path, manifest["profile_path"]))
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
    state_hash = "0x" + ("55" * 32)
    state_proof = {
        "present": True,
        "state_hash": state_hash[2:],
        "proof_type": "tau.adapter.acceptance.v1",
    }
    tau_state = {"app_hash": packet["app_hash"]}

    receipt = build_tau_export_acceptance_receipt_v0(
        packet=packet,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        state_proof=state_proof,
        tau_state=tau_state,
    )

    assert receipt["schema"] == TAU_EXPORT_ACCEPTANCE_RECEIPT_SCHEMA_V0
    assert receipt["status"] == TAU_EXPORT_ACCEPTANCE_STATUS_ASSIGNED_V0
    assert receipt["packet_hash"] == packet["packet_hash"]
    assert receipt["packet_app_hash"] == packet["app_hash"]
    assert receipt["tau_state_hash"] == state_hash
    assert receipt["state_hash_key"] == f"state_proof:{state_hash[2:]}"
    assert receipt["shared_pool_frontier_signature_certificate_count"] == 0
    assert (
        receipt["shared_pool_frontier_signature_certificates_root"]
        == FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1
    )
    assert receipt["authorizes_settlement"] is False
    validate_tau_export_acceptance_receipt_v0(
        receipt=receipt,
        packet=packet,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        state_proof=state_proof,
        tau_state=tau_state,
    )


def test_tau_export_acceptance_receipt_rejects_state_and_packet_substitution(tmp_path: Path) -> None:
    manifest_path, manifest = _executed_bundle(tmp_path)
    ledger = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile = _load_json(_manifest_relative_path(manifest_path, manifest["profile_path"]))
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
    alternate_packet = build_tau_export_packet_v0(
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        tau_network_id="tau-testnet-beta",
        tau_adapter_ref="zenodex-local-app-bridge-v0",
    )
    state_proof = {
        "present": True,
        "state_hash": "66" * 32,
        "proof_type": "tau.adapter.acceptance.v1",
    }
    tau_state = {"app_hash": packet["app_hash"]}
    receipt = build_tau_export_acceptance_receipt_v0(
        packet=packet,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        state_proof=state_proof,
        tau_state=tau_state,
    )

    with pytest.raises(ValueError, match="app_hash"):
        build_tau_export_acceptance_receipt_v0(
            packet=packet,
            checkpoint=checkpoint,
            header=header,
            body=body,
            profile=profile,
            state_proof=state_proof,
            tau_state={"app_hash": "0x" + ("77" * 32)},
        )

    with pytest.raises(ValueError, match="binding mismatch"):
        validate_tau_export_acceptance_receipt_v0(
            receipt=receipt,
            packet=alternate_packet,
            checkpoint=checkpoint,
            header=header,
            body=body,
            profile=profile,
            state_proof=state_proof,
            tau_state=tau_state,
        )

    forged_receipt = dict(receipt, authorizes_settlement=True)
    with pytest.raises(ValueError, match="binding mismatch"):
        validate_tau_export_acceptance_receipt_v0(
            receipt=forged_receipt,
            packet=packet,
            checkpoint=checkpoint,
            header=header,
            body=body,
            profile=profile,
            state_proof=state_proof,
            tau_state=tau_state,
        )


def test_tau_export_acceptance_receipt_binds_frontier_signature_root(
    tmp_path: Path,
) -> None:
    manifest_path, manifest = _executed_bundle(tmp_path)
    ledger = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile = _load_json(_manifest_relative_path(manifest_path, manifest["profile_path"]))
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
    frontier_root = "aa" * 32
    state_proof = {
        "present": True,
        "state_hash": "66" * 32,
        "proof_type": "tau.adapter.acceptance.v1",
        "meta": {
            "shared_pool_frontier_signature_certificate_count": 1,
            "shared_pool_frontier_signature_certificates_root": frontier_root,
        },
    }
    tau_state = {"app_hash": packet["app_hash"]}

    receipt = build_tau_export_acceptance_receipt_v0(
        packet=packet,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        state_proof=state_proof,
        tau_state=tau_state,
    )

    assert receipt["shared_pool_frontier_signature_certificate_count"] == 1
    assert (
        receipt["shared_pool_frontier_signature_certificates_root"]
        == f"0x{frontier_root}"
    )
    validate_tau_export_acceptance_receipt_v0(
        receipt=receipt,
        packet=packet,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        state_proof=state_proof,
        tau_state=tau_state,
    )

    tampered = dict(receipt)
    tampered["shared_pool_frontier_signature_certificates_root"] = "0x" + "bb" * 32
    with pytest.raises(ValueError, match="binding mismatch"):
        validate_tau_export_acceptance_receipt_v0(
            receipt=tampered,
            packet=packet,
            checkpoint=checkpoint,
            header=header,
            body=body,
            profile=profile,
            state_proof=state_proof,
            tau_state=tau_state,
        )


def test_tau_export_acceptance_receipt_rejects_partial_frontier_signature_meta(
    tmp_path: Path,
) -> None:
    manifest_path, manifest = _executed_bundle(tmp_path)
    ledger = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile = _load_json(_manifest_relative_path(manifest_path, manifest["profile_path"]))
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
    tau_state = {"app_hash": packet["app_hash"]}

    with pytest.raises(ValueError, match="certificates_root missing"):
        build_tau_export_acceptance_receipt_v0(
            packet=packet,
            checkpoint=checkpoint,
            header=header,
            body=body,
            profile=profile,
            state_proof={
                "present": True,
                "state_hash": "66" * 32,
                "proof_type": "tau.adapter.acceptance.v1",
                "meta": {
                    "shared_pool_frontier_signature_certificate_count": 1,
                },
            },
            tau_state=tau_state,
        )

    with pytest.raises(ValueError, match="must be empty root when count is zero"):
        build_tau_export_acceptance_receipt_v0(
            packet=packet,
            checkpoint=checkpoint,
            header=header,
            body=body,
            profile=profile,
            state_proof={
                "present": True,
                "state_hash": "66" * 32,
                "proof_type": "tau.adapter.acceptance.v1",
                "meta": {
                    "shared_pool_frontier_signature_certificate_count": 0,
                    "shared_pool_frontier_signature_certificates_root": "aa" * 32,
                },
            },
            tau_state=tau_state,
        )
