from __future__ import annotations

import json
import threading
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import pytest

from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from tools.zeno_ledger_node import (
    _public_network_config_to_join_config_v0,
    attach_public_network_config_quorum_v0,
    build_public_network_config_v0,
    doctor_public_node_v0,
)


TEST_BLS_PRIVATE_KEY_A = "0x" + "01" * 32
TEST_BLS_PRIVATE_KEY_B = "0x" + "02" * 32


class _QuietStaticHandler(SimpleHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        return


def _start_static_server(root: Path) -> tuple[ThreadingHTTPServer, str]:
    handler = partial(_QuietStaticHandler, directory=str(root))
    server = ThreadingHTTPServer(("127.0.0.1", 0), handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    host, port = server.server_address
    return server, f"http://{host}:{port}"


def _registry() -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="public-network-config-quorum-testnet-v0",
        payload_kind="public_network_config",
        threshold=2,
        signers=[
            {
                "signer_id": "operator-a",
                "key_id": "bls-a",
                "public_key": bls_public_key_hex_from_private_key_v0(TEST_BLS_PRIVATE_KEY_A),
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "operator-b",
                "key_id": "bls-b",
                "public_key": bls_public_key_hex_from_private_key_v0(TEST_BLS_PRIVATE_KEY_B),
                "weight": 1,
                "status": "active",
            },
        ],
    )


def _envelopes(network_config_hash: str) -> list[dict[str, object]]:
    return [
        build_bls_signed_artifact_envelope_v0(
            payload_kind="public_network_config",
            payload_hash=network_config_hash,
            signer_id="operator-a",
            key_id="bls-a",
            private_key_hex=TEST_BLS_PRIVATE_KEY_A,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind="public_network_config",
            payload_hash=network_config_hash,
            signer_id="operator-b",
            key_id="bls-b",
            private_key_hex=TEST_BLS_PRIVATE_KEY_B,
        ),
    ]


def _bundle(root: Path) -> None:
    (root / "core_features").mkdir(parents=True)
    (root / "public_testnet_manifest.json").write_text(
        json.dumps(
            {
                "schema": "zenodex.zeno_ledger.public_testnet_bundle.v0",
                "network_id": "zeno-ledger-config-quorum-testnet-0",
                "chain_id": "zeno-ledger-config-quorum-testnet-0",
                "token_symbol": "tZENO",
                "core_suite_path": "core_features/feature_suite.json",
                "test_token_catalog": [],
                "testnet_faucet_posture": {"supports_fixture_mint": True},
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (root / "core_features" / "feature_suite.json").write_text(
        json.dumps(
            {
                "schema": "zenodex.zeno_ledger.feature_suite.v0",
                "feature_suite_hash": "0x" + "11" * 32,
                "feature_count": 0,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


def test_doctor_accepts_signed_public_network_config_quorum(tmp_path: Path) -> None:
    bundle_root = tmp_path / "bundle"
    _bundle(bundle_root)
    server, mirror_url = _start_static_server(bundle_root)
    try:
        config = build_public_network_config_v0(
            bundle_root=bundle_root,
            mirror_base_url=mirror_url,
            writer_urls=["http://127.0.0.1:8799"],
            peer_urls=["http://127.0.0.1:8800"],
            poll_seconds=5,
            node_port=8788,
        )
        registry = _registry()
        signed_config = attach_public_network_config_quorum_v0(
            network_config=config,
            registry=registry,
            envelopes=_envelopes(str(config["network_config_hash"])),
        )
        (bundle_root / "public_network_config.json").write_text(
            json.dumps(signed_config, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        report = doctor_public_node_v0(
            config_url=f"{mirror_url}/public_network_config.json",
            expected_network_config_hash=str(config["network_config_hash"]),
            require_network_config_quorum=True,
            expected_config_signer_registry_hash=str(registry["registry_hash"]),
        )
    finally:
        server.shutdown()
        server.server_close()

    assert report["ok"] is True
    remote = report["remote_network"]
    assert remote["network_config_quorum_required"] is True
    assert remote["network_config_quorum_admission"]["accepted_weight"] == 2
    assert remote["network_config_quorum_admission"]["registry_hash"] == registry["registry_hash"]


def test_doctor_rejects_required_unsigned_public_network_config_quorum(tmp_path: Path) -> None:
    bundle_root = tmp_path / "bundle"
    _bundle(bundle_root)
    server, mirror_url = _start_static_server(bundle_root)
    try:
        config = build_public_network_config_v0(
            bundle_root=bundle_root,
            mirror_base_url=mirror_url,
            writer_urls=["http://127.0.0.1:8799"],
            peer_urls=[],
            poll_seconds=5,
            node_port=8788,
        )
        (bundle_root / "public_network_config.json").write_text(
            json.dumps(config, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        report = doctor_public_node_v0(
            config_url=f"{mirror_url}/public_network_config.json",
            expected_network_config_hash=str(config["network_config_hash"]),
            require_network_config_quorum=True,
        )
    finally:
        server.shutdown()
        server.server_close()

    assert report["ok"] is False
    public_config_check = [check for check in report["checks"] if check["name"] == "public_network_config"][0]
    assert "quorum is required" in public_config_check["error"]


def test_doctor_rejects_insufficient_public_network_config_quorum(tmp_path: Path) -> None:
    bundle_root = tmp_path / "bundle"
    _bundle(bundle_root)
    server, mirror_url = _start_static_server(bundle_root)
    try:
        config = build_public_network_config_v0(
            bundle_root=bundle_root,
            mirror_base_url=mirror_url,
            writer_urls=["http://127.0.0.1:8799"],
            peer_urls=[],
            poll_seconds=5,
            node_port=8788,
        )
        registry = _registry()
        signed_config = attach_public_network_config_quorum_v0(
            network_config=config,
            registry=registry,
            envelopes=_envelopes(str(config["network_config_hash"])),
        )
        signed_config["config_signature_envelopes"] = signed_config["config_signature_envelopes"][:1]
        (bundle_root / "public_network_config.json").write_text(
            json.dumps(signed_config, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        report = doctor_public_node_v0(
            config_url=f"{mirror_url}/public_network_config.json",
            expected_network_config_hash=str(config["network_config_hash"]),
            require_network_config_quorum=True,
            expected_config_signer_registry_hash=str(registry["registry_hash"]),
        )
    finally:
        server.shutdown()
        server.server_close()

    assert report["ok"] is False
    public_config_check = [check for check in report["checks"] if check["name"] == "public_network_config"][0]
    assert "threshold not met" in public_config_check["error"]


def test_join_config_conversion_requires_signed_public_network_config_quorum(tmp_path: Path) -> None:
    bundle_root = tmp_path / "bundle"
    _bundle(bundle_root)
    config = build_public_network_config_v0(
        bundle_root=bundle_root,
        mirror_base_url="http://127.0.0.1:8000",
        writer_urls=["http://127.0.0.1:8799"],
        peer_urls=[],
        poll_seconds=5,
        node_port=8788,
    )

    with pytest.raises(ValueError, match="quorum is required"):
        _public_network_config_to_join_config_v0(
            network_config=config,
            node_id="node-b",
            bundle_root=tmp_path / "synced",
            data_dir=tmp_path / "node-b",
            host="127.0.0.1",
            port=None,
            poll_seconds=None,
            serve=False,
            require_network_config_quorum=True,
        )

    registry = _registry()
    signed_config = attach_public_network_config_quorum_v0(
        network_config=config,
        registry=registry,
        envelopes=_envelopes(str(config["network_config_hash"])),
    )
    join_config = _public_network_config_to_join_config_v0(
        network_config=signed_config,
        node_id="node-b",
        bundle_root=tmp_path / "synced",
        data_dir=tmp_path / "node-b",
        host="127.0.0.1",
        port=None,
        poll_seconds=None,
        serve=False,
        require_network_config_quorum=True,
        expected_config_signer_registry_hash=str(registry["registry_hash"]),
    )

    assert join_config["network_config_quorum_required"] is True
    assert join_config["network_config_quorum_admission"]["accepted_weight"] == 2
    assert join_config["peer_registry_admission"]["writer_count"] == 1
    assert join_config["peer_registry_admission"]["peer_count"] == 1
