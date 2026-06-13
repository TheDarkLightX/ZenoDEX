from __future__ import annotations

import hashlib
import json
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

from src.integration.zeno_ledger_live_quorum_v0 import build_live_checkpoint_quorum_admission_v0
from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_ledger_v0 import (
    build_checkpoint_v0,
    build_header_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    hash_v0,
)
from src.state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes
from tools.zeno_ledger_node import NODE_STATUS_SCHEMA, check_peer_status_v0, pull_live_from_peer_v0

ZERO_ROOT = "0x" + "00" * 32
TEST_BLS_PRIVATE_KEY_A = "0x" + "01" * 32
TEST_BLS_PRIVATE_KEY_B = "0x" + "02" * 32


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _node_status_hash(status: dict[str, object]) -> str:
    body = {key: value for key, value in status.items() if key != "node_status_hash"}
    return hash_v0("node_status_v0", body)


def _status(
    *,
    node_id: str,
    data_dir: Path,
    bundle_root: Path,
    latest_height: int,
    last_header_hash: str,
    sequencer_set_hash: str,
) -> dict[str, object]:
    body: dict[str, object] = {
        "schema": NODE_STATUS_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": node_id,
        "node_role": "follower_watcher",
        "network_id": "zeno-ledger-peer-check-testnet-0",
        "chain_id": "zeno-ledger-peer-check-testnet-0",
        "bundle_root": str(bundle_root),
        "data_dir": str(data_dir),
        "latest_height": latest_height,
        "last_header_hash": last_header_hash,
        "last_app_hash": _root(f"{node_id}-app"),
        "operator_attestation_path": "",
        "operator_attestation_hash": _root(f"{node_id}-attestation"),
        "combined_testnet_status_path": "",
        "combined_testnet_status_hash": _root(f"{node_id}-testnet-status"),
        "combined_watcher_count": 1,
        "sequencer_set_hash": sequencer_set_hash,
        "mirror_index_hash": _root("mirror"),
        "feature_suite_hash": _root("features"),
        "covered_feature_count": 0,
        "covered_features": [],
        "required_features": [],
        "token_symbol": "tZENO",
        "token_posture": {},
        "test_token_catalog": [],
        "testnet_faucet_posture": {},
        "testnet_token_support": {},
    }
    return {**body, "node_status_hash": _node_status_hash(body)}


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _header(*, height: int, label: str, sequencer_set_hash: str) -> dict[str, object]:
    return build_header_v0(
        chain_id="zeno-ledger-peer-check-testnet-0",
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=sequencer_set_hash,
        ingress_root=_root(f"ingress-{label}"),
        tx_root=_root(f"tx-{label}"),
        pre_state_root=_root(f"pre-{label}"),
        post_state_root=_root(f"post-{label}"),
        app_hash=_root(f"app-{label}"),
        evidence_root=_root(f"evidence-{label}"),
        body_root=_root(f"body-{label}"),
        data_availability_root=_root(f"da-{label}"),
        proof_journal_hash=_root(f"proof-{label}"),
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _write_local_node(
    *,
    data_dir: Path,
    latest_height: int,
    latest_header_hash: str,
    sequencer_set_hash: str,
    live: bool,
) -> dict[str, object]:
    status = _status(
        node_id="local-node",
        data_dir=data_dir,
        bundle_root=data_dir / "bundle",
        latest_height=5 if live else latest_height,
        last_header_hash=_root("bootstrap-5") if live else latest_header_hash,
        sequencer_set_hash=sequencer_set_hash,
    )
    _write_json(data_dir / "node_status.json", status)
    if live:
        snapshot_path = data_dir / "live_ledger" / "snapshots" / f"{latest_height}.json"
        header_path = data_dir / "live_ledger" / "headers" / f"{latest_height}.json"
        snapshot = {
            "schema": "zenodex/tau_app_state/v1",
            "dex_state": {},
            "test_label": f"local-live-{latest_height}",
        }
        post_state_root = canonical_hex_fixed_allow_0x(
            hashlib.sha256(canonical_json_bytes(snapshot)).hexdigest(),
            nbytes=32,
            name="post_state_root",
        )
        header_fields = {
            "chain_id": "zeno-ledger-peer-check-testnet-0",
            "height": latest_height,
            "post_state_root": post_state_root,
            "evidence_root": _root(f"local-evidence-{latest_height}"),
            "config_digest": _root("config"),
            "module_versions_digest": _root("modules"),
        }
        app_hash = compute_app_hash_v0(header_fields)
        header = build_header_v0(
            chain_id="zeno-ledger-peer-check-testnet-0",
            height=latest_height,
            time_ms=1_778_730_000_000 + latest_height,
            prev_header_hash=ZERO_ROOT,
            sequencer_set_hash=sequencer_set_hash,
            ingress_root=_root(f"local-ingress-{latest_height}"),
            tx_root=_root(f"local-tx-{latest_height}"),
            pre_state_root=_root(f"local-pre-{latest_height}"),
            post_state_root=post_state_root,
            app_hash=app_hash,
            evidence_root=str(header_fields["evidence_root"]),
            body_root=_root(f"local-body-{latest_height}"),
            data_availability_root=_root(f"local-da-{latest_height}"),
            proof_journal_hash=ZERO_ROOT,
            config_digest=str(header_fields["config_digest"]),
            module_versions_digest=str(header_fields["module_versions_digest"]),
            signature_set_root=ZERO_ROOT,
        )
        _write_json(snapshot_path, snapshot)
        _write_json(header_path, header)
        _write_json(
            data_dir / "live_state.json",
            {
                "schema": "zenodex.zeno_ledger.node_live_state.v0",
                "latest_height": latest_height,
                "latest_header_path": str(header_path),
                "latest_snapshot_path": str(snapshot_path),
                "latest_header_hash": canonical_header_hash_v0(header),
                "latest_app_hash": app_hash,
            },
        )
    return status


class _PeerHandler(BaseHTTPRequestHandler):
    peer_status: dict[str, object]
    live_state: dict[str, object]
    live_headers: dict[int, dict[str, object]]
    live_checkpoints: dict[int, dict[str, object]]

    def log_message(self, format: str, *args: object) -> None:
        return

    def _send_json(self, value: object) -> None:
        payload = json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def do_GET(self) -> None:  # noqa: N802
        if self.path == "/status":
            self._send_json(self.peer_status)
            return
        if self.path == "/live":
            self._send_json({"ok": True, "live": True, "state": self.live_state})
            return
        parts = [part for part in self.path.split("/") if part]
        if len(parts) == 3 and parts[:2] == ["live", "header"]:
            self._send_json(self.live_headers[int(parts[2])])
            return
        if len(parts) == 3 and parts[:2] == ["live", "checkpoint"]:
            self._send_json(self.live_checkpoints[int(parts[2])])
            return
        self.send_response(404)
        self.end_headers()


def _serve_peer(
    *,
    peer_status: dict[str, object],
    live_state: dict[str, object],
    live_headers: dict[int, dict[str, object]],
    live_checkpoints: dict[int, dict[str, object]] | None = None,
) -> ThreadingHTTPServer:
    handler = type(
        "PeerHandler",
        (_PeerHandler,),
        {
            "peer_status": peer_status,
            "live_state": live_state,
            "live_headers": live_headers,
            "live_checkpoints": dict(live_checkpoints or {}),
        },
    )
    server = ThreadingHTTPServer(("127.0.0.1", 0), handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    return server


def test_peer_check_includes_follow_candidate_fork_choice(tmp_path: Path) -> None:
    sequencer_set_hash = _root("validator-set")
    common_header_hash = _root("bootstrap-5")
    peer_header = _header(height=6, label="peer-extends", sequencer_set_hash=sequencer_set_hash)
    peer_header_hash = canonical_header_hash_v0(peer_header)
    data_dir = tmp_path / "local"
    _write_local_node(
        data_dir=data_dir,
        latest_height=5,
        latest_header_hash=common_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        live=False,
    )
    peer_status = _status(
        node_id="peer-node",
        data_dir=tmp_path / "peer",
        bundle_root=tmp_path / "peer-bundle",
        latest_height=5,
        last_header_hash=common_header_hash,
        sequencer_set_hash=sequencer_set_hash,
    )
    server = _serve_peer(
        peer_status=peer_status,
        live_state={
            "schema": "zenodex.zeno_ledger.node_live_state.v0",
            "latest_height": 6,
            "latest_header_hash": peer_header_hash,
            "latest_app_hash": _root("peer-app-6"),
        },
        live_headers={6: peer_header},
    )
    try:
        host, port = server.server_address
        peer_check = check_peer_status_v0(data_dir=data_dir, peer_urls=[f"http://{host}:{port}"])
    finally:
        server.shutdown()
        server.server_close()

    assert peer_check["ok"] is True
    peer = peer_check["peers"][0]
    assert peer["height_relation"] == "peer_ahead"
    assert peer["fork_choice_compatible"] is True
    assert peer["fork_choice"]["decision"] == "follow_candidate"
    assert peer["fork_choice"]["reason"] == "candidate_extends_local_tip"


def test_peer_check_rejects_same_height_conflicting_live_tip(tmp_path: Path) -> None:
    sequencer_set_hash = _root("validator-set")
    local_header_hash = _root("local-live-6")
    peer_header = _header(height=6, label="peer-conflict", sequencer_set_hash=sequencer_set_hash)
    peer_header_hash = canonical_header_hash_v0(peer_header)
    data_dir = tmp_path / "local"
    _write_local_node(
        data_dir=data_dir,
        latest_height=6,
        latest_header_hash=local_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        live=True,
    )
    peer_status = _status(
        node_id="peer-node",
        data_dir=tmp_path / "peer",
        bundle_root=tmp_path / "peer-bundle",
        latest_height=5,
        last_header_hash=_root("bootstrap-5"),
        sequencer_set_hash=sequencer_set_hash,
    )
    server = _serve_peer(
        peer_status=peer_status,
        live_state={
            "schema": "zenodex.zeno_ledger.node_live_state.v0",
            "latest_height": 6,
            "latest_header_hash": peer_header_hash,
            "latest_app_hash": _root("peer-app-6"),
        },
        live_headers={6: peer_header},
    )
    try:
        host, port = server.server_address
        peer_check = check_peer_status_v0(data_dir=data_dir, peer_urls=[f"http://{host}:{port}"])
    finally:
        server.shutdown()
        server.server_close()

    assert peer_check["ok"] is False
    peer = peer_check["peers"][0]
    assert peer["status"] == "rejected"
    assert peer["height_relation"] == "same_height"
    assert peer["common_header_match"] is False
    assert peer["fork_choice_compatible"] is False
    assert peer["fork_choice"]["decision"] == "reject_candidate"
    assert peer["fork_choice"]["reason"] == "common_prefix_mismatch"


def test_pull_live_from_peer_rejects_incompatible_same_height_tip(tmp_path: Path) -> None:
    sequencer_set_hash = _root("validator-set")
    local_header_hash = _root("local-live-6")
    peer_header = _header(height=6, label="peer-conflict", sequencer_set_hash=sequencer_set_hash)
    peer_header_hash = canonical_header_hash_v0(peer_header)
    data_dir = tmp_path / "local"
    _write_local_node(
        data_dir=data_dir,
        latest_height=6,
        latest_header_hash=local_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        live=True,
    )
    peer_status = _status(
        node_id="peer-node",
        data_dir=tmp_path / "peer",
        bundle_root=tmp_path / "peer-bundle",
        latest_height=5,
        last_header_hash=_root("bootstrap-5"),
        sequencer_set_hash=sequencer_set_hash,
    )
    server = _serve_peer(
        peer_status=peer_status,
        live_state={
            "schema": "zenodex.zeno_ledger.node_live_state.v0",
            "latest_height": 6,
            "latest_header_hash": peer_header_hash,
            "latest_app_hash": _root("peer-app-6"),
        },
        live_headers={6: peer_header},
    )
    try:
        host, port = server.server_address
        pull_report = pull_live_from_peer_v0(data_dir=data_dir, peer_url=f"http://{host}:{port}")
    finally:
        server.shutdown()
        server.server_close()

    assert pull_report["ok"] is False
    assert pull_report["status"] == "rejected"
    assert pull_report["pulled_count"] == 0
    assert pull_report["reject_reason"] == "peer_check_rejected"
    assert pull_report["peer_check"]["peers"][0]["fork_choice"]["decision"] == "reject_candidate"


def _registry() -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="live-checkpoint-quorum-testnet-v0",
        payload_kind="checkpoint",
        threshold=2,
        signers=[
            {
                "signer_id": "validator-a",
                "key_id": "bls-a",
                "public_key": bls_public_key_hex_from_private_key_v0(TEST_BLS_PRIVATE_KEY_A),
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "validator-b",
                "key_id": "bls-b",
                "public_key": bls_public_key_hex_from_private_key_v0(TEST_BLS_PRIVATE_KEY_B),
                "weight": 1,
                "status": "active",
            },
        ],
    )


def _envelopes(header_hash: str) -> list[dict[str, object]]:
    return [
        build_bls_signed_artifact_envelope_v0(
            payload_kind="checkpoint",
            payload_hash=header_hash,
            signer_id="validator-a",
            key_id="bls-a",
            private_key_hex=TEST_BLS_PRIVATE_KEY_A,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind="checkpoint",
            payload_hash=header_hash,
            signer_id="validator-b",
            key_id="bls-b",
            private_key_hex=TEST_BLS_PRIVATE_KEY_B,
        ),
    ]


def test_pull_live_from_peer_rejects_missing_required_live_quorum(tmp_path: Path) -> None:
    sequencer_set_hash = _root("validator-set")
    common_header_hash = _root("bootstrap-5")
    peer_header = _header(height=6, label="peer-extends", sequencer_set_hash=sequencer_set_hash)
    peer_header_hash = canonical_header_hash_v0(peer_header)
    data_dir = tmp_path / "local"
    _write_local_node(
        data_dir=data_dir,
        latest_height=5,
        latest_header_hash=common_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        live=False,
    )
    peer_status = _status(
        node_id="peer-node",
        data_dir=tmp_path / "peer",
        bundle_root=tmp_path / "peer-bundle",
        latest_height=5,
        last_header_hash=common_header_hash,
        sequencer_set_hash=sequencer_set_hash,
    )
    server = _serve_peer(
        peer_status=peer_status,
        live_state={
            "schema": "zenodex.zeno_ledger.node_live_state.v0",
            "latest_height": 6,
            "latest_header_hash": peer_header_hash,
            "latest_app_hash": _root("peer-app-6"),
        },
        live_headers={6: peer_header},
    )
    try:
        host, port = server.server_address
        pull_report = pull_live_from_peer_v0(
            data_dir=data_dir,
            peer_url=f"http://{host}:{port}",
            live_quorum_registry=_registry(),
            live_quorum_envelopes_by_height={},
        )
    finally:
        server.shutdown()
        server.server_close()

    assert pull_report["ok"] is False
    assert pull_report["status"] == "rejected"
    assert pull_report["pulled_count"] == 0
    assert pull_report["reject_reason"] == "live_quorum_missing_envelopes"


def test_pull_live_from_peer_rejects_insufficient_live_quorum(tmp_path: Path) -> None:
    sequencer_set_hash = _root("validator-set")
    common_header_hash = _root("bootstrap-5")
    peer_header = _header(height=6, label="peer-extends", sequencer_set_hash=sequencer_set_hash)
    peer_header_hash = canonical_header_hash_v0(peer_header)
    data_dir = tmp_path / "local"
    _write_local_node(
        data_dir=data_dir,
        latest_height=5,
        latest_header_hash=common_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        live=False,
    )
    peer_status = _status(
        node_id="peer-node",
        data_dir=tmp_path / "peer",
        bundle_root=tmp_path / "peer-bundle",
        latest_height=5,
        last_header_hash=common_header_hash,
        sequencer_set_hash=sequencer_set_hash,
    )
    server = _serve_peer(
        peer_status=peer_status,
        live_state={
            "schema": "zenodex.zeno_ledger.node_live_state.v0",
            "latest_height": 6,
            "latest_header_hash": peer_header_hash,
            "latest_app_hash": _root("peer-app-6"),
        },
        live_headers={6: peer_header},
        live_checkpoints={6: build_checkpoint_v0(peer_header)},
    )
    try:
        host, port = server.server_address
        pull_report = pull_live_from_peer_v0(
            data_dir=data_dir,
            peer_url=f"http://{host}:{port}",
            live_quorum_registry=_registry(),
            live_quorum_envelopes_by_height={6: _envelopes(peer_header_hash)[:1]},
        )
    finally:
        server.shutdown()
        server.server_close()

    assert pull_report["ok"] is False
    assert pull_report["status"] == "rejected"
    assert pull_report["pulled_count"] == 0
    assert pull_report["reject_reason"] == "live_quorum_rejected"
    assert "threshold not met" in pull_report["errors"][0]


def test_live_quorum_admission_helper_matches_peer_header_checkpoint() -> None:
    registry = _registry()
    peer_header = _header(height=6, label="peer-extends", sequencer_set_hash=_root("validator-set"))
    checkpoint = {
        "schema": "zenodex/zeno_ledger/checkpoint/v0",
        "chain_id": peer_header["chain_id"],
        "height": peer_header["height"],
        "header_hash": canonical_header_hash_v0(peer_header),
        "app_hash": peer_header["app_hash"],
        "post_state_root": peer_header["post_state_root"],
        "ingress_root": peer_header["ingress_root"],
        "evidence_root": peer_header["evidence_root"],
        "body_root": peer_header["body_root"],
        "config_digest": peer_header["config_digest"],
        "proof_journal_hash": peer_header["proof_journal_hash"],
        "sequencer_set_hash": peer_header["sequencer_set_hash"],
        "signature_set_root": peer_header["signature_set_root"],
        "signature_set": [],
    }
    envelopes = _envelopes(str(checkpoint["header_hash"]))

    admission = build_live_checkpoint_quorum_admission_v0(
        header=peer_header,
        checkpoint=checkpoint,
        registry=registry,
        envelopes=envelopes,
    )

    assert admission["ok"] is True
    assert admission["accepted_weight"] == 2
