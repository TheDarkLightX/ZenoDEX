from __future__ import annotations

import json
import shutil
import threading
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import pytest

from src.integration.zeno_ledger_block_gossip_v0 import (
    build_block_gossip_envelope_v0,
    validate_block_gossip_envelope_v0,
)
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_ASSET0, DEFAULT_BOOTSTRAP_SENDER
from tools.zeno_ledger_node import (
    accept_block_gossip_envelope_v0,
    append_testnet_faucet_v0,
    load_node_status_v0,
    make_node_http_server_v0,
    run_node_once_v0,
)


def _load(path: Path) -> dict[str, object]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(obj, dict)
    return obj


def _post_json(url: str, value: dict[str, object]) -> dict[str, object]:
    request = Request(
        url,
        data=json.dumps(value, sort_keys=True).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urlopen(request, timeout=5) as response:  # noqa: S310 - local test server
            payload = response.read().decode("utf-8")
    except HTTPError as exc:
        payload = exc.read().decode("utf-8")
    obj = json.loads(payload)
    assert isinstance(obj, dict)
    return obj


@pytest.fixture(scope="module")
def bundle_root(tmp_path_factory: pytest.TempPathFactory) -> Path:
    root = tmp_path_factory.mktemp("block_gossip_bundle") / "bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=root,
        network_id="zeno-ledger-block-gossip-testnet-0",
        chain_id="zeno-ledger-block-gossip-testnet-0",
        sequencer_id="sequencer-block-gossip-testnet-0",
        time_ms=1_778_730_123_000,
        token_symbol="tZENO",
    )
    assert build_report["ok"] is True
    return root


@pytest.fixture(scope="module")
def baseline_nodes(tmp_path_factory: pytest.TempPathFactory, bundle_root: Path) -> tuple[Path, Path, Path]:
    root = tmp_path_factory.mktemp("block_gossip_nodes")
    source = root / "node-a-base"
    target = root / "node-b-base"
    assert run_node_once_v0(bundle_root=bundle_root, node_id="node-a", data_dir=source)["ok"] is True
    assert run_node_once_v0(bundle_root=bundle_root, node_id="node-b", data_dir=target)["ok"] is True
    return bundle_root, source, target


def _node_pair(tmp_path: Path, baseline_nodes: tuple[Path, Path, Path]) -> tuple[Path, Path, Path]:
    bundle_root, source_base, target_base = baseline_nodes
    source = tmp_path / "node-a"
    target = tmp_path / "node-b"
    shutil.copytree(source_base, source)
    shutil.copytree(target_base, target)
    return bundle_root, source, target


def _faucet_gossip_envelope(source: Path) -> dict[str, object]:
    append_report = append_testnet_faucet_v0(
        data_dir=source,
        to_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset=DEFAULT_ASSET0,
        amount=1_000,
        time_ms=1_778_730_223_000,
        tx_id="gossip-faucet-v0",
    )
    height = int(append_report["height"])
    envelope = build_block_gossip_envelope_v0(
        header=_load(source / "live_ledger" / "headers" / f"{height}.json"),
        body=_load(source / "live_ledger" / "bodies" / f"{height}.json"),
        checkpoint=_load(source / "live_ledger" / "checkpoints" / f"{height}.json"),
        source_node_id="node-a",
        source_peer_url="http://127.0.0.1:8800",
    )
    validate_block_gossip_envelope_v0(envelope)
    return envelope


def test_block_gossip_accepts_next_height_after_local_replay(
    tmp_path: Path,
    baseline_nodes: tuple[Path, Path, Path],
) -> None:
    _, source, target = _node_pair(tmp_path, baseline_nodes)
    envelope = _faucet_gossip_envelope(source)

    report = accept_block_gossip_envelope_v0(data_dir=target, envelope=envelope)

    assert report["ok"] is True
    assert report["status"] == "accepted"
    assert report["height"] == envelope["height"]
    assert report["header_hash"] == envelope["header_hash"]
    status = load_node_status_v0(target)
    live_state = _load(target / "live_state.json")
    assert live_state["latest_height"] == int(status["latest_height"]) + 1
    assert live_state["latest_header_hash"] == envelope["header_hash"]


def test_block_gossip_rejects_replayed_or_skipped_height(
    tmp_path: Path,
    baseline_nodes: tuple[Path, Path, Path],
) -> None:
    _, source, target = _node_pair(tmp_path, baseline_nodes)
    envelope = _faucet_gossip_envelope(source)

    accept_block_gossip_envelope_v0(data_dir=target, envelope=envelope)

    try:
        accept_block_gossip_envelope_v0(data_dir=target, envelope=envelope)
    except ValueError as exc:
        assert "duplicate gossip envelope" in str(exc)
    else:  # pragma: no cover - defensive assertion
        raise AssertionError("replayed gossip block was accepted")


def test_block_gossip_rejects_body_transaction_flood(
    tmp_path: Path,
    baseline_nodes: tuple[Path, Path, Path],
) -> None:
    _, source, target = _node_pair(tmp_path, baseline_nodes)
    envelope = _faucet_gossip_envelope(source)

    try:
        accept_block_gossip_envelope_v0(data_dir=target, envelope=envelope, max_body_transactions=0)
    except ValueError as exc:
        assert "transaction count exceeds maximum" in str(exc)
    else:  # pragma: no cover - defensive assertion
        raise AssertionError("oversized gossip block was accepted")


def test_block_gossip_http_route_is_opt_in(
    tmp_path: Path,
    baseline_nodes: tuple[Path, Path, Path],
) -> None:
    _, source, target = _node_pair(tmp_path, baseline_nodes)
    envelope = _faucet_gossip_envelope(source)

    disabled = make_node_http_server_v0(data_dir=target, host="127.0.0.1", port=0)
    disabled_thread = threading.Thread(target=disabled.serve_forever, daemon=True)
    disabled_thread.start()
    try:
        host, port = disabled.server_address
        rejected = _post_json(f"http://{host}:{port}/gossip/block", {"envelope": envelope})
    finally:
        disabled.shutdown()
        disabled.server_close()
    assert rejected["error"] == "block_gossip_disabled"

    enabled_target = tmp_path / "node-c"
    shutil.copytree(target, enabled_target)
    enabled = make_node_http_server_v0(
        data_dir=enabled_target,
        host="127.0.0.1",
        port=0,
        enable_block_gossip=True,
    )
    enabled_thread = threading.Thread(target=enabled.serve_forever, daemon=True)
    enabled_thread.start()
    try:
        host, port = enabled.server_address
        accepted = _post_json(f"http://{host}:{port}/gossip/block", {"envelope": envelope})
    finally:
        enabled.shutdown()
        enabled.server_close()
    assert accepted["ok"] is True
    assert accepted["header_hash"] == envelope["header_hash"]
